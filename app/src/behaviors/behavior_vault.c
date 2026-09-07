/*
 * Copyright (c) 2026 Evgenii Shchemelev
 * SPDX-License-Identifier: MIT
 *
 * Passphrase-gated password vault behavior.
 *
 * Press &vault <index>, then type your master passphrase (any characters, any
 * length) and press Enter. Keystrokes are captured from the keycode stream (and
 * suppressed, so they never reach the host); on Enter the passphrase is stretched
 * with PBKDF2-HMAC-SHA256 into a key, the selected secret is decrypted, and it is
 * "typed" over HID. Wrong passphrase -> nothing. Backspace edits, Escape cancels.
 *
 * Session unlock: the first correct passphrase runs the (deliberately slow)
 * PBKDF2 once, caches the derived key in RAM, and unlocks. Later &vault presses
 * decrypt instantly from the cached key. Re-locks only on power loss / reset.
 *
 * The KDF runs on a dedicated low-priority work queue so its multi-second stretch
 * does not stall BLE/HID.
 *
 * Security: salt, verifier and ciphertext all ship in the firmware, so strength
 * rests on passphrase entropy against an offline PBKDF2 attack from a dump. While
 * unlocked the passphrase is effectively off: a grabbed powered dongle types all.
 */

#define DT_DRV_COMPAT zmk_behavior_vault

#include <zephyr/device.h>
#include <zephyr/kernel.h>
#include <drivers/behavior.h>
#include <zephyr/logging/log.h>
#include <string.h>

#include <zmk/behavior.h>
#include <zmk/event_manager.h>
#include <zmk/events/keycode_state_changed.h>
#include <zmk/keys.h>
#include <dt-bindings/zmk/hid_usage_pages.h>
#include <dt-bindings/zmk/modifiers.h>

#include <tinycrypt/sha256.h>
#include <tinycrypt/hmac.h>
#include <tinycrypt/constants.h>

LOG_MODULE_DECLARE(zmk, CONFIG_ZMK_LOG_LEVEL);

#if DT_HAS_COMPAT_STATUS_OKAY(DT_DRV_COMPAT)

#define VAULT_MAX_CT 256
#define VAULT_MAX_CODES (VAULT_MAX_CT / 4)
#define VAULT_MAX_PIN 64
#define VAULT_CAPTURE_TIMEOUT_MS 30000
#define VAULT_TYPE_STEP_MS 12
#define VAULT_WQ_STACK 3072

/* HID usage ids (keyboard page) */
#define HID_ENTER 0x28
#define HID_ESC 0x29
#define HID_BSPC 0x2A
#define HID_KP_ENTER 0x58
#define HID_LSHIFT 0xE1
#define HID_RSHIFT 0xE5

/* Per-secret record: shared KDF salt + verifier live in the header globals. */
struct vault_secret {
    uint8_t nonce[16];
    uint16_t ct_len;
    uint8_t ct[VAULT_MAX_CT];
};

/* Generated at build time by syspass_gen.py: defines VAULT_SECRET_COUNT,
 * VAULT_KDF_ITERS, vault_salt[16], vault_verifier[4], vault_secrets[]. */
#include <vault_secrets.h>

static struct {
    bool active;
    bool done;
    bool shift_l;
    bool shift_r;
    uint8_t secret;
    uint8_t len;
    uint8_t buf[VAULT_MAX_PIN];
} cap;

/* Session state: survives until power loss / reset. Caches the derived key so
 * the slow KDF runs only once per unlock. */
static struct {
    bool unlocked;
    uint8_t key[16];
} session;

static struct {
    uint32_t codes[VAULT_MAX_CODES];
    uint16_t count;
    uint16_t idx;
    bool pressing;
} typ;

static bool pending_session;
static uint8_t pending_secret;

static struct k_work_delayable finish_work;
static struct k_work_delayable timeout_work;
static struct k_work_delayable type_work;

/* Dedicated queue for the KDF-heavy finish handler. */
K_THREAD_STACK_DEFINE(vault_wq_stack, VAULT_WQ_STACK);
static struct k_work_q vault_wq;

static void vault_reset_capture(void) {
    cap.active = false;
    cap.done = false;
    cap.shift_l = false;
    cap.shift_r = false;
    cap.len = 0;
    memset(cap.buf, 0, sizeof(cap.buf));
}

static int keycode_to_ascii(uint32_t id, bool shift) {
    if (id >= 0x04 && id <= 0x1D) {
        char base = (char)('a' + (id - 0x04));
        return shift ? (base - 'a' + 'A') : base;
    }
    if (id >= 0x1E && id <= 0x26) {
        static const char sh[] = "!@#$%^&*(";
        return shift ? sh[id - 0x1E] : (char)('1' + (id - 0x1E));
    }
    if (id == 0x27) {
        return shift ? ')' : '0';
    }
    switch (id) {
    case 0x2C: return ' ';
    case 0x2D: return shift ? '_' : '-';
    case 0x2E: return shift ? '+' : '=';
    case 0x2F: return shift ? '{' : '[';
    case 0x30: return shift ? '}' : ']';
    case 0x31: return shift ? '|' : '\\';
    case 0x33: return shift ? ':' : ';';
    case 0x34: return shift ? '"' : '\'';
    case 0x35: return shift ? '~' : '`';
    case 0x36: return shift ? '<' : ',';
    case 0x37: return shift ? '>' : '.';
    case 0x38: return shift ? '?' : '/';
    default: return -1;
    }
}

static void vault_sha256(uint8_t out[TC_SHA256_DIGEST_SIZE], const uint8_t *a, size_t alen,
                         const uint8_t *b, size_t blen, const uint8_t *c, size_t clen) {
    struct tc_sha256_state_struct s;
    tc_sha256_init(&s);
    if (alen) {
        tc_sha256_update(&s, a, alen);
    }
    if (blen) {
        tc_sha256_update(&s, b, blen);
    }
    if (clen) {
        tc_sha256_update(&s, c, clen);
    }
    tc_sha256_final(out, &s);
}

/* PBKDF2-HMAC-SHA256, single output block (dklen 20 <= 32). */
static void vault_pbkdf2(const uint8_t *pass, uint16_t plen, uint32_t iters, uint8_t out[20]) {
    struct tc_hmac_state_struct h;
    uint8_t u[TC_SHA256_DIGEST_SIZE];
    uint8_t t[TC_SHA256_DIGEST_SIZE];
    uint8_t salt_block[16 + 4];

    memcpy(salt_block, vault_salt, 16);
    salt_block[16] = 0;
    salt_block[17] = 0;
    salt_block[18] = 0;
    salt_block[19] = 1; /* INT(1), big-endian */

    tc_hmac_set_key(&h, pass, plen);
    tc_hmac_init(&h);
    tc_hmac_update(&h, salt_block, sizeof(salt_block));
    tc_hmac_final(u, TC_SHA256_DIGEST_SIZE, &h);
    memcpy(t, u, TC_SHA256_DIGEST_SIZE);

    for (uint32_t i = 1; i < iters; i++) {
        tc_hmac_set_key(&h, pass, plen);
        tc_hmac_init(&h);
        tc_hmac_update(&h, u, TC_SHA256_DIGEST_SIZE);
        tc_hmac_final(u, TC_SHA256_DIGEST_SIZE, &h);
        for (int j = 0; j < TC_SHA256_DIGEST_SIZE; j++) {
            t[j] ^= u[j];
        }
    }

    memcpy(out, t, 20);
    memset(u, 0, sizeof(u));
    memset(t, 0, sizeof(t));
}

/* Stretch `pass` and check it against the stored verifier. On success copies the
 * 16-byte key into key_out. */
static bool derive_and_verify(const uint8_t *pass, uint16_t plen, uint8_t key_out[16]) {
    uint8_t dk[20];
    vault_pbkdf2(pass, plen, VAULT_KDF_ITERS, dk);
    bool ok = (memcmp(dk + 16, vault_verifier, 4) == 0);
    if (ok) {
        memcpy(key_out, dk, 16);
    }
    memset(dk, 0, sizeof(dk));
    return ok;
}

/* Decrypt `secret` with an already-derived key and queue it for typing. */
static void decrypt_and_type(uint8_t secret, const uint8_t key[16]) {
    if (secret >= VAULT_SECRET_COUNT || typ.count != 0) {
        return;
    }
    const struct vault_secret *sec = &vault_secrets[secret];

    uint8_t plain[VAULT_MAX_CT];
    uint16_t len = sec->ct_len;
    if (len > VAULT_MAX_CT) {
        len = VAULT_MAX_CT;
    }
    for (uint16_t off = 0; off < len; off += 32) {
        uint32_t blk = off / 32;
        uint8_t ctr[4] = {(uint8_t)(blk), (uint8_t)(blk >> 8), (uint8_t)(blk >> 16),
                          (uint8_t)(blk >> 24)};
        uint8_t ks[TC_SHA256_DIGEST_SIZE];
        vault_sha256(ks, key, 16, sec->nonce, 16, ctr, 4);
        uint16_t n = (uint16_t)((len - off < 32) ? (len - off) : 32);
        for (uint16_t j = 0; j < n; j++) {
            plain[off + j] = sec->ct[off + j] ^ ks[j];
        }
        memset(ks, 0, sizeof(ks));
    }

    uint16_t count = len / 4;
    if (count > VAULT_MAX_CODES) {
        count = VAULT_MAX_CODES;
    }
    for (uint16_t i = 0; i < count; i++) {
        typ.codes[i] = (uint32_t)plain[i * 4] | ((uint32_t)plain[i * 4 + 1] << 8) |
                       ((uint32_t)plain[i * 4 + 2] << 16) | ((uint32_t)plain[i * 4 + 3] << 24);
    }
    typ.count = count;
    typ.idx = 0;
    typ.pressing = true;

    memset(plain, 0, sizeof(plain));

    if (count > 0) {
        k_work_schedule(&type_work, K_MSEC(VAULT_TYPE_STEP_MS));
    }
}

static void vault_finish_fn(struct k_work *w) {
    if (pending_session) {
        pending_session = false;
        decrypt_and_type(pending_secret, session.key);
        return;
    }

    k_work_cancel_delayable(&timeout_work);
    cap.active = false;

    uint8_t key[16];
    if (derive_and_verify(cap.buf, cap.len, key)) {
        memcpy(session.key, key, 16);
        session.unlocked = true;
        decrypt_and_type(cap.secret, session.key);
    } else {
        LOG_WRN("vault: wrong passphrase");
    }
    memset(key, 0, sizeof(key));
    vault_reset_capture();
}

static void vault_type_fn(struct k_work *w) {
    if (typ.idx >= typ.count) {
        memset(typ.codes, 0, sizeof(typ.codes));
        typ.count = 0;
        return;
    }
    uint32_t code = typ.codes[typ.idx];
    if (typ.pressing) {
        raise_zmk_keycode_state_changed_from_encoded(code, true, k_uptime_get());
        typ.pressing = false;
    } else {
        raise_zmk_keycode_state_changed_from_encoded(code, false, k_uptime_get());
        typ.pressing = true;
        typ.idx++;
    }
    k_work_schedule(&type_work, K_MSEC(VAULT_TYPE_STEP_MS));
}

static void vault_timeout_fn(struct k_work *w) {
    if (cap.active) {
        LOG_WRN("vault: passphrase entry timed out");
    }
    vault_reset_capture();
}

static int vault_keycode_listener(const zmk_event_t *eh) {
    if (!cap.active || cap.done) {
        return ZMK_EV_EVENT_BUBBLE;
    }
    struct zmk_keycode_state_changed *ev = as_zmk_keycode_state_changed(eh);
    if (ev == NULL) {
        return ZMK_EV_EVENT_BUBBLE;
    }
    if (ev->usage_page != HID_USAGE_KEY) {
        return ZMK_EV_EVENT_HANDLED;
    }

    uint32_t id = ev->keycode;

    if (id == HID_LSHIFT) { cap.shift_l = ev->state; return ZMK_EV_EVENT_HANDLED; }
    if (id == HID_RSHIFT) { cap.shift_r = ev->state; return ZMK_EV_EVENT_HANDLED; }
    if (id >= 0xE0 && id <= 0xE7) { return ZMK_EV_EVENT_HANDLED; }

    if (!ev->state) {
        return ZMK_EV_EVENT_HANDLED;
    }

    if (id == HID_ENTER || id == HID_KP_ENTER) {
        cap.done = true;
        k_work_schedule_for_queue(&vault_wq, &finish_work, K_NO_WAIT);
        return ZMK_EV_EVENT_HANDLED;
    }
    if (id == HID_ESC) {
        k_work_cancel_delayable(&timeout_work);
        vault_reset_capture();
        return ZMK_EV_EVENT_HANDLED;
    }
    if (id == HID_BSPC) {
        if (cap.len > 0) {
            cap.len--;
        }
        return ZMK_EV_EVENT_HANDLED;
    }

    bool shift = cap.shift_l || cap.shift_r ||
                 ((ev->implicit_modifiers | ev->explicit_modifiers) & (MOD_LSFT | MOD_RSFT));
    int c = keycode_to_ascii(id, shift);
    if (c >= 0 && cap.len < VAULT_MAX_PIN) {
        cap.buf[cap.len++] = (uint8_t)c;
    }
    return ZMK_EV_EVENT_HANDLED;
}

ZMK_LISTENER(behavior_vault, vault_keycode_listener);
ZMK_SUBSCRIPTION(behavior_vault, zmk_keycode_state_changed);

static void vault_begin(uint8_t secret) {
    if (secret >= VAULT_SECRET_COUNT || typ.count != 0) {
        return;
    }
    if (session.unlocked) {
        pending_secret = secret;
        pending_session = true;
        k_work_schedule_for_queue(&vault_wq, &finish_work, K_NO_WAIT);
        return;
    }
    vault_reset_capture();
    cap.secret = secret;
    cap.active = true;
    k_work_reschedule(&timeout_work, K_MSEC(VAULT_CAPTURE_TIMEOUT_MS));
}

static int on_vault_pressed(struct zmk_behavior_binding *binding,
                            struct zmk_behavior_binding_event event) {
    vault_begin((uint8_t)binding->param1);
    return ZMK_BEHAVIOR_OPAQUE;
}

static int on_vault_released(struct zmk_behavior_binding *binding,
                             struct zmk_behavior_binding_event event) {
    return ZMK_BEHAVIOR_OPAQUE;
}

static const struct behavior_driver_api behavior_vault_driver_api = {
    .binding_pressed = on_vault_pressed,
    .binding_released = on_vault_released,
#if IS_ENABLED(CONFIG_ZMK_BEHAVIOR_METADATA)
    .get_parameter_metadata = zmk_behavior_get_empty_param_metadata,
#endif
};

static int behavior_vault_init(const struct device *dev) {
    static bool initialized;
    if (!initialized) {
        k_work_init_delayable(&finish_work, vault_finish_fn);
        k_work_init_delayable(&timeout_work, vault_timeout_fn);
        k_work_init_delayable(&type_work, vault_type_fn);
        k_work_queue_init(&vault_wq);
        k_work_queue_start(&vault_wq, vault_wq_stack, K_THREAD_STACK_SIZEOF(vault_wq_stack),
                           K_LOWEST_APPLICATION_THREAD_PRIO, NULL);
        initialized = true;
    }
    return 0;
}

#define VAULT_INST(n)                                                                              \
    BEHAVIOR_DT_INST_DEFINE(n, behavior_vault_init, NULL, NULL, NULL, POST_KERNEL,                 \
                            CONFIG_KERNEL_INIT_PRIORITY_DEFAULT, &behavior_vault_driver_api);

DT_INST_FOREACH_STATUS_OKAY(VAULT_INST)

#endif /* DT_HAS_COMPAT_STATUS_OKAY(DT_DRV_COMPAT) */
