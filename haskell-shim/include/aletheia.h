// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * Aletheia C API
 *
 * Formally verified CAN frame analysis via Linear Temporal Logic.
 * This header defines the C ABI exported by libaletheia-ffi.so. A C caller
 * compiles it as C23; a C++ caller as C++23.
 */

#ifndef ALETHEIA_H
#define ALETHEIA_H

#if !defined(__cplusplus) && (!defined(__STDC_VERSION__) || __STDC_VERSION__ < 202311L)
#error "aletheia.h requires C23"
#endif

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Structures
 *
 * Every argument and result but a session handle, a returned string and a
 * count crosses the ABI as one of these structures, passed by pointer; a
 * 128-bit number is two 64-bit words inside one. The layout is fixed for LP64
 * targets (x86_64, ARM64); every binding mirrors it, and each mirror is pinned
 * against the sizes, alignments and offsets asserted below.
 *
 *   struct aletheia_text            size 16, align 8
 *     data         const char *      0
 *     size         size_t            8
 *
 *   struct aletheia_frame           size 32, align 8
 *     timestamp    uint64_t          0
 *     data         const uint8_t *   8
 *     can_id       uint32_t         16
 *     extended     uint8_t          20
 *     dlc          uint8_t          21
 *     data_len     uint8_t          22
 *     brs_present  uint8_t          23
 *     brs_value    uint8_t          24
 *     esi_present  uint8_t          25
 *     esi_value    uint8_t          26
 *
 *   struct aletheia_uint128         size 16, align 8
 *     lo           uint64_t          0
 *     hi           uint64_t          8
 *
 *   struct aletheia_rational        size 40, align 8
 *     numerator    struct aletheia_uint128   0
 *     denominator  struct aletheia_uint128  16
 *     negative     uint8_t                  32
 *
 *   struct aletheia_signal_values   size 24, align 8
 *     indices      const uint32_t *                   0
 *     values       const struct aletheia_rational *   8
 *     count        uint32_t                          16
 *
 *   struct aletheia_buffer          size 24, align 8
 *     data         uint8_t *         0
 *     err          char *            8
 *     size         uint32_t         16
 *
 *   struct aletheia_decimal         size 48, align 8
 *     value        struct aletheia_rational  0
 *     err          char *                   40
 *
 *   struct aletheia_time_bound      size 16, align 8
 *     microseconds uint64_t          0
 *     err          char *            8
 *
 *   struct aletheia_property_check  size 8, align 8
 *     err          char *            0
 */

/*
 * Text the caller passes: size bytes of UTF-8 from data, with no terminating
 * NUL. data may be NULL only when size is 0, the empty text. An entry taking
 * one refuses, in this order: a NULL text, a NULL data with a non-zero size
 * or a size past what the library can index, bytes that are not UTF-8, and a
 * NUL among the bytes. The locale of the calling process plays no part.
 */
struct aletheia_text {
    const char *data;
    size_t size;
};

/*
 * One CAN frame.
 *
 * The kernel decides every rule below and refuses a frame breaking one with
 * its typed code: an identifier out of range (parse_std_can_id_out_of_range,
 * parse_ext_can_id_out_of_range), a DLC above 15 (parse_dlc_code_out_of_range),
 * a data_len that is not the DLC's byte count (parse_payload_length_mismatch).
 *
 * timestamp    Microseconds. Read by the three trace-event entries,
 *              aletheia_send_frame, aletheia_send_remote and aletheia_send_error.
 * data         Payload in bus order (data[0] is the first byte on the bus,
 *              per ISO 11898 field order, not host endianness). May be NULL
 *              only when data_len is 0.
 * can_id       11-bit standard or 29-bit extended identifier. Read by every
 *              frame entry but aletheia_send_error.
 * extended     0 for a standard identifier, 1 for an extended one, read with
 *              can_id.
 * dlc          Data Length Code, 0 to 15. Codes 0 to 8 are byte counts; 9 to
 *              15 are the CAN-FD sizes 12, 16, 20, 24, 32, 48, 64.
 * data_len     Payload byte count. Must equal the DLC's byte count on every
 *              entry that reads a payload; aletheia_build_frame_bin reads
 *              neither data nor data_len.
 * brs_present  CAN-FD Bit Rate Switch (ISO 11898-1:2015 section 10.4.2):
 * brs_value    present 0 means absent (a CAN 2.0B frame); otherwise the bit
 *              is value != 0. Read by aletheia_send_frame only.
 * esi_present  CAN-FD Error State Indicator (section 10.4.3), encoded as BRS.
 * esi_value
 */
struct aletheia_frame {
    uint64_t timestamp;
    const uint8_t *data;
    uint32_t can_id;
    uint8_t extended;
    uint8_t dlc;
    uint8_t data_len;
    uint8_t brs_present;
    uint8_t brs_value;
    uint8_t esi_present;
    uint8_t esi_value;
};

/*
 * An unsigned 128-bit number, lo + hi * 2^64.
 */
struct aletheia_uint128 {
    uint64_t lo;
    uint64_t hi;
};

/*
 * An exact rational: numerator / denominator, negated when negative is not 0.
 * The library writes negative as 1 or 0, and 0 for a zero numerator; it reads
 * any byte but 0 as negative, so a negative zero is zero.
 */
struct aletheia_rational {
    struct aletheia_uint128 numerator;
    struct aletheia_uint128 denominator;
    uint8_t negative;
};

/*
 * Signal values to write into a frame: count entries, each a DBC signal index
 * indices[i] and the exact rational values[i], its denominator positive
 * (parse_non_positive_denominator otherwise). Each array may be NULL only when
 * count is 0.
 */
struct aletheia_signal_values {
    const uint32_t *indices;
    const struct aletheia_rational *values;
    uint32_t count;
};

/*
 * A binary result.
 *
 * aletheia_build_frame_bin and aletheia_update_frame_bin write into the
 * caller's memory: data points at a buffer of size bytes, which must hold the
 * DLC's byte count, and on success size is set to the count written.
 * aletheia_extract_signals_bin allocates: on success data points at size
 * bytes the caller frees with aletheia_free_buf.
 *
 * On failure every entry sets err to a JSON error envelope, as every other
 * entry answers ({"status": "error", "code": ..., "message": ...}), which the
 * caller frees with aletheia_free_str, and leaves data and size as they were.
 * The code is the kernel's typed refusal, or ffi_validation_error for a NULL
 * pointer the entry needs (the state, the frame, the signal values, or an
 * array or data with a non-zero count) or a buffer smaller than the frame the
 * kernel built.
 * A NULL buffer, which has no err to set, returns 1 with nothing written.
 */
struct aletheia_buffer {
    uint8_t *data;
    char *err;
    uint32_t size;
};

/*
 * A parsed decimal: on success value holds it in lowest terms with a positive
 * denominator, the numerator and the denominator each at most 2^128 - 1. On
 * failure err is the JSON error envelope every entry answers with, which the
 * caller frees with aletheia_free_str: its status, code and message, and the
 * code's own fields (text_parse_failure with line and column,
 * text_trailing_input with those and the unconsumed statement's,
 * input_bound_exceeded naming the field "decimal" with bound_kind, observed
 * and limit), or code ffi_validation_error for a text struct aletheia_text
 * refuses. Every call writes both fields: err NULL on success, and value
 * zero in every field on failure.
 */
struct aletheia_decimal {
    struct aletheia_rational value;
    char *err;
};

/*
 * A parsed time bound: on success microseconds holds the whole number of
 * microseconds the text denotes, at most 2^64 - 1. On failure err is the JSON
 * error envelope every entry answers with, which the caller frees with
 * aletheia_free_str: a text that is not a decimal refused as
 * aletheia_parse_decimal refuses it, a negative or fractional number with
 * code handler_property_refused and the reason a property's time bound is
 * refused with, a number past 2^64 - 1 with input_bound_exceeded naming
 * the field "time bound", or code ffi_validation_error for a text struct
 * aletheia_text refuses. Every call writes both fields: err NULL on success,
 * and microseconds 0 on failure.
 */
struct aletheia_time_bound {
    uint64_t microseconds;
    char *err;
};

/*
 * A property's check: on failure err is the JSON error envelope every entry
 * answers with, which the caller frees with aletheia_free_str: a text refused
 * as aletheia_process refuses a request (dispatch_invalid_json for one that is
 * not JSON), a property refused with code handler_property_refused, its
 * message the reason set_properties gives after "SetProperties: property N: ",
 * or code ffi_validation_error for a text struct aletheia_text refuses.
 * Every call writes err: NULL when the kernel accepts the property.
 */
struct aletheia_property_check {
    char *err;
};

static_assert(sizeof(struct aletheia_text) == 16, "aletheia_text size");
static_assert(alignof(struct aletheia_text) == 8, "aletheia_text alignment");
static_assert(offsetof(struct aletheia_text, data) == 0, "aletheia_text.data");
static_assert(offsetof(struct aletheia_text, size) == 8, "aletheia_text.size");
static_assert(sizeof(struct aletheia_frame) == 32, "aletheia_frame size");
static_assert(alignof(struct aletheia_frame) == 8, "aletheia_frame alignment");
static_assert(offsetof(struct aletheia_frame, timestamp) == 0, "aletheia_frame.timestamp");
static_assert(offsetof(struct aletheia_frame, data) == 8, "aletheia_frame.data");
static_assert(offsetof(struct aletheia_frame, can_id) == 16, "aletheia_frame.can_id");
static_assert(offsetof(struct aletheia_frame, extended) == 20, "aletheia_frame.extended");
static_assert(offsetof(struct aletheia_frame, dlc) == 21, "aletheia_frame.dlc");
static_assert(offsetof(struct aletheia_frame, data_len) == 22, "aletheia_frame.data_len");
static_assert(offsetof(struct aletheia_frame, brs_present) == 23, "aletheia_frame.brs_present");
static_assert(offsetof(struct aletheia_frame, brs_value) == 24, "aletheia_frame.brs_value");
static_assert(offsetof(struct aletheia_frame, esi_present) == 25, "aletheia_frame.esi_present");
static_assert(offsetof(struct aletheia_frame, esi_value) == 26, "aletheia_frame.esi_value");
static_assert(sizeof(struct aletheia_uint128) == 16, "aletheia_uint128 size");
static_assert(alignof(struct aletheia_uint128) == 8, "aletheia_uint128 alignment");
static_assert(offsetof(struct aletheia_uint128, lo) == 0, "aletheia_uint128.lo");
static_assert(offsetof(struct aletheia_uint128, hi) == 8, "aletheia_uint128.hi");
static_assert(sizeof(struct aletheia_rational) == 40, "aletheia_rational size");
static_assert(alignof(struct aletheia_rational) == 8, "aletheia_rational alignment");
static_assert(offsetof(struct aletheia_rational, numerator) == 0, "aletheia_rational.numerator");
static_assert(offsetof(struct aletheia_rational, denominator) == 16, "aletheia_rational.denominator");
static_assert(offsetof(struct aletheia_rational, negative) == 32, "aletheia_rational.negative");
static_assert(sizeof(struct aletheia_signal_values) == 24, "aletheia_signal_values size");
static_assert(alignof(struct aletheia_signal_values) == 8, "aletheia_signal_values alignment");
static_assert(offsetof(struct aletheia_signal_values, indices) == 0, "aletheia_signal_values.indices");
static_assert(offsetof(struct aletheia_signal_values, values) == 8, "aletheia_signal_values.values");
static_assert(offsetof(struct aletheia_signal_values, count) == 16, "aletheia_signal_values.count");
static_assert(sizeof(struct aletheia_buffer) == 24, "aletheia_buffer size");
static_assert(alignof(struct aletheia_buffer) == 8, "aletheia_buffer alignment");
static_assert(offsetof(struct aletheia_buffer, data) == 0, "aletheia_buffer.data");
static_assert(offsetof(struct aletheia_buffer, err) == 8, "aletheia_buffer.err");
static_assert(offsetof(struct aletheia_buffer, size) == 16, "aletheia_buffer.size");
static_assert(sizeof(struct aletheia_decimal) == 48, "aletheia_decimal size");
static_assert(alignof(struct aletheia_decimal) == 8, "aletheia_decimal alignment");
static_assert(offsetof(struct aletheia_decimal, value) == 0, "aletheia_decimal.value");
static_assert(offsetof(struct aletheia_decimal, err) == 40, "aletheia_decimal.err");
static_assert(sizeof(struct aletheia_time_bound) == 16, "aletheia_time_bound size");
static_assert(alignof(struct aletheia_time_bound) == 8, "aletheia_time_bound alignment");
static_assert(offsetof(struct aletheia_time_bound, microseconds) == 0, "aletheia_time_bound.microseconds");
static_assert(offsetof(struct aletheia_time_bound, err) == 8, "aletheia_time_bound.err");
static_assert(sizeof(struct aletheia_property_check) == 8, "aletheia_property_check size");
static_assert(alignof(struct aletheia_property_check) == 8, "aletheia_property_check alignment");
static_assert(offsetof(struct aletheia_property_check, err) == 0, "aletheia_property_check.err");

/*
 * The version of this ABI: the layout of the structures above and the
 * signatures below. Any change to either changes the number. A binding reads
 * aletheia_abi_version() from the library it loads and refuses a library
 * whose number is not the one it was written against, rather than calling an
 * entry whose arguments it would lay out differently.
 */
constexpr uint32_t ALETHEIA_ABI_VERSION = 4;

/*
 * GHC Runtime System initialization.
 *
 * Must be called exactly once per process, before any aletheia_* call but
 * aletheia_abi_version().
 * argc and argv may be NULL/0 for default RTS options.
 *
 * IMPORTANT: Never call hs_exit() after hs_init(). The GHC RTS does not
 * support reinitialization: calling hs_exit() followed by hs_init() will
 * crash. The RTS is cleaned up automatically at process exit.
 */
void hs_init(int *argc, char ***argv);

/*
 * The ABI version this library implements: ALETHEIA_ABI_VERSION as it stood
 * when the library was built.
 */
[[nodiscard]] uint32_t aletheia_abi_version();

/*
 * Create a new Aletheia session.
 *
 * Returns an opaque state handle for use with aletheia_process().
 * Each session maintains independent LTL evaluation state; multiple
 * sessions may run concurrently from separate threads.
 *
 * The handle must be freed with aletheia_close() when no longer needed.
 */
[[nodiscard("close the session with aletheia_close")]] void *aletheia_init();

/*
 * Process a JSON command and return the response.
 *
 * @param state   Handle from aletheia_init(). Must not be NULL.
 * @param input   The JSON command. A text struct aletheia_text refuses is
 *                answered with an ffi_validation_error response.
 * @return        UTF-8 encoded, null-terminated JSON response.
 *                The caller MUST free the returned string with
 *                aletheia_free_str(). Returns NULL only on allocation failure.
 *
 * Thread safety: A single state handle must not be used from multiple threads
 * concurrently. Different state handles may be used from different threads.
 *
 * See the Aletheia JSON protocol documentation for command/response formats.
 */
[[nodiscard("free the reply with aletheia_free_str")]] char *
aletheia_process(void *state, const struct aletheia_text *input);

/*
 * Send a binary CAN frame for LTL analysis (streaming hot path).
 *
 * This is the high-performance entry point for data frames. Unlike
 * aletheia_process(), no JSON parsing occurs on the input side.
 *
 * @param state   Handle from aletheia_init(). Must not be NULL.
 * @param frame   The frame; every field is read. A NULL frame is refused.
 * @return        UTF-8 encoded, null-terminated JSON response.
 *                The caller MUST free the returned string with
 *                aletheia_free_str(). Returns NULL only on allocation failure.
 *
 * Thread safety: Same as aletheia_process(), one thread per state handle.
 *
 * Requires streaming mode (aletheia_start_stream() first).
 */
[[nodiscard("free the reply with aletheia_free_str")]] char *
aletheia_send_frame(void *state, const struct aletheia_frame *frame);

/*
 * Send a CAN error frame for LTL analysis: a bus-error event, which carries a
 * timestamp and nothing else. Reads the frame's timestamp only.
 * @return  Same contract as aletheia_send_frame().
 */
[[nodiscard("free the reply with aletheia_free_str")]] char *
aletheia_send_error(void *state, const struct aletheia_frame *frame);

/*
 * Send a CAN remote frame for LTL analysis: an identifier and no payload
 * (ISO 11898). Reads the frame's timestamp, can_id and extended.
 * @return  Same contract as aletheia_send_frame().
 */
[[nodiscard("free the reply with aletheia_free_str")]] char *
aletheia_send_remote(void *state, const struct aletheia_frame *frame);

/*
 * Stream lifecycle and DBC export, answering JSON as aletheia_process() does.
 */
[[nodiscard("free the reply with aletheia_free_str")]] char *aletheia_start_stream(void *state);
[[nodiscard("free the reply with aletheia_free_str")]] char *aletheia_end_stream(void *state);
[[nodiscard("free the reply with aletheia_free_str")]] char *aletheia_format_dbc(void *state);

/*
 * Extract a frame's signals against the loaded DBC, answering JSON.
 *
 * Reads the frame's can_id, extended, dlc, data and data_len.
 * @return  Same contract as aletheia_send_frame().
 */
[[nodiscard("free the reply with aletheia_free_str")]] char *
aletheia_extract_signals(void *state, const struct aletheia_frame *frame);

/*
 * Build a payload from signal values, writing raw bytes into out.
 *
 * Reads the frame's can_id, extended and dlc. out->data must hold the DLC's
 * byte count, given in out->size.
 * @return  0 on success, 1 on failure with out->err set (see
 *          struct aletheia_buffer).
 */
[[nodiscard("1 is a refusal, its err freed with aletheia_free_str")]] int8_t
aletheia_build_frame_bin(void *state, const struct aletheia_frame *frame,
                         const struct aletheia_signal_values *values, struct aletheia_buffer *out);

/*
 * Rewrite signal values in the frame's payload, writing the new payload into
 * out. Reads the frame's can_id, extended, dlc, data and data_len; out as for
 * aletheia_build_frame_bin().
 */
[[nodiscard("1 is a refusal, its err freed with aletheia_free_str")]] int8_t
aletheia_update_frame_bin(void *state, const struct aletheia_frame *frame,
                          const struct aletheia_signal_values *values, struct aletheia_buffer *out);

/*
 * Extract a frame's signals into the packed binary layout the protocol
 * documentation specifies, allocated into out (see struct aletheia_buffer).
 * Reads the frame's can_id, extended, dlc, data and data_len.
 * @return  0 on success, 1 on failure with out->err set.
 */
[[nodiscard("1 is a refusal, its err freed with aletheia_free_str")]] int8_t
aletheia_extract_signals_bin(void *state, const struct aletheia_frame *frame,
                             struct aletheia_buffer *out);

/*
 * Render a rational as the decimal or fraction string every binding prints.
 * Free the result with aletheia_free_str(). A NULL rational answers NULL.
 */
[[nodiscard("free the string with aletheia_free_str")]] char *
aletheia_format_rational(const struct aletheia_rational *value);

/*
 * Parse a decimal string into the exact rational it denotes (see
 * struct aletheia_decimal).
 * @return  0 on success, 1 on failure with out->err set. A text struct
 *          aletheia_text refuses is such a failure, code ffi_validation_error;
 *          a NULL out returns 1 with nothing written.
 */
[[nodiscard("1 is a refusal, its err freed with aletheia_free_str")]] int8_t
aletheia_parse_decimal(const struct aletheia_text *input, struct aletheia_decimal *out);

/*
 * Parse a time bound, a decimal string of microseconds, into the whole number
 * it denotes (see struct aletheia_time_bound).
 * @return  0 on success, 1 on failure with out->err set. A text struct
 *          aletheia_text refuses is such a failure, code ffi_validation_error;
 *          a NULL out returns 1 with nothing written.
 */
[[nodiscard("1 is a refusal, its err freed with aletheia_free_str")]] int8_t
aletheia_parse_time_bound(const struct aletheia_text *input, struct aletheia_time_bound *out);

/*
 * Check a property's JSON as set_properties reads one, before any session
 * holds it: every field, ordering, denominator and time bound is decided, and
 * each signal name as an identifier, its presence in a DBC left to
 * set_properties (see struct aletheia_property_check).
 * @return  0 when the kernel accepts the property, 1 on refusal with out->err
 *          set. A text struct aletheia_text refuses is such a refusal, code
 *          ffi_validation_error; a NULL out returns 1 with nothing written.
 */
[[nodiscard("1 is a refusal, its err freed with aletheia_free_str")]] int8_t
aletheia_check_property(const struct aletheia_text *property, struct aletheia_property_check *out);

/*
 * The bytes the runtime has allocated since it started, in every session and
 * thread of the process. The call runs a collection first, because the
 * runtime counts an allocation area only when it collects it, so the count
 * covers every allocation made before the call, and the difference of two
 * calls is what ran between them allocated. Call it only once the runtime
 * has started (hs_init).
 */
[[nodiscard]] uint64_t aletheia_allocated_bytes();

/*
 * Free a string returned by any aletheia_* function that returns char*, or
 * the err of a result structure. Passing NULL is safe (no-op).
 */
void aletheia_free_str(char *ptr);

/*
 * Free the data aletheia_extract_signals_bin() allocated.
 */
void aletheia_free_buf(uint8_t *ptr);

/*
 * Close a session and free its state.
 *
 * @param state   Handle from aletheia_init().
 *                The handle must not be used after this call.
 */
void aletheia_close(void *state);

#ifdef __cplusplus
}
#endif

#endif /* ALETHEIA_H */
