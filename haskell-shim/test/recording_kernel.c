// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers the kernel's entries with a refusal quoting
// what it was handed, so a test can read what a binding marshals to the kernel
// entries whose arguments the real kernel acknowledges without reading: the
// timestamp of an error or remote event, the CAN-FD bus bits of a frame, and
// the size of a command's text. It counts the closes and the frees it is
// handed, so a test reads that a state was closed or a string released, which
// the real kernel acknowledges without reading and which only a leak checker
// would otherwise report. Its renderer answers the rational it was handed, but
// for one numerator it answers with a null string, so a test can follow a
// render that held with one that failed, its property check refuses quoting
// the property, so a test reads the text a binding sends, and its allocation
// count is a known value, so a test reads what reached them. It
// carries every symbol the bindings resolve, at the kernel's own signatures,
// its count of the process's CPUs is four, and its runtime entry is a no-op, so a process whose first backend opens it
// reads the runtime as up without one. The build makes it beside the library,
// where the bindings' tests load it.
#include "aletheia.h"

#include <inttypes.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// The message the binding frees through aletheia_free_str, so it is one block
// from the allocator the kernel's own strings come from.
static char *handed_back(const char *text) {
    size_t size = strlen(text) + 1;
    char *out = malloc(size);
    if (out != nullptr)
        memcpy(out, text, size);
    return out;
}

static char *refusal(const char *detail) {
    char text[512];
    snprintf(text, sizeof text,
             "{\"status\":\"error\",\"code\":\"recording_kernel\",\"message\":\"%s\"}", detail);
    return handed_back(text);
}

uint32_t aletheia_abi_version() {
    return ALETHEIA_ABI_VERSION;
}

void hs_init_with_rtsopts(int *, char ***) {}

// The CPUs the stand-in says the process may use: four, whatever the machine,
// so a test asks a count past the bound or within it and reads the same answer
// on every machine.
uint32_t getNumberOfProcessors() {
    return 4;
}

void *aletheia_init() {
    static int state = 0;
    return &state;
}

// Closes are counted so a test can read that the state it opened was closed.
static atomic_int closes;
void aletheia_close(void *) {
    atomic_fetch_add(&closes, 1);
}
int aletheia_test_close_count() {
    return atomic_load(&closes);
}

// Frees are counted too: a string the binding failed to release is a leak
// only a sanitizer would report, where the count reads the release itself.
static atomic_int frees;
void aletheia_free_str(char *p) {
    atomic_fetch_add(&frees, 1);
    free(p);
}
int aletheia_test_free_count() {
    return atomic_load(&frees);
}

void aletheia_free_buf(uint8_t *) {}

char *aletheia_process(void *, const struct aletheia_text *input) {
    char detail[64];
    snprintf(detail, sizeof detail, "process size=%zu", input->size);
    return refusal(detail);
}

char *aletheia_start_stream(void *) {
    return refusal("start_stream");
}

char *aletheia_end_stream(void *) {
    return refusal("end_stream");
}

char *aletheia_format_dbc(void *) {
    return refusal("format_dbc");
}

char *aletheia_send_error(void *, const struct aletheia_frame *frame) {
    char detail[64];
    snprintf(detail, sizeof detail, "send_error ts=%" PRIu64, frame->timestamp);
    return refusal(detail);
}

char *aletheia_send_remote(void *, const struct aletheia_frame *frame) {
    char detail[96];
    snprintf(detail, sizeof detail, "send_remote ts=%" PRIu64 " id=%" PRIu32 " extended=%u",
             frame->timestamp, frame->can_id, frame->extended);
    return refusal(detail);
}

char *aletheia_send_frame(void *, const struct aletheia_frame *frame) {
    char detail[160];
    snprintf(detail, sizeof detail,
             "send_frame ts=%" PRIu64 " id=%" PRIu32 " extended=%u dlc=%u len=%u brs=%u/%u esi=%u/%u",
             frame->timestamp, frame->can_id, frame->extended, frame->dlc, frame->data_len,
             frame->brs_present, frame->brs_value, frame->esi_present, frame->esi_value);
    return refusal(detail);
}

// The numerator the renderer refuses, answering a null string: 7919, not
// negative.
static constexpr uint64_t refused_numerator = 7919;

// The decimal digits of a 128-bit number, written backwards from end, which
// the 39 digits of 2^128 - 1 fit before; answers where the digits start.
static char *digits(struct aletheia_uint128 n, char *end) {
    unsigned _BitInt(128) value = (unsigned _BitInt(128))n.hi << 64 | n.lo;
    do {
        *--end = (char)('0' + (int)(value % 10));
        value /= 10;
    } while (value != 0);
    return end;
}

// The renderer and the three parsers, so the stand-in serves them too: what
// the binding hands the kernel is the question, and a parse answers nothing. A
// render is the numerator and the denominator in decimal, the numerator
// signed, so a test reads every word and the sign that reached the kernel.
char *aletheia_format_rational(const struct aletheia_rational *value) {
    if (value->negative == 0 && value->numerator.hi == 0 &&
        value->numerator.lo == refused_numerator)
        return nullptr;
    char numerator[40] = {};
    char denominator[40] = {};
    char text[96];
    snprintf(text, sizeof text, "%s%s/%s", value->negative != 0 ? "-" : "",
             digits(value->numerator, numerator + sizeof numerator - 1),
             digits(value->denominator, denominator + sizeof denominator - 1));
    return handed_back(text);
}

int8_t aletheia_parse_decimal(const struct aletheia_text *, struct aletheia_decimal *out) {
    out->err = refusal("parse_decimal");
    return 1;
}

int8_t aletheia_parse_time_bound(const struct aletheia_text *, struct aletheia_time_bound *out) {
    out->err = refusal("parse_time_bound");
    return 1;
}

// The property quoted as a JSON string's content: a quote, a backslash and a
// control character escaped, the rest dropped once the message is full.
int8_t aletheia_check_property(const struct aletheia_text *property,
                               struct aletheia_property_check *out) {
    char detail[400];
    size_t at = (size_t)snprintf(detail, sizeof detail, "check_property ");
    for (size_t i = 0; i < property->size && at + 7 < sizeof detail; ++i) {
        unsigned char c = (unsigned char)property->data[i];
        if (c == '"' || c == '\\')
            at += (size_t)snprintf(detail + at, sizeof detail - at, "\\%c", c);
        else if (c < 0x20)
            at += (size_t)snprintf(detail + at, sizeof detail - at, "\\u%04x", c);
        else
            detail[at++] = (char)c;
    }
    detail[at] = '\0';
    out->err = refusal(detail);
    return 1;
}

// The allocation count is 2^63 plus the reads made before this one: a read
// that dropped a high bit or took the count as signed reads another number,
// and two reads in a row differ by one, so a test reads that the whole count
// came back and that each read reached the stand-in.
static atomic_uint_fast64_t allocation_reads;
uint64_t aletheia_allocated_bytes() {
    return (UINT64_C(1) << 63) + atomic_fetch_add(&allocation_reads, 1);
}

char *aletheia_extract_signals(void *, const struct aletheia_frame *) {
    return refusal("extract_signals");
}

// The three binary entries refuse with an error envelope, as the kernel's do.
int8_t aletheia_build_frame_bin(void *, const struct aletheia_frame *,
                                const struct aletheia_signal_values *,
                                struct aletheia_buffer *out) {
    out->err = refusal("build_frame_bin");
    return 1;
}

int8_t aletheia_update_frame_bin(void *, const struct aletheia_frame *,
                                 const struct aletheia_signal_values *,
                                 struct aletheia_buffer *out) {
    out->err = refusal("update_frame_bin");
    return 1;
}

int8_t aletheia_extract_signals_bin(void *, const struct aletheia_frame *,
                                    struct aletheia_buffer *out) {
    out->err = refusal("extract_signals_bin");
    return 1;
}
