// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers every call with a refusal quoting what it
// was handed, so a test can read what a binding marshals to the kernel
// entries whose arguments the real kernel acknowledges without reading: the
// timestamp of an error or remote event, the CAN-FD bus bits of a frame, and
// the size of a command's text. It counts the closes and the frees it is
// handed, so a test reads that a state was closed or a string released, which
// the real kernel acknowledges without reading and which only a leak checker
// would otherwise report. It carries every symbol the bindings resolve, at the
// kernel's own signatures, and its runtime entry is a no-op: the runtime is
// brought up once per process by the first backend a suite builds, on the
// real library, and never by this one. The build makes it beside the library,
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
    if (out != NULL)
        memcpy(out, text, size);
    return out;
}

static char *refusal(const char *detail) {
    char text[512];
    snprintf(text, sizeof text,
             "{\"status\":\"error\",\"code\":\"recording_kernel\",\"message\":\"%s\"}", detail);
    return handed_back(text);
}

uint32_t aletheia_abi_version(void) {
    return ALETHEIA_ABI_VERSION;
}

void hs_init_with_rtsopts(int *argc, char ***argv) {
    (void)argc;
    (void)argv;
}

void *aletheia_init(void) {
    static int state = 0;
    return &state;
}

// Closes are counted so a test can read that the state it opened was closed.
static atomic_int closes;
void aletheia_close(void *state) {
    (void)state;
    atomic_fetch_add(&closes, 1);
}
int aletheia_test_close_count(void) {
    return atomic_load(&closes);
}

// Frees are counted too: a string the binding failed to release is a leak
// only a sanitizer would report, where the count reads the release itself.
static atomic_int frees;
void aletheia_free_str(char *p) {
    atomic_fetch_add(&frees, 1);
    free(p);
}
int aletheia_test_free_count(void) {
    return atomic_load(&frees);
}

void aletheia_free_buf(uint8_t *buf) {
    (void)buf;
}

char *aletheia_process(void *state, const struct aletheia_text *input) {
    (void)state;
    char detail[64];
    snprintf(detail, sizeof detail, "process size=%zu", input->size);
    return refusal(detail);
}

char *aletheia_start_stream(void *state) {
    (void)state;
    return refusal("start_stream");
}

char *aletheia_end_stream(void *state) {
    (void)state;
    return refusal("end_stream");
}

char *aletheia_format_dbc(void *state) {
    (void)state;
    return refusal("format_dbc");
}

char *aletheia_send_error(void *state, const struct aletheia_frame *frame) {
    (void)state;
    char detail[64];
    snprintf(detail, sizeof detail, "send_error ts=%" PRIu64, frame->timestamp);
    return refusal(detail);
}

char *aletheia_send_remote(void *state, const struct aletheia_frame *frame) {
    (void)state;
    char detail[96];
    snprintf(detail, sizeof detail, "send_remote ts=%" PRIu64 " id=%" PRIu32 " extended=%u",
             frame->timestamp, frame->can_id, frame->extended);
    return refusal(detail);
}

char *aletheia_send_frame(void *state, const struct aletheia_frame *frame) {
    (void)state;
    char detail[160];
    snprintf(detail, sizeof detail,
             "send_frame ts=%" PRIu64 " id=%" PRIu32 " extended=%u dlc=%u len=%u brs=%u/%u esi=%u/%u",
             frame->timestamp, frame->can_id, frame->extended, frame->dlc, frame->data_len,
             frame->brs_present, frame->brs_value, frame->esi_present, frame->esi_value);
    return refusal(detail);
}

// The renderer's three entries, so the stand-in serves it too: what the
// binding hands the kernel is the question, and a render answers nothing.
char *aletheia_format_rational(const struct aletheia_rational *value) {
    char text[64];
    snprintf(text, sizeof text, "%" PRIu64 "/%" PRIu64, (uint64_t)value->numerator,
             (uint64_t)value->denominator);
    return handed_back(text);
}

int8_t aletheia_parse_decimal(const struct aletheia_text *input, struct aletheia_decimal *out) {
    (void)input;
    out->err = refusal("parse_decimal");
    return 1;
}

char *aletheia_extract_signals(void *state, const struct aletheia_frame *frame) {
    (void)state;
    (void)frame;
    return refusal("extract_signals");
}

// The three binary entries refuse with an error envelope, as the kernel's do.
int8_t aletheia_build_frame_bin(void *state, const struct aletheia_frame *frame,
                                const struct aletheia_signal_values *values,
                                struct aletheia_buffer *out) {
    (void)state;
    (void)frame;
    (void)values;
    out->err = refusal("build_frame_bin");
    return 1;
}

int8_t aletheia_update_frame_bin(void *state, const struct aletheia_frame *frame,
                                 const struct aletheia_signal_values *values,
                                 struct aletheia_buffer *out) {
    (void)state;
    (void)frame;
    (void)values;
    out->err = refusal("update_frame_bin");
    return 1;
}

int8_t aletheia_extract_signals_bin(void *state, const struct aletheia_frame *frame,
                                    struct aletheia_buffer *out) {
    (void)state;
    (void)frame;
    out->err = refusal("extract_signals_bin");
    return 1;
}
