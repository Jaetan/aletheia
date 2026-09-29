// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers every call with nothing: a null session, a
// null string, a null render. It carries every symbol the backend resolves,
// at the kernel's own signatures, so the backend opens it and the suite can
// read what the binding does with a null where the real kernel never hands
// one. The kernel's header holds each entry to the kernel's signature. Its
// runtime entry is a no-op, so a process that opens it reads the runtime as
// up without a runtime, which is what lets the renderer and the decimal
// parser reach their null answers. The suite compiles it into a temporary
// directory with the C compiler cgo already requires.
#include "aletheia.h"

#include <stdint.h>
#include <stdlib.h>

uint32_t aletheia_abi_version(void) {
    return ALETHEIA_ABI_VERSION;
}

void hs_init_with_rtsopts(int *argc, char ***argv) {
    (void)argc;
    (void)argv;
}

void *aletheia_init(void) {
    return NULL;
}

void aletheia_close(void *state) {
    (void)state;
}

void aletheia_free_str(char *p) {
    free(p);
}

void aletheia_free_buf(uint8_t *buf) {
    free(buf);
}

char *aletheia_process(void *state, const struct aletheia_text *input) {
    (void)state;
    (void)input;
    return NULL;
}

char *aletheia_start_stream(void *state) {
    (void)state;
    return NULL;
}

char *aletheia_end_stream(void *state) {
    (void)state;
    return NULL;
}

char *aletheia_format_dbc(void *state) {
    (void)state;
    return NULL;
}

char *aletheia_send_error(void *state, const struct aletheia_frame *frame) {
    (void)state;
    (void)frame;
    return NULL;
}

char *aletheia_send_remote(void *state, const struct aletheia_frame *frame) {
    (void)state;
    (void)frame;
    return NULL;
}

char *aletheia_send_frame(void *state, const struct aletheia_frame *frame) {
    (void)state;
    (void)frame;
    return NULL;
}

char *aletheia_format_rational(const struct aletheia_rational *value) {
    (void)value;
    return NULL;
}

int8_t aletheia_parse_decimal(const struct aletheia_text *input, struct aletheia_decimal *out) {
    (void)input;
    out->err = NULL;
    return 1;
}

char *aletheia_extract_signals(void *state, const struct aletheia_frame *frame) {
    (void)state;
    (void)frame;
    return NULL;
}

int8_t aletheia_build_frame_bin(void *state, const struct aletheia_frame *frame,
                                const struct aletheia_signal_values *values,
                                struct aletheia_buffer *out) {
    (void)state;
    (void)frame;
    (void)values;
    out->err = NULL;
    return 1;
}

int8_t aletheia_update_frame_bin(void *state, const struct aletheia_frame *frame,
                                 const struct aletheia_signal_values *values,
                                 struct aletheia_buffer *out) {
    (void)state;
    (void)frame;
    (void)values;
    out->err = NULL;
    return 1;
}

int8_t aletheia_extract_signals_bin(void *state, const struct aletheia_frame *frame,
                                    struct aletheia_buffer *out) {
    (void)state;
    (void)frame;
    out->err = NULL;
    return 1;
}
