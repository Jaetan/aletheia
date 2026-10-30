// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers every call with nothing: a null session, a
// null string, a null render. It carries every symbol the backend resolves,
// at the kernel's own signatures, so the backend opens it and the suite can
// read what the binding does with a null where the real kernel never hands
// one. The kernel's header holds each entry to the kernel's signature. Its
// runtime entry is a no-op, so a process that opens it reads the runtime as
// up without a runtime, which is what lets the renderer, the decimal parser,
// the time-bound parser and the property check reach their null answers. The
// build makes it beside the library, where the bindings' tests load it.
#include "aletheia.h"

#include <stdint.h>
#include <stdlib.h>

uint32_t aletheia_abi_version() {
    return ALETHEIA_ABI_VERSION;
}

void hs_init_with_rtsopts(int *, char ***) {}

// The CPUs the process may use, as the runtime counts them: one, the count every
// backend that opens this stand-in asks.
uint32_t getNumberOfProcessors() {
    return 1;
}

void *aletheia_init() {
    return nullptr;
}

void aletheia_close(void *) {}

void aletheia_free_str(char *p) {
    free(p);
}

void aletheia_free_buf(uint8_t *buf) {
    free(buf);
}

char *aletheia_process(void *, const struct aletheia_text *) {
    return nullptr;
}

char *aletheia_start_stream(void *) {
    return nullptr;
}

char *aletheia_end_stream(void *) {
    return nullptr;
}

char *aletheia_format_dbc(void *) {
    return nullptr;
}

char *aletheia_send_error(void *, const struct aletheia_frame *) {
    return nullptr;
}

char *aletheia_send_remote(void *, const struct aletheia_frame *) {
    return nullptr;
}

char *aletheia_send_frame(void *, const struct aletheia_frame *) {
    return nullptr;
}

char *aletheia_format_rational(const struct aletheia_rational *) {
    return nullptr;
}

int8_t aletheia_parse_decimal(const struct aletheia_text *, struct aletheia_decimal *out) {
    *out = (struct aletheia_decimal){};
    return 1;
}

int8_t aletheia_parse_time_bound(const struct aletheia_text *, struct aletheia_time_bound *out) {
    *out = (struct aletheia_time_bound){};
    return 1;
}

int8_t aletheia_check_property(const struct aletheia_text *, struct aletheia_property_check *out) {
    *out = (struct aletheia_property_check){};
    return 1;
}

uint64_t aletheia_allocated_bytes() {
    return 0;
}

char *aletheia_extract_signals(void *, const struct aletheia_frame *) {
    return nullptr;
}

int8_t aletheia_build_frame_bin(void *, const struct aletheia_frame *,
                                const struct aletheia_signal_values *,
                                struct aletheia_buffer *out) {
    out->err = nullptr;
    return 1;
}

int8_t aletheia_update_frame_bin(void *, const struct aletheia_frame *,
                                 const struct aletheia_signal_values *,
                                 struct aletheia_buffer *out) {
    out->err = nullptr;
    return 1;
}

int8_t aletheia_extract_signals_bin(void *, const struct aletheia_frame *,
                                    struct aletheia_buffer *out) {
    out->err = nullptr;
    return 1;
}
