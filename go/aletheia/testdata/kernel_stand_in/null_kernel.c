// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A kernel stand-in that answers every call with nothing: a null session, a
// null string, a null render. It carries every symbol the backend resolves,
// at the kernel's own signatures, so the backend opens it and the suite can
// read what the binding does with a null where the real kernel never hands
// one. Its runtime entry is a no-op, so a process that opens it reads the
// runtime as up without a runtime, which is what lets the renderer and the
// decimal parser reach their null answers. The suite compiles it into a
// temporary directory with the C compiler cgo already requires.
#include <stdint.h>
#include <stdlib.h>

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

char *aletheia_process(void *state, const char *input) {
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

char *aletheia_send_error(void *state, uint64_t ts) {
    (void)state;
    (void)ts;
    return NULL;
}

char *aletheia_send_remote(void *state, uint64_t ts, uint32_t id, uint8_t extended) {
    (void)state;
    (void)ts;
    (void)id;
    (void)extended;
    return NULL;
}

char *aletheia_send_frame(void *state, uint64_t ts, uint32_t id, uint8_t extended, uint8_t dlc,
                          const uint8_t *data, uint8_t len, uint8_t brs_present,
                          uint8_t brs_value, uint8_t esi_present, uint8_t esi_value) {
    (void)state;
    (void)ts;
    (void)id;
    (void)extended;
    (void)dlc;
    (void)data;
    (void)len;
    (void)brs_present;
    (void)brs_value;
    (void)esi_present;
    (void)esi_value;
    return NULL;
}

char *aletheia_format_rational(int64_t num, int64_t den) {
    (void)num;
    (void)den;
    return NULL;
}

char *aletheia_parse_decimal(const char *input) {
    (void)input;
    return NULL;
}

char *aletheia_extract_signals(void *state, uint32_t id, uint8_t extended, uint8_t dlc,
                               const uint8_t *data, uint8_t len) {
    (void)state;
    (void)id;
    (void)extended;
    (void)dlc;
    (void)data;
    (void)len;
    return NULL;
}

int8_t aletheia_build_frame_bin(void *state, uint32_t id, uint8_t extended, uint8_t dlc,
                                uint32_t count, const uint32_t *indices, const int64_t *nums,
                                const int64_t *dens, uint8_t *out, char **err) {
    (void)state;
    (void)id;
    (void)extended;
    (void)dlc;
    (void)count;
    (void)indices;
    (void)nums;
    (void)dens;
    (void)out;
    *err = NULL;
    return 1;
}

int8_t aletheia_update_frame_bin(void *state, uint32_t id, uint8_t extended, uint8_t dlc,
                                 const uint8_t *data, uint8_t len, uint32_t count,
                                 const uint32_t *indices, const int64_t *nums, const int64_t *dens,
                                 uint8_t *out, char **err) {
    (void)state;
    (void)id;
    (void)extended;
    (void)dlc;
    (void)data;
    (void)len;
    (void)count;
    (void)indices;
    (void)nums;
    (void)dens;
    (void)out;
    *err = NULL;
    return 1;
}

int8_t aletheia_extract_signals_bin(void *state, uint32_t id, uint8_t extended, uint8_t dlc,
                                    const uint8_t *data, uint8_t len, uint8_t **out,
                                    uint32_t *out_size, char **err) {
    (void)state;
    (void)id;
    (void)extended;
    (void)dlc;
    (void)data;
    (void)len;
    (void)out;
    (void)out_size;
    *err = NULL;
    return 1;
}
