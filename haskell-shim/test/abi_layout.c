// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * The C half of the abi-layout test: fills each structure of aletheia.h with
 * a value whose every byte differs from its neighbours', and checks a copy
 * field by field. A field Haskell reads or writes at the wrong offset lands
 * a byte the check does not expect.
 */
#include "aletheia.h"

#include <stdint.h>
#include <string.h>

static const struct aletheia_frame frame_sample = {
    .timestamp = 0x0102030405060708u,
    .data = (const uint8_t *)(uintptr_t)0x1112131415161718u,
    .can_id = 0x21222324u,
    .extended = 0x31,
    .dlc = 0x32,
    .data_len = 0x33,
    .brs_present = 0x34,
    .brs_value = 0x35,
    .esi_present = 0x36,
    .esi_value = 0x37,
};

static const struct aletheia_signal_values values_sample = {
    .indices = (const uint32_t *)(uintptr_t)0x4142434445464748u,
    .numerators = (const int64_t *)(uintptr_t)0x5152535455565758u,
    .denominators = (const int64_t *)(uintptr_t)0x6162636465666768u,
    .count = 0x71727374u,
};

static const struct aletheia_buffer buffer_sample = {
    .data = (uint8_t *)(uintptr_t)0x8182838485868788u,
    .err = (char *)(uintptr_t)0x9192939495969798u,
    .size = 0xA1A2A3A4u,
};

static const struct aletheia_rational rational_sample = {
    .numerator = 0x0B0C0D0E0F101112,
    .denominator = 0x1314151617181920,
};

static const struct aletheia_decimal decimal_sample = {
    .value = {.numerator = 0x2122232425262728, .denominator = 0x3132333435363738},
    .err = (char *)(uintptr_t)0x4142434445464748u,
};

size_t abi_frame_size(void) { return sizeof(struct aletheia_frame); }
size_t abi_frame_align(void) { return _Alignof(struct aletheia_frame); }
size_t abi_values_size(void) { return sizeof(struct aletheia_signal_values); }
size_t abi_values_align(void) { return _Alignof(struct aletheia_signal_values); }
size_t abi_buffer_size(void) { return sizeof(struct aletheia_buffer); }
size_t abi_buffer_align(void) { return _Alignof(struct aletheia_buffer); }

size_t abi_rational_size(void) { return sizeof(struct aletheia_rational); }
size_t abi_rational_align(void) { return _Alignof(struct aletheia_rational); }
size_t abi_decimal_size(void) { return sizeof(struct aletheia_decimal); }
size_t abi_decimal_align(void) { return _Alignof(struct aletheia_decimal); }

void abi_fill_rational(struct aletheia_rational *r) { *r = rational_sample; }
void abi_fill_decimal(struct aletheia_decimal *d) { *d = decimal_sample; }
void abi_fill_frame(struct aletheia_frame *f) { *f = frame_sample; }
void abi_fill_values(struct aletheia_signal_values *v) { *v = values_sample; }
void abi_fill_buffer(struct aletheia_buffer *b) { *b = buffer_sample; }

/* Each check answers a bit per field that differs from the sample, 0 when
 * the copy is exact. */
unsigned abi_check_frame(const struct aletheia_frame *f) {
    const struct aletheia_frame *s = &frame_sample;
    return (unsigned)(f->timestamp != s->timestamp) << 0 |
           (unsigned)(f->data != s->data) << 1 | (unsigned)(f->can_id != s->can_id) << 2 |
           (unsigned)(f->extended != s->extended) << 3 | (unsigned)(f->dlc != s->dlc) << 4 |
           (unsigned)(f->data_len != s->data_len) << 5 |
           (unsigned)(f->brs_present != s->brs_present) << 6 |
           (unsigned)(f->brs_value != s->brs_value) << 7 |
           (unsigned)(f->esi_present != s->esi_present) << 8 |
           (unsigned)(f->esi_value != s->esi_value) << 9;
}

unsigned abi_check_values(const struct aletheia_signal_values *v) {
    const struct aletheia_signal_values *s = &values_sample;
    return (unsigned)(v->indices != s->indices) << 0 |
           (unsigned)(v->numerators != s->numerators) << 1 |
           (unsigned)(v->denominators != s->denominators) << 2 |
           (unsigned)(v->count != s->count) << 3;
}

unsigned abi_check_buffer(const struct aletheia_buffer *b) {
    const struct aletheia_buffer *s = &buffer_sample;
    return (unsigned)(b->data != s->data) << 0 | (unsigned)(b->err != s->err) << 1 |
           (unsigned)(b->size != s->size) << 2;
}

unsigned abi_check_rational(const struct aletheia_rational *r) {
    return (unsigned)(r->numerator != rational_sample.numerator) << 0 |
           (unsigned)(r->denominator != rational_sample.denominator) << 1;
}

unsigned abi_check_decimal(const struct aletheia_decimal *d) {
    const struct aletheia_decimal *s = &decimal_sample;
    return (unsigned)(d->value.numerator != s->value.numerator) << 0 |
           (unsigned)(d->value.denominator != s->value.denominator) << 1 |
           (unsigned)(d->err != s->err) << 2;
}
