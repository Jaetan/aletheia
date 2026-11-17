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

static const struct aletheia_text text_sample = {
    .data = (const char *)(uintptr_t)0xC1C2C3C4C5C6C7C8u,
    .size = 0xD1D2D3D4D5D6D7D8u,
};

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

static const struct aletheia_uint128 uint128_sample = {
    .lo = 0xE1E2E3E4E5E6E7E8u,
    .hi = 0xF1F2F3F4F5F6F7F8u,
};

static const struct aletheia_signal_values values_sample = {
    .indices = (const uint32_t *)(uintptr_t)0x4142434445464748u,
    .values = (const struct aletheia_rational *)(uintptr_t)0x5152535455565758u,
    .count = 0x71727374u,
};

static const struct aletheia_buffer buffer_sample = {
    .data = (uint8_t *)(uintptr_t)0x8182838485868788u,
    .err = (char *)(uintptr_t)0x9192939495969798u,
    .size = 0xA1A2A3A4u,
};

static const struct aletheia_rational rational_sample = {
    .numerator = {.lo = 0x0B0C0D0E0F101112u, .hi = 0x1314151617181920u},
    .denominator = {.lo = 0x2122232425262728u, .hi = 0x3132333435363738u},
    .negative = 0x39,
};

static const struct aletheia_decimal decimal_sample = {
    .value = {.numerator = {.lo = 0x4142434445464748u, .hi = 0x5152535455565758u},
              .denominator = {.lo = 0x6162636465666768u, .hi = 0x7172737475767778u},
              .negative = 0x79},
    .err = (char *)(uintptr_t)0x8182838485868788u,
};

static const struct aletheia_time_bound time_bound_sample = {
    .microseconds = 0x9192939495969798u,
    .err = (char *)(uintptr_t)0xA1A2A3A4A5A6A7A8u,
};

static const struct aletheia_property_check property_check_sample = {
    .err = (char *)(uintptr_t)0xB1B2B3B4B5B6B7B8u,
};

size_t abi_text_size() { return sizeof(struct aletheia_text); }
size_t abi_text_align() { return alignof(struct aletheia_text); }
size_t abi_frame_size() { return sizeof(struct aletheia_frame); }
size_t abi_frame_align() { return alignof(struct aletheia_frame); }
size_t abi_values_size() { return sizeof(struct aletheia_signal_values); }
size_t abi_values_align() { return alignof(struct aletheia_signal_values); }
size_t abi_buffer_size() { return sizeof(struct aletheia_buffer); }
size_t abi_buffer_align() { return alignof(struct aletheia_buffer); }

size_t abi_uint128_size() { return sizeof(struct aletheia_uint128); }
size_t abi_uint128_align() { return alignof(struct aletheia_uint128); }
size_t abi_rational_size() { return sizeof(struct aletheia_rational); }
size_t abi_rational_align() { return alignof(struct aletheia_rational); }
size_t abi_decimal_size() { return sizeof(struct aletheia_decimal); }
size_t abi_decimal_align() { return alignof(struct aletheia_decimal); }
size_t abi_time_bound_size() { return sizeof(struct aletheia_time_bound); }
size_t abi_time_bound_align() { return alignof(struct aletheia_time_bound); }
size_t abi_property_check_size() { return sizeof(struct aletheia_property_check); }
size_t abi_property_check_align() { return alignof(struct aletheia_property_check); }

void abi_fill_uint128(struct aletheia_uint128 *u) { *u = uint128_sample; }
void abi_fill_rational(struct aletheia_rational *r) { *r = rational_sample; }
void abi_fill_decimal(struct aletheia_decimal *d) { *d = decimal_sample; }
void abi_fill_time_bound(struct aletheia_time_bound *t) { *t = time_bound_sample; }
void abi_fill_property_check(struct aletheia_property_check *c) { *c = property_check_sample; }
void abi_fill_text(struct aletheia_text *t) { *t = text_sample; }
void abi_fill_frame(struct aletheia_frame *f) { *f = frame_sample; }
void abi_fill_values(struct aletheia_signal_values *v) { *v = values_sample; }
void abi_fill_buffer(struct aletheia_buffer *b) { *b = buffer_sample; }

/* Each check answers a bit per field that differs from the sample, 0 when
 * the copy is exact. */
unsigned abi_check_text(const struct aletheia_text *t) {
    return (unsigned)(t->data != text_sample.data) << 0 |
           (unsigned)(t->size != text_sample.size) << 1;
}

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
    return (unsigned)(v->indices != s->indices) << 0 | (unsigned)(v->values != s->values) << 1 |
           (unsigned)(v->count != s->count) << 2;
}

unsigned abi_check_uint128(const struct aletheia_uint128 *u) {
    return (unsigned)(u->lo != uint128_sample.lo) << 0 |
           (unsigned)(u->hi != uint128_sample.hi) << 1;
}

unsigned abi_check_buffer(const struct aletheia_buffer *b) {
    const struct aletheia_buffer *s = &buffer_sample;
    return (unsigned)(b->data != s->data) << 0 | (unsigned)(b->err != s->err) << 1 |
           (unsigned)(b->size != s->size) << 2;
}

// A rational's five bits: one per word and one for the sign.
static unsigned rational_bits(const struct aletheia_rational *r, const struct aletheia_rational *s) {
    return (unsigned)(r->numerator.lo != s->numerator.lo) << 0 |
           (unsigned)(r->numerator.hi != s->numerator.hi) << 1 |
           (unsigned)(r->denominator.lo != s->denominator.lo) << 2 |
           (unsigned)(r->denominator.hi != s->denominator.hi) << 3 |
           (unsigned)(r->negative != s->negative) << 4;
}

unsigned abi_check_rational(const struct aletheia_rational *r) {
    return rational_bits(r, &rational_sample);
}

unsigned abi_check_decimal(const struct aletheia_decimal *d) {
    return rational_bits(&d->value, &decimal_sample.value) |
           (unsigned)(d->err != decimal_sample.err) << 5;
}

unsigned abi_check_time_bound(const struct aletheia_time_bound *t) {
    return (unsigned)(t->microseconds != time_bound_sample.microseconds) << 0 |
           (unsigned)(t->err != time_bound_sample.err) << 1;
}

unsigned abi_check_property_check(const struct aletheia_property_check *c) {
    return (unsigned)(c->err != property_check_sample.err) << 0;
}
