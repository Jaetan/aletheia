// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The structures the kernel's entries take by pointer, mirrored from
// haskell-shim/include/aletheia.h (the Go module does not ship that header).
// Every cgo preamble of the package that crosses one includes this file, and
// TestFFIStructuresMatchKernelHeader holds each layout to the header's.
#ifndef ALETHEIA_GO_ABI_H
#define ALETHEIA_GO_ABI_H

#include <stddef.h>
#include <stdint.h>

struct aletheia_text {
    const char *data;
    size_t size;
};

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

struct aletheia_signal_values {
    const uint32_t *indices;
    const int64_t *numerators;
    const int64_t *denominators;
    uint32_t count;
};

struct aletheia_buffer {
    uint8_t *data;
    char *err;
    uint32_t size;
};

struct aletheia_rational {
    int64_t numerator;
    int64_t denominator;
};

struct aletheia_decimal {
    struct aletheia_rational value;
    char *err;
};

#endif
