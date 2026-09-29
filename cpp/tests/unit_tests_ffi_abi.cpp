// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The backend's mirror of the kernel's structures (src/detail/ffi_abi.hpp)
// lays out as the kernel's own header does: same size, alignment and offset
// for every field, and the ABI version is the header's. A field moved on either side stops this
// file compiling instead of misreading across the ABI.

#include "aletheia.h"
#include "detail/ffi_abi.hpp"

#include <cstddef>

namespace {

using aletheia::detail::abi_version;
using aletheia::detail::FfiBuffer;
using aletheia::detail::FfiDecimal;
using aletheia::detail::FfiFrame;
using aletheia::detail::FfiRational;
using aletheia::detail::FfiSignalValues;
using aletheia::detail::FfiText;

static_assert(abi_version == ALETHEIA_ABI_VERSION);

static_assert(sizeof(FfiText) == sizeof(aletheia_text));
static_assert(alignof(FfiText) == alignof(aletheia_text));
static_assert(offsetof(FfiText, data) == offsetof(aletheia_text, data));
static_assert(offsetof(FfiText, size) == offsetof(aletheia_text, size));

static_assert(sizeof(FfiFrame) == sizeof(aletheia_frame));
static_assert(alignof(FfiFrame) == alignof(aletheia_frame));
static_assert(offsetof(FfiFrame, timestamp) == offsetof(aletheia_frame, timestamp));
static_assert(offsetof(FfiFrame, data) == offsetof(aletheia_frame, data));
static_assert(offsetof(FfiFrame, can_id) == offsetof(aletheia_frame, can_id));
static_assert(offsetof(FfiFrame, extended) == offsetof(aletheia_frame, extended));
static_assert(offsetof(FfiFrame, dlc) == offsetof(aletheia_frame, dlc));
static_assert(offsetof(FfiFrame, data_len) == offsetof(aletheia_frame, data_len));
static_assert(offsetof(FfiFrame, brs_present) == offsetof(aletheia_frame, brs_present));
static_assert(offsetof(FfiFrame, brs_value) == offsetof(aletheia_frame, brs_value));
static_assert(offsetof(FfiFrame, esi_present) == offsetof(aletheia_frame, esi_present));
static_assert(offsetof(FfiFrame, esi_value) == offsetof(aletheia_frame, esi_value));

static_assert(sizeof(FfiSignalValues) == sizeof(aletheia_signal_values));
static_assert(alignof(FfiSignalValues) == alignof(aletheia_signal_values));
static_assert(offsetof(FfiSignalValues, indices) == offsetof(aletheia_signal_values, indices));
static_assert(offsetof(FfiSignalValues, numerators) ==
              offsetof(aletheia_signal_values, numerators));
static_assert(offsetof(FfiSignalValues, denominators) ==
              offsetof(aletheia_signal_values, denominators));
static_assert(offsetof(FfiSignalValues, count) == offsetof(aletheia_signal_values, count));

static_assert(sizeof(FfiBuffer) == sizeof(aletheia_buffer));
static_assert(alignof(FfiBuffer) == alignof(aletheia_buffer));
static_assert(offsetof(FfiBuffer, data) == offsetof(aletheia_buffer, data));
static_assert(offsetof(FfiBuffer, err) == offsetof(aletheia_buffer, err));
static_assert(offsetof(FfiBuffer, size) == offsetof(aletheia_buffer, size));

static_assert(sizeof(FfiRational) == sizeof(aletheia_rational));
static_assert(alignof(FfiRational) == alignof(aletheia_rational));
static_assert(offsetof(FfiRational, numerator) == offsetof(aletheia_rational, numerator));
static_assert(offsetof(FfiRational, denominator) == offsetof(aletheia_rational, denominator));

static_assert(sizeof(FfiDecimal) == sizeof(aletheia_decimal));
static_assert(alignof(FfiDecimal) == alignof(aletheia_decimal));
static_assert(offsetof(FfiDecimal, value) == offsetof(aletheia_decimal, value));
static_assert(offsetof(FfiDecimal, err) == offsetof(aletheia_decimal, err));

} // namespace
