// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Validation-issue vocabulary (severity / code / issue), split out of
// validation.hpp so error.hpp can carry issues on a typed error without
// pulling the DBC definition headers into every error-consuming TU.
#pragma once

#include <string>
#include <string_view>

namespace aletheia {

enum class IssueSeverity { Error, Warning };

enum class IssueCode {
    DuplicateMessageId,
    DuplicateMessageName,
    DuplicateSignalName,
    FactorZero,
    MultiplexorNotFound,
    MultiplexorCycle,
    GlobalNameCollision,
    MinExceedsMax,
    SignalExceedsDlc,
    SignalOverlap,
    BitLengthZero,
    OffsetScaleRange,
    EmptyMessage,
    StartBitOutOfRange,
    BitLengthExcessive,
    MultiplexorNonUnitScaling,
    DuplicateAttributeName,
    UnknownCommentTarget,
    UnknownMessageSender,
    UnknownSignalReceiver,
    UnknownValueDescriptionTarget,
    // Text-round-trip checker diagnostics, attached to formatDBCText's result
    // or refusal. The two multiplexing codes are also emitted, warning-class,
    // by the structural validator (validateDBC and the DBC-loading routes),
    // which reuses the same kernel deciders.
    TextRoundtripDivergence,
    MultiValueMuxSelector,
    MuxMasterIncoherent,
    UnknownAttributeName,
    AttributeValueTypeMismatch,
    AttributeEnumEmpty,
    AttributeEnumDefaultUnstable,
    // Structural-validation errors, after the round-trip codes in the order
    // the kernel declares its codes.
    RangeExceedsBits,
    ValueDescriptionKeyOutOfRange,
};

// A reply holding a severity or a code outside these enums is refused.
struct ValidationIssue {
    IssueSeverity severity;
    IssueCode code;
    std::string detail;
};

// Render an issue severity / code to its canonical wire string
// ("error"/"warning"; "offset_scale_range"; …) — the inverse of the JSON
// parser's string→enum mapping. Used by the CLI's `validate` output and any
// caller presenting validation issues; returns "unknown" for a value no
// enumerator names.
[[nodiscard]] auto to_string(IssueSeverity severity) -> std::string_view;
[[nodiscard]] auto to_string(IssueCode code) -> std::string_view;

} // namespace aletheia
