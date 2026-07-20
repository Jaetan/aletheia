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
    // Text-round-trip checker diagnostics (formatDBCText / round-trip refusal).
    // validateDBC and the DBC-loading routes mirror MultiValueMuxSelector and
    // MuxMasterIncoherent warning-class, via the same kernel deciders.
    TextRoundtripDivergence,
    MultiValueMuxSelector,
    MuxMasterIncoherent,
    UnknownAttributeName,
    AttributeValueTypeMismatch,
    AttributeEnumEmpty,
    AttributeEnumDefaultUnstable,
    Unknown
};

struct ValidationIssue {
    IssueSeverity severity;
    IssueCode code;
    // The verbatim wire code string. Preserved so an unrecognized code
    // (code == IssueCode::Unknown, e.g. a future core code) round-trips rather
    // than collapsing to the literal "unknown" — mirrors Go's string-typed
    // IssueCode, Rust's IssueCode::Unknown(String), and Python's passthrough.
    // The JSON decoders populate this from the wire; for a decoder-produced
    // issue with a known code it equals to_string(code). A manually constructed
    // ValidationIssue may leave it empty.
    std::string code_raw;
    std::string detail;
};

// Render an issue severity / code to its canonical wire string
// ("error"/"warning"; "offset_scale_range"; …) — the inverse of the JSON
// parser's string→enum mapping. Used by the CLI's `validate` output and any
// caller presenting validation issues; returns "unknown" for
// IssueCode::Unknown.
[[nodiscard]] auto to_string(IssueSeverity severity) -> std::string_view;
[[nodiscard]] auto to_string(IssueCode code) -> std::string_view;

// Render an issue's code for display, preserving the original wire string for an
// unrecognized code: returns `code_raw` when `code == IssueCode::Unknown` and
// `code_raw` is non-empty (so a future core code round-trips), otherwise the
// canonical `to_string(code)` spelling (which is "unknown" for an Unknown code
// with no recorded wire string). Use this rather than `to_string(issue.code)`
// at presentation boundaries.
[[nodiscard]] auto issue_code_label(const ValidationIssue& issue) -> std::string_view;

} // namespace aletheia
