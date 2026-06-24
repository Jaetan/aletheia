// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <string>
#include <string_view>
#include <vector>

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
    Unknown
};

struct ValidationIssue {
    IssueSeverity severity;
    IssueCode code;
    // The verbatim wire code string. Preserved so an unrecognized code
    // (code == IssueCode::Unknown, e.g. a future core code) round-trips rather
    // than collapsing to the literal "unknown" — mirrors Go's string-typed
    // IssueCode, Rust's IssueCode::Unknown(String), and Python's passthrough.
    // For a known code it equals to_string(code).
    std::string code_raw;
    std::string detail;
};

struct ValidationResult {
    bool has_errors;
    std::vector<ValidationIssue> issues;
};

// Render an issue severity / code to its canonical wire string
// ("error"/"warning"; "offset_scale_range"; …) — the inverse of the JSON
// parser's string→enum mapping. Used by the CLI's `validate` output and any
// caller presenting validation issues; returns "unknown" for
// IssueCode::Unknown.
[[nodiscard]] auto to_string(IssueSeverity severity) -> std::string_view;
[[nodiscard]] auto to_string(IssueCode code) -> std::string_view;

// Render an issue's code for display, preserving the original wire string for an
// unrecognized code: returns `code_raw` when `code == IssueCode::Unknown` (so a
// future core code round-trips), else the canonical `to_string(code)` spelling.
// Use this rather than `to_string(issue.code)` at presentation boundaries.
[[nodiscard]] auto issue_code_label(const ValidationIssue& issue) -> std::string_view;

} // namespace aletheia

#include <aletheia/dbc.hpp>

namespace aletheia {

// ParsedDBC bundles the parsed body and any non-error issues (warnings)
// returned by parse_dbc / parse_dbc_text.  Errors short-circuit to the
// Result<>::error() path; this struct is only constructed when the parse +
// structural validation pass has zero error-severity issues.
struct ParsedDBC {
    DbcDefinition dbc;
    std::vector<ValidationIssue> warnings;
};

} // namespace aletheia
