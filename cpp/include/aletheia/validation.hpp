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
