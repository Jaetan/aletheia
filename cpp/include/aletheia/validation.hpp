// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/dbc.hpp>
#include <aletheia/validation_issue.hpp> // IWYU pragma: export

#include <string>
#include <vector>

namespace aletheia {

struct ValidationResult {
    bool has_errors;
    std::vector<ValidationIssue> issues;
};

// ParsedDBC bundles the parsed body and any non-error issues (warnings)
// returned by parse_dbc / parse_dbc_text.  Errors short-circuit to the
// Result<>::error() path; this struct is only constructed when the parse +
// structural validation pass has zero error-severity issues.
struct ParsedDBC {
    DbcDefinition dbc;
    std::vector<ValidationIssue> warnings;
};

// DbcText bundles the .dbc text image produced by format_dbc_text with its
// wfTextIssues diagnostics, which are warning-severity and advisory, so
// `issues` may be non-empty on a proven round-trip.  When this struct is
// produced at all, and what is returned when it is not, is the contract
// stated on format_dbc_text in client.hpp.
struct DbcText {
    std::string text;
    std::vector<ValidationIssue> issues;
};

} // namespace aletheia
