// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/validation_issue.hpp> // IWYU pragma: export

#include <vector>

namespace aletheia {

struct ValidationResult {
    bool has_errors;
    std::vector<ValidationIssue> issues;
};

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
