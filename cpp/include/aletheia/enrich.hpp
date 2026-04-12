// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// enrich.hpp surfaces LtlFormula, Predicate variants, and PropertyDiagnostic
// to callers; those vocabulary types live in ltl.hpp and response.hpp.
#include <aletheia/ltl.hpp>      // IWYU pragma: export
#include <aletheia/response.hpp> // IWYU pragma: export

#include <string>
#include <vector>

namespace aletheia {

// Format a formula as a human-readable string.
// Always succeeds — every formula has a representation.
auto format_formula(const LtlFormula& f) -> std::string;

// Collect all signal names referenced in a formula, deduplicated, in order.
auto collect_signals(const LtlFormula& f) -> std::vector<SignalName>;

// Build a diagnostic from a formula. Always succeeds.
auto build_diagnostic(const LtlFormula& f) -> PropertyDiagnostic;

} // namespace aletheia
