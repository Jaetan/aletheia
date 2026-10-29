// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// enrich.hpp surfaces LtlFormula, Predicate variants, and PropertyDiagnostic
// to callers; those vocabulary types live in ltl.hpp and response.hpp.
#include <aletheia/error.hpp>
#include <aletheia/ltl.hpp>      // IWYU pragma: export
#include <aletheia/response.hpp> // IWYU pragma: export

#include <string>
#include <vector>

namespace aletheia {

// Format a formula as a human-readable string.  Predicate thresholds render
// through the kernel's `aletheia_format_rational` (cross-binding SSOT), so
// this needs the GHC runtime started and answers an error of kind Ffi while
// it is down.
[[nodiscard]] auto format_formula(LtlFormula const& f) -> Result<std::string>;

// Collect all signal names referenced in a formula, deduplicated, in order.
[[nodiscard]] auto collect_signals(LtlFormula const& f) -> std::vector<SignalName>;

// Build a diagnostic from a formula: its signals and format_formula's text,
// or format_formula's error.
[[nodiscard]] auto build_diagnostic(LtlFormula const& f) -> Result<PropertyDiagnostic>;

} // namespace aletheia
