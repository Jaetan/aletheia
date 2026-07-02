// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// enrich.hpp surfaces LtlFormula, Predicate variants, and PropertyDiagnostic
// to callers; those vocabulary types live in ltl.hpp and response.hpp.
#include <aletheia/ltl.hpp>      // IWYU pragma: export
#include <aletheia/response.hpp> // IWYU pragma: export

#include <string>
#include <vector>

namespace aletheia {

// Format a formula as a human-readable string.  Predicate thresholds render
// through the kernel's `aletheia_format_rational` (cross-binding SSOT), so
// this needs a live FfiBackend/GHC RTS and throws `AletheiaException(Ffi)`
// when the library or runtime is unavailable.
auto format_formula(const LtlFormula& f) -> std::string;

// Collect all signal names referenced in a formula, deduplicated, in order.
auto collect_signals(const LtlFormula& f) -> std::vector<SignalName>;

// Build a diagnostic from a formula.  Renders predicate thresholds via the
// kernel's `aletheia_format_rational` (through format_formula), so it needs a
// live FfiBackend/GHC RTS and throws `AletheiaException(Ffi)` when the
// library or runtime is unavailable.
auto build_diagnostic(const LtlFormula& f) -> PropertyDiagnostic;

} // namespace aletheia
