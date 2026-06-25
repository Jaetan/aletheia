// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// Test-only re-exports of the enrichment helper functions, which are private in
// production (matching the Rust and Python bindings — the public surface is the
// PropertyDiagnostic type, not these constructors). Go does not compile
// `_test.go` files into the production build, so these do not re-expose the
// functions publicly; they only let the external (aletheia_test) tests keep
// calling them unchanged.
//
// FormatFormula / BuildDiagnostic panic on a renderer error rather than return
// it: the tests run with the GHC runtime up (see TestMain in main_test.go), so
// the error never fires here; a panic would mean a broken test setup, surfaced
// loudly.

// FormatFormula re-exports the internal formatFormula for tests.
func FormatFormula(f Formula) string {
	s, err := formatFormula(f)
	if err != nil {
		panic(err)
	}
	return s
}

// BuildDiagnostic re-exports the internal buildDiagnostic for tests.
func BuildDiagnostic(f Formula) PropertyDiagnostic {
	d, err := buildDiagnostic(f)
	if err != nil {
		panic(err)
	}
	return d
}

// CollectSignals re-exports the internal collectSignals for tests (infallible —
// no FFI — so a plain alias suffices).
var CollectSignals = collectSignals
