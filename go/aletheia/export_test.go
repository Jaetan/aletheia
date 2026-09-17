// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The enrichment helpers are private, as they are in the Rust binding
// (build_diagnostic) and the Python one (the _enrichment module), whose
// public surface is the diagnostic itself. These re-exports let the tests
// outside the package call them, and since Go leaves a _test.go file out of
// the production build, nothing here reaches a consumer.
//
// The two that can fail panic rather than return the error: the tests run
// with the GHC runtime up, which TestMain brings up, so a renderer error here
// is a broken setup and should be loud.

// FormatFormula is formatFormula for the tests.
func FormatFormula(f Formula) string {
	s, err := formatFormula(f)
	if err != nil {
		panic(err)
	}
	return s
}

// BuildDiagnostic is buildDiagnostic for the tests.
func BuildDiagnostic(f Formula) PropertyDiagnostic {
	d, err := buildDiagnostic(f)
	if err != nil {
		panic(err)
	}
	return d
}

// CollectSignals is collectSignals for the tests; it cannot fail.
var CollectSignals = collectSignals

// FindFFILibrary is findFFILibrary for the tests, which looked for the library
// their own way before this: the same environment variable and the same
// candidates, minus the registered path, which is the one difference a copy
// cannot help having.
var FindFFILibrary = findFFILibrary

// FormatEnrichedReason is formatEnrichedReason for the tests; it cannot fail.
var FormatEnrichedReason = formatEnrichedReason
