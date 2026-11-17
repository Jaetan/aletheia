//go:build !cgo || !linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// checkFormula and ParseTimeBound need cgo on linux to reach the kernel's
// property parse. Without cgo they fail with an FFI error, as FromDecimal in
// decimal_nocgo.go does, so the package still compiles with CGO_ENABLED=0.
func checkFormula(_ Formula) error {
	return ffiError("building a check requires cgo on linux; build with CGO_ENABLED=1")
}

// ParseTimeBound fails with an FFI error without cgo on linux.
func ParseTimeBound(_ string) (TimeBound, error) {
	return TimeBound{}, ffiError("reading a time bound requires cgo on linux; build with CGO_ENABLED=1")
}
