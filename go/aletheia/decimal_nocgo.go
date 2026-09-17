//go:build !cgo || !linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// FromDecimal needs cgo on linux to reach the kernel's decimal parser, the
// one source of decimal-to-rational for every binding. Without cgo it fails
// with an FFI error, as formatRationalFFI in ffi_nocgo.go does, so the
// package still compiles with CGO_ENABLED=0.
func FromDecimal(_ string) (Rational, error) {
	return Rational{}, ffiError("FromDecimal requires cgo on linux; build with CGO_ENABLED=1")
}
