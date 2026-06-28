//go:build !cgo || !linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// FromDecimal requires cgo on linux. This stub exists so the package compiles
// with CGO_ENABLED=0; decimal→rational parsing delegates to the Agda kernel
// (the cross-binding decimal SSOT), which is unreachable without cgo. Mirrors
// the error stance of formatRationalFFI in ffi_nocgo.go. Use MockBackend for
// non-cgo unit tests; the FromDecimal path is not supported in !cgo builds.
func FromDecimal(_ string) (Rational, error) {
	return Rational{}, ffiError("FromDecimal requires cgo on linux; build with CGO_ENABLED=1")
}
