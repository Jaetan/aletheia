//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Decimal text to an exact [Rational] through the kernel's own parser
// (aletheia_parse_decimal), which is what the Python, C++ and Rust bindings
// use too, so the four agree byte for byte and no binding carries a float64
// on this path. Like the rational renderer this file is a consumer of the GHC
// runtime, not its owner: it loads the library and its two symbols on first
// use and never initialises the runtime, which an FFIBackend does with the
// bus count it was given.

package aletheia

/*
#cgo LDFLAGS: -ldl

#include <dlfcn.h>
#include <stdlib.h>

static char* decimal_call_parse(void *fn, const char *s) {
    return ((char* (*)(const char*))fn)(s);
}
// The renderer's file carries the same three lines: a cgo preamble is visible
// to its own file alone, so the two consumers of the shared free function each
// declare their way of calling it.
static void decimal_call_free_str(void *fn, char *ptr) {
    ((void (*)(char*))fn)(ptr);
}
*/
import "C"

import (
	"runtime"
	"sync"
	"unsafe"
)

var (
	decimalInitOnce sync.Once
	decimalInitErr  error
	decimalParseFn  unsafe.Pointer
	decimalFreeFn   unsafe.Pointer
)

// loadDecimalFFI resolves the parse and free symbols through the loader the
// renderer's file carries; it does not initialise the runtime.
func loadDecimalFFI() error {
	syms, err := loadStandaloneSymbols("decimal", "aletheia_parse_decimal", "aletheia_free_str")
	if err != nil {
		return err
	}
	decimalParseFn, decimalFreeFn = syms[0], syms[1]
	return nil
}

func ensureDecimalLoaded() error {
	decimalInitOnce.Do(func() {
		decimalInitErr = loadDecimalFFI()
	})
	return decimalInitErr
}

// FromDecimal parses a decimal literal into an exact [Rational] through the
// kernel: "0.1" is 1/10, "3.14" is 157/50, "42" is 42/1. The grammar is the
// kernel's, an optional minus, digits, and optionally a point followed by
// digits; no plus sign, no leading or trailing point, no exponent, so "1e3",
// ".5", "1." and "+2" are refused.
//
// The call needs a live GHC runtime, which an FFIBackend (through a [Client])
// starts; without one it fails before reaching the FFI rather than starting
// the runtime with a default bus count.
//
// Errors: [ErrValidation] for a literal the kernel refuses or a rational past
// int64 (the kernel's decimal_parse_failed and decimal_overflow); [ErrFFI]
// when the runtime is down or the library or symbol is missing; [ErrProtocol]
// on a null return or a malformed response, which no working kernel produces.
func FromDecimal(s string) (Rational, error) {
	if err := ensureDecimalLoaded(); err != nil {
		return Rational{}, err
	}
	if !hsInitialized() {
		return Rational{}, ffiError("GHC runtime not initialized: create a Client (FFIBackend) before parsing decimals")
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	cStr := C.CString(s)
	defer C.free(unsafe.Pointer(cStr))
	raw := C.decimal_call_parse(decimalParseFn, cStr)
	if raw == nil {
		return Rational{}, protocolError("aletheia_parse_decimal returned a null pointer")
	}
	defer C.decimal_call_free_str(decimalFreeFn, raw)
	return decodeDecimalResponse(C.GoString(raw))
}

// decodeDecimalResponse reads the parser's envelope: a bare numerator and
// denominator object on success, a status error envelope on failure. The
// status is read first, so the kernel's reason reaches the caller as a
// validation error instead of the rational decoder's missing-field one.
func decodeDecimalResponse(raw string) (Rational, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return Rational{}, err
	}
	if getString(m, "status") == "error" {
		msg := getString(m, "message")
		if msg == "" {
			msg = "invalid decimal literal"
		}
		return Rational{}, NewValidationError(msg)
	}
	return parseRational(m)
}
