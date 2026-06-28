//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Decimal-string → exact [Rational] via the verified Agda kernel
// (`aletheia_parse_decimal`), the cross-binding single source of truth for the
// float principle: a decimal is an exact rational, never a float64.  Like the
// rational renderer (renderer.go) this is a *consumer* of the GHC RTS — it
// dlopens the library and resolves its symbol on first use but never
// initialises the runtime (an FFIBackend owns that, with its bus-count -N).  If
// the runtime is down [FromDecimal] is vocal: it returns an error rather than
// self-initialising (self-init would latch a default -N and squander the
// backend's).  No local Go fallback exists — the kernel parse is byte-identical
// to Python's, C++'s, and Rust's by construction.

package aletheia

/*
#cgo LDFLAGS: -ldl

#include <dlfcn.h>
#include <stdlib.h>

// Cgo trampolines local to this file.
static char* decimal_call_parse(void *fn, const char *s) {
    return ((char* (*)(const char*))fn)(s);
}
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

// loadDecimalFFI dlopens libaletheia-ffi.so and resolves the parse-decimal /
// free symbols.  It does NOT initialise the GHC RTS: like the renderer, the
// decimal parser is a consumer of a runtime that an FFIBackend must bring up
// (see [FromDecimal]), so it only loads the symbols it calls.  Reuses
// findFFILibrary / rendererDlsym from renderer.go (same build tag, same
// search-path contract).
func loadDecimalFFI() error {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	libPath := findFFILibrary()
	if libPath == "" {
		return ffiError("libaletheia-ffi.so not found; build with: cabal run shake -- build")
	}

	cPath := C.CString(libPath)
	defer C.free(unsafe.Pointer(cPath))
	handle := C.dlopen(cPath, C.RTLD_NOW|C.RTLD_LOCAL)
	if handle == nil {
		return ffiError("decimal dlopen failed: " + C.GoString(C.dlerror()))
	}

	parseFn, err := rendererDlsym(handle, "aletheia_parse_decimal")
	if err != nil {
		return err
	}
	freeFn, err := rendererDlsym(handle, "aletheia_free_str")
	if err != nil {
		return err
	}

	decimalParseFn = parseFn
	decimalFreeFn = freeFn
	return nil
}

func ensureDecimalLoaded() error {
	decimalInitOnce.Do(func() {
		decimalInitErr = loadDecimalFFI()
	})
	return decimalInitErr
}

// FromDecimal parses a decimal string into an exact [Rational] via the verified
// Agda kernel (`aletheia_parse_decimal`) — the cross-binding single source of
// truth for decimal→rational (the float principle: a decimal is an exact
// rational, never a float64).  "0.1" → 1/10, "3.14" → 157/50, "42" → 42/1.  The
// accepted grammar is the kernel's: -?digits or -?digits.digits+ — no '+' sign,
// no leading/trailing '.', no exponent (so "1e3", ".5", "1.", "+2" are
// rejected).
//
// Like the rational renderer, decimal parsing is RTS-gated and vocal: it never
// initialises the GHC RTS (an FFIBackend, via a [Client], is the sole
// initialiser, owning the bus-count -N), so it returns an error BEFORE the FFI
// call if the runtime is down.
//
// Errors: a validation error ([ErrValidation]) when the string is not a valid
// decimal literal or its rational overflows int64 (the kernel's
// decimal_parse_failed / decimal_overflow — user input, not a wire fault); an
// FFI error ([ErrFFI]) if the runtime is down or the .so / symbol is
// unavailable; a protocol error ([ErrProtocol]) on a null return or malformed
// response (an ABI / kernel malfunction).
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
		// Unreachable for a well-formed call (the kernel returns an error
		// envelope, never null); a null means a kernel / ABI malfunction, so
		// surface it rather than a fabricated value. Matches the renderer's
		// null handling and the Rust binding's.
		return Rational{}, protocolError("aletheia_parse_decimal returned a null pointer")
	}
	defer C.decimal_call_free_str(decimalFreeFn, raw)
	return decodeDecimalResponse(C.GoString(raw))
}

// decodeDecimalResponse decodes the aletheia_parse_decimal wire envelope: a bare
// {"numerator","denominator"} object on success, or a {"status":"error",...}
// envelope on failure.  The status branch is checked BEFORE handing the value to
// the wire decoder — otherwise parseRational would report an opaque "missing
// numerator" and mask the precise decimal_parse_failed / decimal_overflow
// reason.  A failure maps to a validation error (user input, not a wire fault);
// success reuses the shared wire decoder parseRational (UseNumber-exact via
// parseResponse — no reimplemented denominator check).
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
