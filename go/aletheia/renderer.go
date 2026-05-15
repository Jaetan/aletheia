//go:build cgo && linux

// Package-level registration for the cross-binding-identical Rational
// pretty-printer (R20 cluster Y stage 2).
//
// Production code paths flow through `NewFFIBackend`, which registers
// the loaded library's `aletheia_format_rational` and `aletheia_free_str`
// function pointers via `setRendererFns`.  The free-function
// `formatRational` (in `enrich.go`) consults these globals on every
// call: when registered, the FFI is used; otherwise it falls back to
// the local Go algorithm — same byte output, but kept in lockstep by
// the test corpus rather than by the kernel.  The fallback path keeps
// tests that don't instantiate an `FFIBackend` (e.g. `enrich_test.go`)
// usable.

package aletheia

/*
#include <stdint.h>

// Cgo trampolines local to this file.  Cgo scopes the inline C block to
// the .go file in which it appears, so even though `ffi.go` already
// declares analogous trampolines, the renderer needs its own copies for
// `tryFormatRationalFFI` to reach the FFI symbols.
static char* renderer_call_format_rational(void *fn, int64_t num, int64_t denom) {
    return ((char* (*)(int64_t, int64_t))fn)(num, denom);
}
static void renderer_call_free_str(void *fn, char *ptr) {
    ((void (*)(char*))fn)(ptr);
}
*/
import "C"

import (
	"sync"
	"unsafe"
)

// rendererState holds the package-level FFI fn pointers + mutex.
// `formatRationalFn` is `aletheia_format_rational`; `freeStrFn` is
// `aletheia_free_str` (shared with other CString-returning calls).
var (
	rendererMu       sync.RWMutex
	rendererFormatFn unsafe.Pointer
	rendererFreeFn   unsafe.Pointer
)

// setRendererFns registers FFI function pointers for the Rational
// pretty-printer.  Called by `NewFFIBackend` after symbol loading.
// Subsequent calls overwrite (the same `.so` is loaded once per
// process, so all backend instances share the same fn addresses).
func setRendererFns(formatFn, freeStrFn unsafe.Pointer) {
	rendererMu.Lock()
	defer rendererMu.Unlock()
	rendererFormatFn = formatFn
	rendererFreeFn = freeStrFn
}

// tryFormatRationalFFI returns the FFI-rendered string and `true`
// when the renderer is registered (i.e. an `FFIBackend` exists in
// this process), otherwise `("", false)` so the caller can fall
// back to the local Go algorithm.
func tryFormatRationalFFI(num, denom int64) (string, bool) {
	rendererMu.RLock()
	fmtFn := rendererFormatFn
	freeFn := rendererFreeFn
	rendererMu.RUnlock()
	if fmtFn == nil {
		return "", false
	}
	raw := C.renderer_call_format_rational(fmtFn, C.int64_t(num), C.int64_t(denom))
	if raw == nil {
		// Defensive: the Agda function always returns a non-null
		// CString (denom = 0 returns the literal "0").  Reach here
		// only on a catastrophic Haskell-side allocation failure.
		return "0", true
	}
	defer C.renderer_call_free_str(freeFn, raw)
	return C.GoString(raw), true
}
