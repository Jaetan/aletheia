//go:build cgo && linux

// Package-level lazy-load + FFI dispatch for the cross-binding-identical
// Rational pretty-printer (R20 cluster Y stage 2).
//
// Single source of truth: every render flows through
// `aletheia_format_rational` in libaletheia-ffi.so.  The library is
// dlopened on first use via sync.Once — independently of `FFIBackend`,
// so tests that never instantiate a backend (e.g. `enrich_test.go`)
// still route through the same Agda kernel function.  No local Go
// fallback exists; `formatRational(r)` is byte-identical to Python's
// and C++'s output by construction, not by a test corpus.

package aletheia

/*
#cgo LDFLAGS: -ldl

#include <dlfcn.h>
#include <stdint.h>
#include <stdlib.h>

// Cgo trampolines local to this file.
static void renderer_call_hs_init(void *fn) {
    ((void (*)(int*, char***))fn)(NULL, NULL);
}
static char* renderer_call_format_rational(void *fn, int64_t num, int64_t denom) {
    return ((char* (*)(int64_t, int64_t))fn)(num, denom);
}
static void renderer_call_free_str(void *fn, char *ptr) {
    ((void (*)(char*))fn)(ptr);
}
*/
import "C"

import (
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"sync"
	"unsafe"
)

var (
	rendererInitOnce sync.Once
	rendererInitErr  error
	rendererFormatFn unsafe.Pointer
	rendererFreeFn   unsafe.Pointer
)

// findFFILibrary locates libaletheia-ffi.so for the renderer's
// lazy-load path.  Mirrors the search strategy in
// `python/aletheia/client/_ffi.py::find_ffi_library` and the test-side
// `findFFILib` in `ffi_backend_test.go`.  Returns the empty string when
// no candidate exists.
func findFFILibrary() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	candidates := []string{
		"../../build/libaletheia-ffi.so",
		"../build/libaletheia-ffi.so",
		"build/libaletheia-ffi.so",
	}
	for _, c := range candidates {
		abs, err := filepath.Abs(c)
		if err != nil {
			continue
		}
		if _, err := os.Stat(abs); err == nil {
			return abs
		}
	}
	return ""
}

// loadRendererFFI dlopens libaletheia-ffi.so and resolves the format /
// free symbols.  Coordinates the GHC RTS handshake with FFIBackend via
// the package-shared `hsInitMu` / `hsInitDone` so a concurrent
// NewFFIBackend cannot race a second hs_init call.
func loadRendererFFI() error {
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
		return ffiError("renderer dlopen failed: " + C.GoString(C.dlerror()))
	}

	hsInit, err := rendererDlsym(handle, "hs_init")
	if err != nil {
		return err
	}
	fmtFn, err := rendererDlsym(handle, "aletheia_format_rational")
	if err != nil {
		return err
	}
	freeFn, err := rendererDlsym(handle, "aletheia_free_str")
	if err != nil {
		return err
	}

	// Initialize the GHC RTS exactly once per process.  Coordinates with
	// FFIBackend via the shared `hsInitMu` / `hsInitDone`: whoever runs
	// first wins; the loser observes `hsInitDone == true` and skips.
	hsInitMu.Lock()
	if !hsInitDone {
		C.renderer_call_hs_init(hsInit)
		hsInitCores = 1
		hsInitDone = true
	}
	hsInitMu.Unlock()

	rendererFormatFn = fmtFn
	rendererFreeFn = freeFn
	return nil
}

// rendererDlsym wraps dlsym + dlerror with a structured error.  Local
// to this file rather than reusing `loadSym` from `ffi.go` because that
// helper assumes the caller has already pinned the OS thread; here we
// pin in `loadRendererFFI` so callers don't have to.
func rendererDlsym(handle unsafe.Pointer, name string) (unsafe.Pointer, error) {
	cName := C.CString(name)
	defer C.free(unsafe.Pointer(cName))
	C.dlerror() // clear previous errors
	sym := C.dlsym(handle, cName)
	if e := C.dlerror(); e != nil {
		return nil, ffiError("renderer dlsym " + name + ": " + C.GoString(e))
	}
	return sym, nil
}

func ensureRendererLoaded() error {
	rendererInitOnce.Do(func() {
		rendererInitErr = loadRendererFFI()
	})
	return rendererInitErr
}

// formatRationalFFI renders a Rational via the Agda kernel.
// Initializes the FFI on first call.  Panics if the library cannot be
// loaded — `formatRational` is invoked from display paths (not the
// streaming hot path) and the .so is required for the package to
// function; surfacing the failure as a panic keeps the call signature
// pure (no error return) while turning a missing-library state into a
// loud failure rather than a silent fallback.
func formatRationalFFI(num, denom int64) string {
	if err := ensureRendererLoaded(); err != nil {
		panic(fmt.Sprintf("aletheia: formatRational requires libaletheia-ffi.so: %v", err))
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	raw := C.renderer_call_format_rational(rendererFormatFn, C.int64_t(num), C.int64_t(denom))
	if raw == nil {
		// Defensive: the Agda function always returns a non-null
		// CString (denom = 0 returns the literal "0").  Reach here
		// only on a catastrophic Haskell-side allocation failure.
		return "0"
	}
	defer C.renderer_call_free_str(rendererFreeFn, raw)
	return C.GoString(raw)
}
