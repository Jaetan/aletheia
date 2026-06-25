//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Package-level lazy-load + FFI dispatch for the cross-binding-identical
// Rational pretty-printer (R20 cluster Y stage 2).
//
// Single source of truth: every render flows through
// `aletheia_format_rational` in libaletheia-ffi.so.  The renderer dlopens
// the library and resolves its symbols on first use, but does NOT
// initialise the GHC RTS — that is an FFIBackend's job.  If the runtime is
// not yet up the renderer returns an error rather than self-initialising
// (which would squander the backend's bus-count -N; the RTS is one-shot per
// process).  No local Go fallback exists; `formatRational(r)` is
// byte-identical to Python's and C++'s output by construction.

package aletheia

/*
#cgo LDFLAGS: -ldl

#include <dlfcn.h>
#include <stdint.h>
#include <stdlib.h>

// Cgo trampolines local to this file.
static char* renderer_call_format_rational(void *fn, int64_t num, int64_t denom) {
    return ((char* (*)(int64_t, int64_t))fn)(num, denom);
}
static void renderer_call_free_str(void *fn, char *ptr) {
    ((void (*)(char*))fn)(ptr);
}
*/
import "C"

import (
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

	// R21 cluster 2: package-static preferred library path, registered
	// by NewFFIBackend before any Check builder triggers
	// formatRationalFFI.  First-write-wins (sync.Once around
	// rendererInitOnce means subsequent registrations after the renderer
	// has loaded are no-ops; the renderer's state is pinned).  Pre-load
	// registrations win over the relative-path heuristic; ALETHEIA_LIB
	// env var still wins over both.  Closes R21 GO-S-17.2 / mirror of
	// CPP-SYS-17.1.
	defaultLibPathMu sync.Mutex
	defaultLibPath   string
)

// RegisterDefaultLibPath records a preferred libaletheia-ffi.so path
// for the lazy-loaded renderer.  Called automatically by NewFFIBackend
// so the renderer (which loads independently of the backend) consults
// the same .so the user asked for, instead of falling back to its
// relative-path heuristic.  First-write-wins: subsequent registrations
// after the renderer has loaded are no-ops.
func RegisterDefaultLibPath(libPath string) {
	defaultLibPathMu.Lock()
	defer defaultLibPathMu.Unlock()
	if defaultLibPath == "" { // first-write-wins
		defaultLibPath = libPath
	}
}

// findFFILibrary locates libaletheia-ffi.so for the renderer's
// lazy-load path.  Search order:
//
//  1. ALETHEIA_LIB env var (operator override)
//  2. Path registered via RegisterDefaultLibPath (the .so the user
//     passed to NewFFIBackend)
//  3. Relative-path heuristic (ctest from cpp/build, go from go/)
//
// Returns the empty string when no candidate exists.
func findFFILibrary() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	defaultLibPathMu.Lock()
	registered := defaultLibPath
	defaultLibPathMu.Unlock()
	if registered != "" {
		if _, err := os.Stat(registered); err == nil {
			return registered
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
// free symbols.  It does NOT initialise the GHC RTS: the renderer is a
// consumer of a runtime that an FFIBackend must bring up (see
// formatRationalFFI), so it only loads the symbols it calls.
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

	fmtFn, err := rendererDlsym(handle, "aletheia_format_rational")
	if err != nil {
		return err
	}
	freeFn, err := rendererDlsym(handle, "aletheia_free_str")
	if err != nil {
		return err
	}

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

// formatRationalFFI renders a Rational via the Agda kernel.  It resolves
// the renderer symbols on first call but does NOT initialise the GHC RTS:
// the renderer is a consumer of a runtime that an FFIBackend must bring up.
// If the runtime is not initialised it returns an error ("be vocal") rather
// than self-initialising — self-initialising would latch a default -N and
// squander the FFIBackend's bus-count -N (the RTS is one-shot per process).
// The caller must create a Client (FFIBackend) before any rendering.
func formatRationalFFI(num, denom int64) (string, error) {
	if err := ensureRendererLoaded(); err != nil {
		return "", err
	}
	if !hsInitialized() {
		return "", ffiError("GHC runtime not initialized: create a Client (FFIBackend) before rendering")
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	raw := C.renderer_call_format_rational(rendererFormatFn, C.int64_t(num), C.int64_t(denom))
	if raw == nil {
		// Unreachable for a well-formed rational (the kernel never returns null);
		// surface it as an error rather than a fabricated "0" — a null means a
		// kernel/ABI malfunction, and a silent "0" would hide the bug and violate
		// the "be vocal" contract. Matches the Rust binding's null handling (#101).
		return "", ffiError("aletheia_format_rational returned a null pointer")
	}
	defer C.renderer_call_free_str(rendererFreeFn, raw)
	return C.GoString(raw), nil
}
