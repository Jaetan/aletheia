//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The rational printer every binding shares, which is the kernel's. Nothing
// here formats a number: the library does, so the four bindings print the same
// text because they call the same function.
//
// The library is opened and its two symbols resolved on first use. The GHC
// runtime is not started here, and this is the rule the whole file turns on: a
// backend starts it, choosing how many cores it gets, and the runtime starts
// once per process. A renderer that started it would fix that choice at a
// default before the backend could make it, so with the runtime down the
// renderer refuses and says so.

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

	// The path a backend registered, which the search below prefers over
	// its own guesses and which the environment still overrides. The first
	// registration wins, and one after the renderer has loaded changes
	// nothing, the symbols being resolved once.
	defaultLibPathMu sync.Mutex
	defaultLibPath   string
)

// RegisterDefaultLibPath names the library the renderer should open. Opening
// a backend calls it, so the renderer, which opens the library on its own,
// opens the one the caller named rather than one it guessed at.
func RegisterDefaultLibPath(libPath string) {
	defaultLibPathMu.Lock()
	defer defaultLibPathMu.Unlock()
	if defaultLibPath == "" { // first-write-wins
		defaultLibPath = libPath
	}
}

// findFFILibrary is the library to open: the one the environment names, then
// the one a backend registered, then the places a build leaves it relative to
// where the tests run. Empty when none of them has it.
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

// loadRendererFFI opens the library and resolves the two symbols this file
// calls, and nothing else: starting the runtime is a backend's to do.
// loadStandaloneSymbols opens the library and resolves the symbols named,
// pinning the thread while it does, because dlerror is per thread and a
// goroutine that migrated between the failure and the message would report the
// wrong one, or none. It serves the two consumers that reach the kernel outside
// a session, this file and the decimal parser, and it starts no runtime, which
// is the rule both turn on. what names the caller in the message a failure to
// open carries.
//
// Only strings and untyped pointers cross, so the caller's own file can hold
// the trampolines it calls them through; a cgo preamble is visible to one file.
func loadStandaloneSymbols(what string, names ...string) ([]unsafe.Pointer, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	libPath := findFFILibrary()
	if libPath == "" {
		return nil, ffiError("libaletheia-ffi.so not found; build with: cabal run shake -- build")
	}

	cPath := C.CString(libPath)
	defer C.free(unsafe.Pointer(cPath))
	handle := C.dlopen(cPath, C.RTLD_NOW|C.RTLD_LOCAL)
	if handle == nil {
		return nil, ffiError(what + " dlopen failed: " + C.GoString(C.dlerror()))
	}

	resolved := make([]unsafe.Pointer, 0, len(names))
	for _, name := range names {
		sym, err := rendererDlsym(handle, name)
		if err != nil {
			return nil, err
		}
		resolved = append(resolved, sym)
	}
	return resolved, nil
}

func loadRendererFFI() error {
	syms, err := loadStandaloneSymbols("renderer", "aletheia_format_rational", "aletheia_free_str")
	if err != nil {
		return err
	}
	rendererFormatFn, rendererFreeFn = syms[0], syms[1]
	return nil
}

// rendererDlsym resolves one symbol, reporting the loader's own message. The
// caller has pinned the thread, dlerror being per thread.
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

// formatRationalFFI renders a rational through the kernel, resolving the
// symbols on the first call. With the runtime down it refuses, for the reason
// at the top of this file: a client must exist before anything renders.
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
		// A null is the kernel or the boundary malfunctioning, never an answer
		// about the number: a zero in its place would read as a rendered value.
		// The Rust binding refuses a null here too.
		return "", ffiError("aletheia_format_rational returned a null pointer")
	}
	defer C.renderer_call_free_str(rendererFreeFn, raw)
	return C.GoString(raw), nil
}
