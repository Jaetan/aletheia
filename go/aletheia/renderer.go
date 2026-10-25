//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The rational printer every binding shares, which is the kernel's. Nothing
// here formats a number: the library does, so the four bindings print the same
// text because they call the same function.
//
// The printer calls the library the runtime started on, through the entries
// the start recorded, and never starts the runtime: [StartRuntime] or a
// backend does, choosing how many cores it gets, and the runtime starts once
// per process. A printer that started it would fix that choice at a default
// before the program could make it, so with the runtime down the printer
// refuses and says so.

package aletheia

/*
#include "aletheia_abi.h"
#include <stdint.h>

// Cgo trampolines local to this file.
static char* renderer_call_format_rational(void *fn, struct aletheia_rational value) {
    return ((char* (*)(const struct aletheia_rational*))fn)(&value);
}
static void renderer_call_free_str(void *fn, char *ptr) {
    ((void (*)(char*))fn)(ptr);
}
*/
import "C"

import "runtime"

// formatRationalFFI renders a rational through the kernel. With the runtime
// down it refuses, for the reason at the top of this file.
func formatRationalFFI(num, denom int64) (string, error) {
	entries, err := startedEntries("rendering")
	if err != nil {
		return "", err
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	raw := C.renderer_call_format_rational(entries.formatRational,
		C.struct_aletheia_rational{numerator: C.int64_t(num), denominator: C.int64_t(denom)})
	if raw == nil {
		// A null is the kernel or the boundary malfunctioning, never an answer
		// about the number: a zero in its place would read as a rendered value.
		// The Rust binding refuses a null here too.
		return "", ffiError("aletheia_format_rational returned a null pointer")
	}
	defer C.renderer_call_free_str(entries.freeStr, raw)
	return C.GoString(raw), nil
}
