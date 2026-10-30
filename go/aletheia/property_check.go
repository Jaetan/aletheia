//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The kernel's reading of a property as a builder makes it, and of a time
// bound as a loader reads one. A builder carrying a checked field (a value, a
// range's order, a tolerance's sign, a time bound, a signal name) hands what
// it made to aletheia_check_property, which reads it as set_properties reads
// a property and refuses it with set_properties' reason, so a check is
// refused where it is built. Both entries are consumers of the GHC runtime,
// as the renderer and the decimal parser are: they never start it, since a
// start fixes the core count for the process, and refuse while it is down.

package aletheia

/*
#include "aletheia_abi.h"
#include <stdlib.h>

static int8_t check_call_property(void *fn, const struct aletheia_text *s, struct aletheia_property_check *out) {
    return ((int8_t (*)(const struct aletheia_text*, struct aletheia_property_check*))fn)(s, out);
}
static int8_t check_call_time_bound(void *fn, const struct aletheia_text *s, struct aletheia_time_bound *out) {
    return ((int8_t (*)(const struct aletheia_text*, struct aletheia_time_bound*))fn)(s, out);
}
static void check_call_free_str(void *fn, char *ptr) {
    ((void (*)(char*))fn)(ptr);
}
*/
import "C"

import (
	"encoding/json"
	"runtime"
	"unsafe"
)

// checkFormula refuses f as the kernel's property parse refuses it, or
// answers nil. Every field, ordering, denominator and time bound is decided,
// and each signal name as an identifier; whether a DBC carries the signal is
// left to set_properties. The refusal's text is the reason set_properties
// gives after "SetProperties: property N: ", in an [*Error] of kind
// [ErrValidation] carrying the kernel's code, or an [*InputBoundExceededError]
// for a number past its bound. [ErrFFI] while the runtime is down.
func checkFormula(f Formula) error {
	property, err := serializeFormula(f)
	if err != nil {
		return err
	}
	text, err := json.Marshal(property)
	if err != nil {
		return err
	}
	entries, err := startedEntries("building a check")
	if err != nil {
		return err
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	cText := C.CString(string(text))
	defer C.free(unsafe.Pointer(cText))
	input := C.struct_aletheia_text{data: cText, size: C.size_t(len(text))}
	var out C.struct_aletheia_property_check
	if C.check_call_property(entries.checkProperty, &input, &out) != 0 {
		return entryRefusal(entries, "aletheia_check_property", out.err)
	}
	return nil
}

// ParseTimeBound reads a time bound, a whole number of microseconds, from
// text through the kernel's time-bound entry (aletheia_parse_time_bound),
// which is what a loader reads a check's within_us with in every binding.
//
// The call needs the GHC runtime up, which [StartRuntime] or a backend
// starts; without it the call fails with [ErrFFI] rather than starting the
// runtime with a default core count.
//
// Errors: the kernel's refusal, typed as [FromDecimal]'s is: an [*Error] of
// kind [ErrValidation] whose Code says how and whose Message is the kernel's
// reason ("timebound -1500 is negative", "timebound 1.5 is not a whole
// number", or the decimal parser's message for text that is no number), and
// an [*InputBoundExceededError] with Field "time bound" for a value past
// 2^64-1.
func ParseTimeBound(text string) (TimeBound, error) {
	entries, err := startedEntries("reading a time bound")
	if err != nil {
		return TimeBound{}, err
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	cText := C.CString(text)
	defer C.free(unsafe.Pointer(cText))
	input := C.struct_aletheia_text{data: cText, size: C.size_t(len(text))}
	var out C.struct_aletheia_time_bound
	if C.check_call_time_bound(entries.parseTimeBound, &input, &out) != 0 {
		return TimeBound{}, entryRefusal(entries, "aletheia_parse_time_bound", out.err)
	}
	return TimeBound{Microseconds: uint64(out.microseconds)}, nil
}

// entryRefusal reads the error envelope an entry outside a session wrote on
// a refusal, frees it, and types it as the caller's own mistake.
func entryRefusal(entries *runtimeEntries, symbol string, envelope *C.char) error {
	if envelope == nil {
		return protocolError(symbol + " refused without an error")
	}
	defer C.check_call_free_str(entries.freeStr, envelope)
	return refusedLiteral(binaryRefusal(C.GoString(envelope)))
}
