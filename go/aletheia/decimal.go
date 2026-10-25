//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Decimal text to an exact [Rational] through the kernel's own parser
// (aletheia_parse_decimal), which is what the Python, C++ and Rust bindings
// use too, so the four agree byte for byte and no binding carries a float64
// on this path. Like the rational renderer this file is a consumer of the GHC
// runtime, not its owner: it calls the library the runtime started on,
// through the entries the start recorded, and never starts the runtime, which
// [StartRuntime] or a backend does with the core count it was given.

package aletheia

/*
#include "aletheia_abi.h"
#include <stdlib.h>

static int8_t decimal_call_parse(void *fn, const struct aletheia_text *s, struct aletheia_decimal *out) {
    return ((int8_t (*)(const struct aletheia_text*, struct aletheia_decimal*))fn)(s, out);
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
	"errors"
	"fmt"
	"runtime"
	"unsafe"
)

// FromDecimal parses a decimal literal into an exact [Rational] through the
// kernel: "0.1" is 1/10, "3.14" is 157/50, "42" is 42/1. The grammar is the
// kernel's, an optional minus, digits, and optionally a point followed by
// digits; no plus sign, no leading or trailing point, no exponent, so "1e3",
// ".5", "1." and "+2" are refused.
//
// The call needs the GHC runtime up, which [StartRuntime] or a backend starts;
// without it the call fails before reaching the FFI rather than starting the
// runtime with a default core count, so a program that reads a decimal before
// opening a client calls [StartRuntime] first.
//
// Errors: the kernel's refusal, read by the envelope reader the binary-output
// entries share. The literal is the caller's own text, so a refused one is an
// [*Error] of kind [ErrValidation] whose Code says how: [CodeTextParseFailure]
// (nothing parsed) or [CodeTextTrailingInput] (a number parsed and characters
// followed), its Message naming the line and column, or
// [CodeFFIValidationError] when the shim refused the bytes (an interior NUL, bytes that are not UTF-8);
// a numerator or denominator whose magnitude is past the kernel's component
// bound is an [*InputBoundExceededError] with Field "decimal". [ErrFFI] when
// the runtime is down; [ErrProtocol] on a null return or a malformed
// response, which no working kernel produces.
func FromDecimal(s string) (Rational, error) {
	entries, err := startedEntries("parsing decimals")
	if err != nil {
		return Rational{}, err
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	cStr := C.CString(s)
	defer C.free(unsafe.Pointer(cStr))
	text := C.struct_aletheia_text{data: cStr, size: C.size_t(len(s))}
	var out C.struct_aletheia_decimal
	if C.decimal_call_parse(entries.parseDecimal, &text, &out) != 0 {
		if out.err == nil {
			return Rational{}, protocolError("aletheia_parse_decimal failed without an error")
		}
		defer C.decimal_call_free_str(entries.freeStr, out.err)
		return Rational{}, refusedLiteral(binaryRefusal("aletheia_parse_decimal", C.GoString(out.err)))
	}
	return decimalValue(int64(out.value.numerator), int64(out.value.denominator))
}

// refusedLiteral gives a coded refusal of the literal the kind of a caller's
// own mistake: the envelope reader answers every well-formed refusal as
// ErrProtocol with its Code, and the literal is the caller's text, not the
// wire's. A typed bound error and a protocol fault (no Code) pass unchanged.
func refusedLiteral(err error) error {
	var e *Error
	if errors.As(err, &e) && e.Kind == ErrProtocol && e.Code != "" {
		return &Error{Kind: ErrValidation, Code: e.Code, Message: e.Message}
	}
	return err
}

// decimalValue is the parsed rational, whose denominator the kernel answers
// positive; any other is the ABI or the kernel malfunctioning.
func decimalValue(numerator, denominator int64) (Rational, error) {
	if denominator <= 0 {
		return Rational{}, protocolError(fmt.Sprintf("aletheia_parse_decimal answered a non-positive denominator %d", denominator))
	}
	return Rational{Numerator: numerator, Denominator: denominator}, nil
}
