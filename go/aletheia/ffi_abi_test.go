//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// The structures the cgo preamble declares lay out as haskell-shim/include/aletheia.h
// fixes them. The expected sizes and offsets are read from the header's own
// static_assert lines, which the C compiler holds to the real layout, so a
// field moved on either side fails here rather than misreading across the ABI.
func TestFFIStructuresMatchKernelHeader(t *testing.T) {
	text, err := os.ReadFile(filepath.Join(repoRoot(t), "haskell-shim", "include", "aletheia.h"))
	if err != nil {
		t.Fatal(err)
	}
	wantSizes := map[string]uintptr{}
	for _, m := range regexp.MustCompile(`static_assert\(sizeof\(struct (\w+)\) == (\d+),`).FindAllStringSubmatch(string(text), -1) {
		wantSizes[m[1]] = parseOffset(t, m[2])
	}
	wantFields := map[string][]abiField{}
	for _, m := range regexp.MustCompile(`static_assert\(offsetof\(struct (\w+), (\w+)\) == (\d+),`).FindAllStringSubmatch(string(text), -1) {
		wantFields[m[1]] = append(wantFields[m[1]], abiField{m[2], parseOffset(t, m[3])})
	}

	version := regexp.MustCompile(`enum \{ ALETHEIA_ABI_VERSION = (\d+) \};`).FindStringSubmatch(string(text))
	if version == nil || parseOffset(t, version[1]) != abiVersion {
		t.Errorf("abiVersion = %d, header defines %v", abiVersion, version)
	}

	sizes, fields := abiLayout()
	if !reflect.DeepEqual(sizes, wantSizes) {
		t.Errorf("sizes = %v, header asserts %v", sizes, wantSizes)
	}
	if !reflect.DeepEqual(fields, wantFields) {
		t.Errorf("fields = %v, header asserts %v", fields, wantFields)
	}
}

// The backend admits a library at its own ABI version and names both
// versions when it refuses any other.
func TestABIVersionErrorAdmitsOnlyTheBindingsVersion(t *testing.T) {
	if err := abiVersionError(abiVersion); err != nil {
		t.Fatalf("the binding's own version was refused: %v", err)
	}
	for _, found := range []uint32{abiVersion - 1, abiVersion + 1} {
		err := abiVersionError(found)
		want := fmt.Sprintf("the library implements ABI version %d, and this binding needs %d", found, abiVersion)
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("abiVersionError(%d) = %v, want an error carrying %q", found, err, want)
		}
	}
}

// A binary entry's refusal is the error envelope a JSON response carries, and
// reads as the JSON path reads one: a kernel code and the shim's own each on
// the coded error with the message inside the envelope, and a structured
// payload lifted to its typed error. Text that is not an envelope, or an
// envelope that is not an error, is the library malfunctioning, which no
// working library sets and the tests over the real one therefore never reach.
func TestBinaryRefusalReadsTheErrorEnvelope(t *testing.T) {
	coded := map[string]struct{ envelope, code, message string }{
		"a kernel code": {
			`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`,
			CodeHandlerNoDBC, "no DBC loaded",
		},
		"the shim's code": {
			`{"status":"error","code":"ffi_validation_error","message":"build_frame_bin: null out buffer"}`,
			"ffi_validation_error", "build_frame_bin: null out buffer",
		},
	}
	for name, tc := range coded {
		t.Run(name, func(t *testing.T) {
			requireDegradedCoded(t, binaryRefusal("build_frame_bin", tc.envelope), tc.code, tc.message)
		})
	}

	t.Run("a structured payload", func(t *testing.T) {
		err := binaryRefusal("build_frame_bin", `{"status":"error","code":"input_bound_exceeded",`+
			`"message":"too many signals","bound_kind":"array_cardinality","observed":1025,"limit":1024}`)
		var bex *InputBoundExceededError
		if !errors.As(err, &bex) {
			t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
		}
		want := InputBoundExceededError{BoundKind: BoundKindArrayCardinality, Observed: 1025, Limit: 1024, Code: CodeInputBoundExceeded}
		if *bex != want {
			t.Errorf("got %+v, want %+v", *bex, want)
		}
	})

	malfunctions := map[string]struct{ envelope, says string }{
		"not JSON":     {"no DBC loaded", "invalid JSON response"},
		"not an error": {`{"status":"success"}`, "extract_signals_bin refused with a response that is not an error envelope"},
	}
	for name, tc := range malfunctions {
		t.Run(name, func(t *testing.T) {
			err := binaryRefusal("extract_signals_bin", tc.envelope)
			var aErr *Error
			if !errors.As(err, &aErr) {
				t.Fatalf("expected *Error, got %T: %v", err, err)
			}
			if aErr.Kind != ErrProtocol || aErr.Code != "" {
				t.Errorf("Kind = %v, Code = %q, want ErrProtocol with no code: %v", aErr.Kind, aErr.Code, err)
			}
			if !strings.Contains(err.Error(), tc.says) {
				t.Errorf("error %q does not say %q", err, tc.says)
			}
		})
	}
}

func parseOffset(t *testing.T, digits string) uintptr {
	t.Helper()
	n, err := strconv.ParseUint(digits, 10, 64)
	if err != nil {
		t.Fatal(err)
	}
	return uintptr(n)
}
