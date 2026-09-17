//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"unsafe"
)

// The typed bound error and every entry point that refuses before the payload
// crosses. The kernel refuses oversized input too, its parser carrying the
// same cap, but the binding's check fires first, so nothing is copied into C
// to be rejected on the far side.

// requireBoundExceeded holds that the failure is the typed bound error with
// the kind, the observed size and the limit the caller expects. An observed
// size of zero means only that it must be over the limit, which is what the
// entry points that measure an encoded payload can promise.
func requireBoundExceeded(t *testing.T, err error, observed, limit uint64) *InputBoundExceededError {
	t.Helper()
	if err == nil {
		t.Fatal("expected a bound error, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.BoundKind != BoundKindInputLengthBytes {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, BoundKindInputLengthBytes)
	}
	if bex.Limit != limit {
		t.Errorf("Limit = %d, want %d", bex.Limit, limit)
	}
	switch {
	case observed != 0 && bex.Observed != observed:
		t.Errorf("Observed = %d, want %d", bex.Observed, observed)
	case observed == 0 && bex.Observed <= limit:
		t.Errorf("Observed = %d, want more than the limit %d", bex.Observed, limit)
	}
	if bex.Code != CodeInputBoundExceeded {
		t.Errorf("Code = %q, want %q", bex.Code, CodeInputBoundExceeded)
	}
	return bex
}

// The error carries the three numbers that let a caller act on it, renders all
// three, and survives wrapping.
func TestInputBoundExceededError_Shape(t *testing.T) {
	err := &InputBoundExceededError{
		BoundKind: BoundKindInputLengthBytes,
		Observed:  100,
		Limit:     50,
		Code:      CodeInputBoundExceeded,
	}
	t.Run("carries kind observed limit", func(t *testing.T) {
		if err.BoundKind != "input_length_bytes" {
			t.Errorf("BoundKind = %q, want %q", err.BoundKind, "input_length_bytes")
		}
		if err.Observed != 100 || err.Limit != 50 {
			t.Errorf("Observed/Limit = %d/%d, want 100/50", err.Observed, err.Limit)
		}
		if err.Code != "input_bound_exceeded" {
			t.Errorf("Code = %q, want %q", err.Code, "input_bound_exceeded")
		}
	})

	t.Run("renders all three", func(t *testing.T) {
		msg := err.Error()
		for _, want := range []string{"input_length_bytes", "100", "50"} {
			if !strings.Contains(msg, want) {
				t.Errorf("Error() = %q, missing %q", msg, want)
			}
		}
	})

	t.Run("unwraps through errors.As", func(t *testing.T) {
		var wrapped error = err
		var bex *InputBoundExceededError
		if !errors.As(wrapped, &bex) {
			t.Fatal("errors.As did not unwrap to *InputBoundExceededError")
		}
		if bex.Observed != 100 {
			t.Errorf("unwrapped Observed = %d, want 100", bex.Observed)
		}
	})
}

// The limits are the numbers the protocol fixes, and every bound kind spells
// the wire code the kernel's own table spells. The roster here is the whole
// set: a kind the binding declares and this map omits would go unchecked.
func TestLimits_Constants(t *testing.T) {
	limits := map[string]struct{ got, want uint64 }{
		"MaxJSONBytes":      {uint64(MaxJSONBytes), 64 * 1024 * 1024},
		"MaxDBCTextBytes":   {uint64(MaxDBCTextBytes), 64 * 1024 * 1024},
		"MaxNestingDepth":   {uint64(MaxNestingDepth), 64},
		"MaxFrameByteCount": {uint64(MaxFrameByteCount), 64},
	}
	for name, tc := range limits {
		t.Run(name, func(t *testing.T) {
			if tc.got != tc.want {
				t.Errorf("%s = %d, want %d", name, tc.got, tc.want)
			}
		})
	}

	kinds := map[string]string{
		BoundKindInputLengthBytes:           "input_length_bytes",
		BoundKindNestingDepth:               "nesting_depth",
		BoundKindArrayCardinality:           "array_cardinality",
		BoundKindIdentifierLength:           "identifier_length",
		BoundKindStringLength:               "string_length",
		BoundKindAtomCount:                  "atom_count",
		BoundKindFrameByteCount:             "frame_byte_count",
		BoundKindPropertyCount:              "property_count",
		BoundKindRationalComponentMagnitude: "rational_component_magnitude",
	}
	for got, want := range kinds {
		if got != want {
			t.Errorf("bound kind %q should spell %q", got, want)
		}
	}
	if len(kinds) != 9 {
		t.Errorf("the roster holds %d kinds; the binding declares nine", len(kinds))
	}
}

// A payload past the cap is refused at the boundary, before anything is
// copied into C. The backend is the zero value on purpose: reaching a
// trampoline through it would crash, so the test passing is itself the
// evidence that the check fires first.
func TestProcess_RejectsOversizeJSON(t *testing.T) {
	backend := &FFIBackend{}
	_, err := backend.Process(unsafe.Pointer(nil), strings.Repeat("x", MaxJSONBytes+1))
	requireBoundExceeded(t, err, uint64(MaxJSONBytes)+1, uint64(MaxJSONBytes))
}

// Both YAML entry points measure the file before reading it. The file is
// sparse, so the test costs an inode rather than sixty-four mebibytes, and
// the check reads the size the filesystem reports.
func TestYAMLLoaders_RejectOversizeFile(t *testing.T) {
	t.Run("LoadChecksFromYAMLFile", func(t *testing.T) {
		_, err := LoadChecksFromYAMLFile(oversizeYAMLFile(t))
		requireBoundExceeded(t, err, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes))
	})
	t.Run("loadYAMLData", func(t *testing.T) {
		_, err := loadYAMLData(oversizeYAMLFile(t))
		requireBoundExceeded(t, err, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes))
	})
}

// oversizeYAMLFile is a sparse file one byte over the text cap.
func oversizeYAMLFile(t *testing.T) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), "huge.yaml")
	f, err := os.Create(path)
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	if err := f.Truncate(int64(MaxDBCTextBytes) + 1); err != nil {
		t.Fatalf("truncate: %v", err)
	}
	if err := f.Close(); err != nil {
		t.Fatalf("close: %v", err)
	}
	return path
}

// Text handed to the YAML loader directly, rather than as a path, is measured
// the same way.
func TestLoadYAMLData_InlineStringOversize(t *testing.T) {
	_, err := loadYAMLData(strings.Repeat("x", MaxDBCTextBytes+1))
	requireBoundExceeded(t, err, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes))
}

// The serializer measures what it produced. Nothing upstream can currently
// grow a definition past the cap, the parser refusing first, so this is the
// second lock on the same door rather than the only one.
func TestSerializeDBC_RejectsOversizeOutput(t *testing.T) {
	_, err := serializeDBC(DBCDefinition{Version: strings.Repeat("x", MaxDBCTextBytes+100)})
	requireBoundExceeded(t, err, 0, uint64(MaxDBCTextBytes))
}

// The DBC text is measured before it is wrapped in a command, so the refusal
// reports the inner cap rather than the cap on the command that would have
// carried it.
func TestParseDBCText_RejectsOversizeText(t *testing.T) {
	c, err := NewClient(NewMockBackend())
	if err != nil {
		t.Fatal(err)
	}
	defer func() { _ = c.Close() }()

	_, err = c.ParseDBCText(context.Background(), strings.Repeat("x", MaxDBCTextBytes+1))
	requireBoundExceeded(t, err, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes))
}
