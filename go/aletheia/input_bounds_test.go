package aletheia

import (
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"unsafe"
)

// UR-2 cross-binding parity: *InputBoundExceededError exists, carries
// BoundKind/Observed/Limit, satisfies the error interface, and is
// returned when a JSON payload exceeds MaxJSONBytes at the FFI boundary
// before the payload is marshaled across cgo.
//
// The Agda kernel ALSO rejects (parseJSON's input-length cap returns a
// parse_input_bound_exceeded error response), but the binding-side
// short-circuit fires first so the C string is never strdup'd.

func TestInputBoundExceededError_Shape(t *testing.T) {
	t.Run("carries kind observed limit", func(t *testing.T) {
		err := &InputBoundExceededError{
			BoundKind: BoundKindInputLengthBytes,
			Observed:  100,
			Limit:     50,
			Code:      CodeParseInputBoundExceeded,
		}
		if err.BoundKind != "input_length_bytes" {
			t.Errorf("BoundKind = %q, want %q", err.BoundKind, "input_length_bytes")
		}
		if err.Observed != 100 || err.Limit != 50 {
			t.Errorf("Observed/Limit = %d/%d, want 100/50", err.Observed, err.Limit)
		}
		if err.Code != "parse_input_bound_exceeded" {
			t.Errorf("Code = %q, want %q", err.Code, "parse_input_bound_exceeded")
		}
	})

	t.Run("error message contains all three fields", func(t *testing.T) {
		err := &InputBoundExceededError{
			BoundKind: BoundKindInputLengthBytes,
			Observed:  100,
			Limit:     50,
		}
		msg := err.Error()
		for _, want := range []string{"input_length_bytes", "100", "50"} {
			if !strings.Contains(msg, want) {
				t.Errorf("Error() = %q, missing %q", msg, want)
			}
		}
	})

	t.Run("satisfies error interface and errors.As", func(t *testing.T) {
		var err error = &InputBoundExceededError{
			BoundKind: BoundKindInputLengthBytes,
			Observed:  100,
			Limit:     50,
		}
		var bex *InputBoundExceededError
		if !errors.As(err, &bex) {
			t.Fatal("errors.As did not unwrap to *InputBoundExceededError")
		}
		if bex.Observed != 100 {
			t.Errorf("unwrapped Observed = %d, want 100", bex.Observed)
		}
	})
}

func TestLimits_Constants(t *testing.T) {
	tests := []struct {
		name string
		got  uint64
		want uint64
	}{
		{"MaxJSONBytes 64 MiB", uint64(MaxJSONBytes), 64 * 1024 * 1024},
		{"MaxDBCTextBytes 64 MiB", uint64(MaxDBCTextBytes), 64 * 1024 * 1024},
		{"MaxNestingDepth", uint64(MaxNestingDepth), 64},
		{"MaxFrameByteCount", uint64(MaxFrameByteCount), 64},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if tt.got != tt.want {
				t.Errorf("got %d, want %d", tt.got, tt.want)
			}
		})
	}

	// Bound-kind wire codes mirror boundKindCode in Aletheia.Limits.
	wantCodes := map[string]string{
		"InputLengthBytes": BoundKindInputLengthBytes,
		"NestingDepth":     BoundKindNestingDepth,
		"ArrayCardinality": BoundKindArrayCardinality,
		"IdentifierLength": BoundKindIdentifierLength,
		"StringLength":     BoundKindStringLength,
		"AtomCount":        BoundKindAtomCount,
		"FrameByteCount":   BoundKindFrameByteCount,
	}
	wantValues := map[string]string{
		"InputLengthBytes": "input_length_bytes",
		"NestingDepth":     "nesting_depth",
		"ArrayCardinality": "array_cardinality",
		"IdentifierLength": "identifier_length",
		"StringLength":     "string_length",
		"AtomCount":        "atom_count",
		"FrameByteCount":   "frame_byte_count",
	}
	for name, got := range wantCodes {
		if got != wantValues[name] {
			t.Errorf("BoundKind%s = %q, want %q", name, got, wantValues[name])
		}
	}
}

// FFI-boundary short-circuit on oversize input.  Uses FFIBackend.Process
// directly with a synthetic state pointer; we never reach the actual cgo
// call because the bound check fires first.
func TestProcess_RejectsOversizeJSON(t *testing.T) {
	// Construct a JSON payload one byte over MaxJSONBytes.  Using a
	// minimal FFIBackend (zero-valued) is OK because the bound check
	// is the first line of `process` — the cgo function pointers are
	// never reached.
	backend := &FFIBackend{}
	bigInput := strings.Repeat("x", MaxJSONBytes+1)

	_, err := backend.Process(unsafe.Pointer(nil), bigInput)
	if err == nil {
		t.Fatal("expected InputBoundExceededError, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.BoundKind != BoundKindInputLengthBytes {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, BoundKindInputLengthBytes)
	}
	if bex.Observed <= MaxJSONBytes {
		t.Errorf("Observed = %d, want > %d", bex.Observed, MaxJSONBytes)
	}
	if bex.Limit != MaxJSONBytes {
		t.Errorf("Limit = %d, want %d", bex.Limit, MaxJSONBytes)
	}
	if bex.Code != CodeParseInputBoundExceeded {
		t.Errorf("Code = %q, want %q", bex.Code, CodeParseInputBoundExceeded)
	}
}

// R19 cluster A: per-loader bound checks for the YAML loader entry points,
// closing the cross-binding asymmetry where Python's yaml_loader caps but
// Go's loadYAMLData / LoadChecksFromYAMLFile previously did not.
//
// Uses a sparse file (truncate to MaxDBCTextBytes+1) so the test does not
// write 64+ MiB of real bytes; the bound check reads st_size which reports
// the truncated size unconditionally on Linux.

func TestLoadChecksFromYAMLFile_RejectsOversize(t *testing.T) {
	tmpFile := filepath.Join(t.TempDir(), "huge.yaml")
	f, err := os.Create(tmpFile)
	if err != nil {
		t.Fatalf("create temp file: %v", err)
	}
	if err := f.Truncate(int64(MaxDBCTextBytes) + 1); err != nil {
		t.Fatalf("truncate: %v", err)
	}
	if err := f.Close(); err != nil {
		t.Fatalf("close: %v", err)
	}

	_, err = LoadChecksFromYAMLFile(tmpFile)
	if err == nil {
		t.Fatal("expected InputBoundExceededError, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.BoundKind != BoundKindInputLengthBytes {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, BoundKindInputLengthBytes)
	}
	if bex.Observed != uint64(MaxDBCTextBytes)+1 {
		t.Errorf("Observed = %d, want %d", bex.Observed, uint64(MaxDBCTextBytes)+1)
	}
	if bex.Limit != MaxDBCTextBytes {
		t.Errorf("Limit = %d, want %d", bex.Limit, MaxDBCTextBytes)
	}
}

func TestLoadYAMLData_FilePathOversize(t *testing.T) {
	tmpFile := filepath.Join(t.TempDir(), "huge.yaml")
	f, err := os.Create(tmpFile)
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	if err := f.Truncate(int64(MaxDBCTextBytes) + 1); err != nil {
		t.Fatalf("truncate: %v", err)
	}
	if err := f.Close(); err != nil {
		t.Fatalf("close: %v", err)
	}

	_, err = loadYAMLData(tmpFile)
	if err == nil {
		t.Fatal("expected InputBoundExceededError, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.Observed != uint64(MaxDBCTextBytes)+1 {
		t.Errorf("Observed = %d, want %d", bex.Observed, uint64(MaxDBCTextBytes)+1)
	}
}

func TestLoadYAMLData_InlineStringOversize(t *testing.T) {
	// loadYAMLData treats source as inline YAML when os.Stat fails (no file).
	// A repeated-x string of length > MaxDBCTextBytes that's not a valid path
	// triggers the inline-form bound check.
	bigInline := strings.Repeat("x", MaxDBCTextBytes+1)
	_, err := loadYAMLData(bigInline)
	if err == nil {
		t.Fatal("expected InputBoundExceededError, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.BoundKind != BoundKindInputLengthBytes {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, BoundKindInputLengthBytes)
	}
	if bex.Observed != uint64(MaxDBCTextBytes)+1 {
		t.Errorf("Observed = %d, want %d", bex.Observed, uint64(MaxDBCTextBytes)+1)
	}
	if bex.Limit != MaxDBCTextBytes {
		t.Errorf("Limit = %d, want %d", bex.Limit, MaxDBCTextBytes)
	}
}

// R19 cluster E1: defense-in-depth output bound on serializeDBC.
// Constructs a DBCDefinition whose marshaled JSON exceeds MaxDBCTextBytes
// and verifies serializeDBC returns *InputBoundExceededError before the
// payload is handed to the FFI.  In normal flow the upstream parser cap
// makes this redundant; this guard catches any internal blowup or future
// bypass.

func TestSerializeDBC_RejectsOversizeOutput(t *testing.T) {
	// A 64 MiB+ Version string drives the marshaled JSON over the cap.
	// Allocating a 64 MiB string is acceptable for a single test —
	// completes in <1s on a typical CI box.
	bigVersion := strings.Repeat("x", MaxDBCTextBytes+100)
	dbc := DBCDefinition{Version: bigVersion}

	_, err := serializeDBC(dbc)
	if err == nil {
		t.Fatal("expected InputBoundExceededError, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.BoundKind != BoundKindInputLengthBytes {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, BoundKindInputLengthBytes)
	}
	if bex.Observed <= uint64(MaxDBCTextBytes) {
		t.Errorf("Observed = %d, want > %d", bex.Observed, MaxDBCTextBytes)
	}
	if bex.Limit != MaxDBCTextBytes {
		t.Errorf("Limit = %d, want %d", bex.Limit, MaxDBCTextBytes)
	}
}
