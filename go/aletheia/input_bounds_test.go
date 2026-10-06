//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"
	"unsafe"
)

// The typed bound error, every entry point that refuses before the payload
// crosses, and the size bounds on a DBC that only the kernel checks. Where
// both check, the kernel's parser carries the same cap, but the binding's
// check fires first, so nothing is copied into C to be rejected on the far
// side.

// requireBoundExceeded holds that the failure is the typed bound error with
// the kind, the observed size, the limit and the field the caller expects,
// the field empty for a bound that names none. An observed size of zero means
// only that it must be over the limit, which is what the entry points that
// measure an encoded payload can promise.
func requireBoundExceeded(t *testing.T, err error, kind string, observed, limit uint64, field string) *InputBoundExceededError {
	t.Helper()
	if err == nil {
		t.Fatal("expected a bound error, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.BoundKind != kind {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, kind)
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
	if bex.Field != field {
		t.Errorf("Field = %q, want %q", bex.Field, field)
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
		"MaxJSONBytes":                          {uint64(MaxJSONBytes), 64 * 1024 * 1024},
		"MaxDBCTextBytes":                       {uint64(MaxDBCTextBytes), 64 * 1024 * 1024},
		"MaxNestingDepth":                       {uint64(MaxNestingDepth), 64},
		"MaxSignalGroupsPerFile":                {uint64(MaxSignalGroupsPerFile), 10000},
		"MaxEnvironmentVariablesPerFile":        {uint64(MaxEnvironmentVariablesPerFile), 10000},
		"MaxUnresolvedValueDescriptionsPerFile": {uint64(MaxUnresolvedValueDescriptionsPerFile), 10000},
		"MaxEnumLabelsPerAttribute":             {uint64(MaxEnumLabelsPerAttribute), 10000},
		"MaxMultiplexValuesPerSignal":           {uint64(MaxMultiplexValuesPerSignal), 1024},
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
		BoundKindPropertyCount:              "property_count",
		BoundKindRationalComponentMagnitude: "rational_component_magnitude",
	}
	for got, want := range kinds {
		if got != want {
			t.Errorf("bound kind %q should spell %q", got, want)
		}
	}
	if len(kinds) != 8 {
		t.Errorf("the roster holds %d kinds; the binding declares eight", len(kinds))
	}
}

// A payload past the cap is refused at the boundary, before anything is
// copied into C. The backend is the zero value on purpose: reaching a
// trampoline through it would crash, so the test passing is itself the
// evidence that the check fires first. The refusal carries no kernel message,
// so its text is the binding's own.
func TestProcess_RejectsOversizeJSON(t *testing.T) {
	backend := &FFIBackend{}
	_, err := backend.Process(unsafe.Pointer(nil), strings.Repeat("x", MaxJSONBytes+1))
	bex := requireBoundExceeded(t, err, BoundKindInputLengthBytes, uint64(MaxJSONBytes)+1, uint64(MaxJSONBytes), "")
	if bex.Message != "" {
		t.Errorf("Message = %q, want none for a refusal the binding makes", bex.Message)
	}
	want := "aletheia validation error: input_length_bytes " + strconv.Itoa(MaxJSONBytes+1) +
		" exceeds limit " + strconv.Itoa(MaxJSONBytes)
	if got := err.Error(); got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
}

// Both YAML entry points measure the file before reading it. The file is
// sparse, so the test costs an inode rather than sixty-four mebibytes, and
// the check reads the size the filesystem reports.
func TestYAMLLoaders_RejectOversizeFile(t *testing.T) {
	t.Run("LoadChecksFromYAMLFile", func(t *testing.T) {
		_, err := LoadChecksFromYAMLFile(oversizeYAMLFile(t))
		requireBoundExceeded(t, err, BoundKindInputLengthBytes, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes), "")
	})
	t.Run("loadYAMLData", func(t *testing.T) {
		_, err := loadYAMLData(oversizeYAMLFile(t))
		requireBoundExceeded(t, err, BoundKindInputLengthBytes, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes), "")
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
	requireBoundExceeded(t, err, BoundKindInputLengthBytes, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes), "")
}

// The serializer measures what it produced. Nothing upstream can currently
// grow a definition past the cap, the parser refusing first, so this is the
// second lock on the same door rather than the only one.
func TestSerializeDBC_RejectsOversizeOutput(t *testing.T) {
	_, err := serializeDBC(DBCDefinition{Version: strings.Repeat("x", MaxDBCTextBytes+100)})
	requireBoundExceeded(t, err, BoundKindInputLengthBytes, 0, uint64(MaxDBCTextBytes), "")
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

	_, err = c.ParseDBCText(t.Context(), strings.Repeat("x", MaxDBCTextBytes+1))
	requireBoundExceeded(t, err, BoundKindInputLengthBytes, uint64(MaxDBCTextBytes)+1, uint64(MaxDBCTextBytes), "")
}

// The size bounds on a DBC's lists and strings are the kernel's alone: the
// binding sends the definition and lifts the refusal into the typed error,
// which names the field the kernel refused and whose text is the kernel's
// message. The expected numbers are the ones the library answers for these
// definitions.

// boundLabels are the kernel's names for the bounds a DBC's lists and strings
// cross, as its message spells them.
var boundLabels = map[string]string{
	BoundKindArrayCardinality: "array cardinality",
	BoundKindStringLength:     "string length",
}

// requireKernelMessage holds that the refusal's text is the kernel's message,
// whole, and that the typed error carries it.
func requireKernelMessage(t *testing.T, err error, bex *InputBoundExceededError, want string) {
	t.Helper()
	if got := err.Error(); got != want {
		t.Errorf("Error() = %q, want the kernel's message %q", got, want)
	}
	if bex.Message != want {
		t.Errorf("Message = %q, want %q", bex.Message, want)
	}
}

// numbered is n distinct values, each the prefix and its index.
func numbered[T ~string](prefix string, n int) []T {
	out := make([]T, n)
	for i := range out {
		out[i] = T(prefix + strconv.Itoa(i))
	}
	return out
}

// boundSignal is a one-bit unsigned signal at unit scale.
func boundSignal(name string) DBCSignal {
	return DBCSignal{
		Name: SignalName(name), BitLength: 1, ByteOrder: LittleEndian,
		Factor: IntRational(1), Offset: IntRational(0),
		Minimum: IntRational(0), Maximum: IntRational(1),
		Presence: AlwaysPresent{},
	}
}

// boundMessage is an eight-byte message ECU sends, carrying the signals.
func boundMessage(t *testing.T, id uint16, signals ...DBCSignal) DBCMessage {
	t.Helper()
	sid, err := NewStandardID(id)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	dlc, err := NewDLC(8)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	return DBCMessage{
		ID: sid, Name: MessageName("M" + strconv.Itoa(int(id))), DLC: dlc,
		Sender: "ECU", Signals: signals,
	}
}

// dbcBound is a definition past one size bound and what the kernel answers
// for it: the base definition with one list or string overfilled.
type dbcBound struct {
	overfill func(t *testing.T, d *DBCDefinition)
	kind     string
	observed uint64
	limit    uint64
}

// definition is one message with one signal, then the overfill.
func (b dbcBound) definition(t *testing.T) DBCDefinition {
	t.Helper()
	d := DBCDefinition{Version: "1.0", Messages: []DBCMessage{boundMessage(t, 0x100, boundSignal("S"))}}
	b.overfill(t, &d)
	return d
}

// kernelMessage is the kernel's refusal of the bound under the command: the
// command, the field, the bound's name, the size observed and the limit.
func (b dbcBound) kernelMessage(command, field string) string {
	return command + ": " + field + ": " + boundLabels[b.kind] + " " +
		strconv.FormatUint(b.observed, 10) + " exceeds limit " + strconv.FormatUint(b.limit, 10)
}

// cardinality is a list one entry past its limit.
func cardinality(limit uint64, overfill func(t *testing.T, d *DBCDefinition)) dbcBound {
	return dbcBound{overfill: overfill, kind: BoundKindArrayCardinality, observed: limit + 1, limit: limit}
}

// listBounds are the bounds on a DBC's metadata lists, keyed by the field the
// kernel's message names.
func listBounds() map[string]dbcBound {
	return map[string]dbcBound{
		"signal groups array": cardinality(MaxSignalGroupsPerFile, func(_ *testing.T, d *DBCDefinition) {
			for i := range MaxSignalGroupsPerFile + 1 {
				d.SignalGroups = append(d.SignalGroups, DBCSignalGroup{Name: "G" + strconv.Itoa(i)})
			}
		}),
		"environment variables array": cardinality(MaxEnvironmentVariablesPerFile, func(_ *testing.T, d *DBCDefinition) {
			for i := range MaxEnvironmentVariablesPerFile + 1 {
				d.EnvironmentVars = append(d.EnvironmentVars, DBCEnvironmentVar{
					Name: "E" + strconv.Itoa(i), VarType: DBCVarTypeInt,
					Initial: IntRational(0), Minimum: IntRational(0), Maximum: IntRational(1),
				})
			}
		}),
		"unresolved value descriptions array": cardinality(MaxUnresolvedValueDescriptionsPerFile, func(t *testing.T, d *DBCDefinition) {
			id, err := NewStandardID(999)
			if err != nil {
				t.Fatalf("NewStandardID: %v", err)
			}
			d.UnresolvedValueDescriptions = slices.Repeat(
				[]DBCRawValueDesc{{ID: id, SignalName: "Q"}}, MaxUnresolvedValueDescriptionsPerFile+1)
		}),
		"senders array": cardinality(MaxNodesPerFile, func(_ *testing.T, d *DBCDefinition) {
			d.Messages[0].Senders = numbered[NodeName]("N", MaxNodesPerFile+1)
		}),
		"receivers array": cardinality(MaxNodesPerFile, func(_ *testing.T, d *DBCDefinition) {
			d.Messages[0].Signals[0].Receivers = numbered[NodeName]("N", MaxNodesPerFile+1)
		}),
		"signal group members array": cardinality(MaxSignalsPerMessage, func(_ *testing.T, d *DBCDefinition) {
			d.SignalGroups = []DBCSignalGroup{{Name: "G", Signals: numbered[SignalName]("S", MaxSignalsPerMessage+1)}}
		}),
		"enum labels array": cardinality(MaxEnumLabelsPerAttribute, func(_ *testing.T, d *DBCDefinition) {
			d.Attributes = []DBCAttribute{DBCAttrDef{
				Name: "A", Scope: DBCAttrScopeNetwork,
				AttrType: DBCAttrTypeEnum{Values: numbered[string]("v", MaxEnumLabelsPerAttribute+1)},
			}}
		}),
		"multiplex values array": cardinality(MaxMultiplexValuesPerSignal, func(_ *testing.T, d *DBCDefinition) {
			selector := boundSignal("Mx")
			selector.BitLength, selector.Maximum = 8, IntRational(255)
			values := make([]MultiplexValue, MaxMultiplexValuesPerSignal+1)
			for i := range values {
				values[i] = MultiplexValue(i)
			}
			muxed := boundSignal("S")
			muxed.StartBit = 8
			muxed.Presence = Multiplexed{Multiplexor: "Mx", MultiplexValues: values}
			d.Messages[0].Signals = []DBCSignal{selector, muxed}
		}),
	}
}

// ParseDBC refuses a definition past any list bound, naming the list.
func TestParseDBC_RefusesEachListBound(t *testing.T) {
	c := newFFIClient(t)
	for field, bound := range listBounds() {
		t.Run(field, func(t *testing.T) {
			_, err := c.ParseDBC(t.Context(), bound.definition(t))
			bex := requireBoundExceeded(t, err, bound.kind, bound.observed, bound.limit, field)
			requireKernelMessage(t, err, bex, bound.kernelMessage("ParseDBC", field))
		})
	}
}

// ValidateDBC refuses a definition past a list bound, as ParseDBC does,
// rather than answering it with issues.
func TestValidateDBC_RefusesAListBound(t *testing.T) {
	c := newFFIClient(t)
	const field = "enum labels array"
	bound := listBounds()[field]
	_, err := c.ValidateDBC(t.Context(), bound.definition(t))
	bex := requireBoundExceeded(t, err, bound.kind, bound.observed, bound.limit, field)
	requireKernelMessage(t, err, bex, bound.kernelMessage("ValidateDBC", field))
}

// FormatDBCText checks every size bound before it formats and refuses as the
// load routes do: a list past its limit, a string past its length, and the
// nodes it derives from the messages' senders when the definition lists none.
func TestFormatDBCText_RefusesADefinitionPastASizeBound(t *testing.T) {
	c := newFFIClient(t)
	bounds := map[string]dbcBound{
		"signal groups array": listBounds()["signal groups array"],
		"version string": {
			overfill: func(_ *testing.T, d *DBCDefinition) {
				d.Version = strings.Repeat("x", MaxStringLengthCharacters+1)
			},
			kind: BoundKindStringLength, observed: MaxStringLengthCharacters + 1, limit: MaxStringLengthCharacters,
		},
		// No nodes are listed, so they are derived: ECU and the two messages'
		// distinct senders, one more than half the limit each.
		"nodes array": {
			overfill: func(t *testing.T, d *DBCDefinition) {
				first := boundMessage(t, 0x100, boundSignal("S"))
				first.Senders = numbered[NodeName]("A", MaxNodesPerFile/2+1)
				second := boundMessage(t, 0x101, boundSignal("S"))
				second.Senders = numbered[NodeName]("B", MaxNodesPerFile/2+1)
				d.Messages = []DBCMessage{first, second}
			},
			kind: BoundKindArrayCardinality, observed: MaxNodesPerFile + 3, limit: MaxNodesPerFile,
		},
	}
	for field, bound := range bounds {
		t.Run(field, func(t *testing.T) {
			_, err := c.FormatDBCText(t.Context(), bound.definition(t))
			bex := requireBoundExceeded(t, err, bound.kind, bound.observed, bound.limit, field)
			requireKernelMessage(t, err, bex, bound.kernelMessage("FormatDBCText", field))
		})
	}
}
