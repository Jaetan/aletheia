// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Internal-package tests for the frozen-index lookup guards (r25). The lazy
// indexes freeze positional indices on first build; if the caller then shrinks
// the public Messages / Signals slice, an unguarded cached index would panic on
// the subscript. The guard turns a stale index into a defined nil ("no longer
// present"). Each test builds the index, shrinks the slice, then re-queries the
// dropped entry — pre-fix this panicked; post-fix it returns nil.
//
// These live in `package aletheia` (not aletheia_test) so they can build the
// indexes directly via the unexported buildIndexes / buildSignalIndex, without
// routing through a mock parse.

package aletheia

import "testing"

func TestMessageByID_StaleCachedIndexGuard(t *testing.T) {
	idA, err := NewStandardID(0x200)
	if err != nil {
		t.Fatalf("NewStandardID(0x200): %v", err)
	}
	idB, err := NewStandardID(0x201)
	if err != nil {
		t.Fatalf("NewStandardID(0x201): %v", err)
	}
	d := &DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{
			{ID: idA, Name: MessageName("A")},
			{ID: idB, Name: MessageName("B")},
		},
	}
	d.buildIndexes() // idIndex: A->0, B->1 (frozen)

	if d.MessageByID(idB) == nil {
		t.Fatal("B must be found before the slice is shrunk")
	}
	// Drop the last message — B's cached index (1) is now out of bounds.
	d.Messages = d.Messages[:1]
	if got := d.MessageByID(idB); got != nil {
		t.Errorf("stale cached index must return nil, got %+v", got)
	}
	// The surviving message is still found.
	if d.MessageByID(idA) == nil {
		t.Error("A must still be found after the shrink")
	}
}

func TestMessageByName_StaleCachedIndexGuard(t *testing.T) {
	idA, _ := NewStandardID(0x200)
	idB, _ := NewStandardID(0x201)
	d := &DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{
			{ID: idA, Name: MessageName("A")},
			{ID: idB, Name: MessageName("B")},
		},
	}
	d.buildIndexes() // nameIndex: A->0, B->1 (frozen)

	if d.MessageByName(MessageName("B")) == nil {
		t.Fatal("B must be found before the slice is shrunk")
	}
	d.Messages = d.Messages[:1]
	if got := d.MessageByName(MessageName("B")); got != nil {
		t.Errorf("stale cached index must return nil, got %+v", got)
	}
	if d.MessageByName(MessageName("A")) == nil {
		t.Error("A must still be found after the shrink")
	}
}

func TestSignalByName_StaleCachedIndexGuard(t *testing.T) {
	m := DBCMessage{
		Name: MessageName("Msg"),
		Signals: []DBCSignal{
			{Name: SignalName("A")},
			{Name: SignalName("B")},
		},
	}
	m.buildSignalIndex() // signalIndex: A->0, B->1 (frozen)

	if m.SignalByName(SignalName("B")) == nil {
		t.Fatal("B must be found before the slice is shrunk")
	}
	// Drop the last signal — B's cached index (1) is now out of bounds.
	m.Signals = m.Signals[:1]
	if got := m.SignalByName(SignalName("B")); got != nil {
		t.Errorf("stale cached index must return nil, got %+v", got)
	}
	if m.SignalByName(SignalName("A")) == nil {
		t.Error("A must still be found after the shrink")
	}
}

// The following tests cover the in-bounds-but-wrong case: the slice is mutated
// in place (reordered / replaced) so a stale cached index stays in bounds but
// names a different element. A bounds-only guard would return the wrong element;
// the key-match check returns nil.

func TestMessageByID_WrongCachedIndexGuard(t *testing.T) {
	idA, _ := NewStandardID(0x200)
	idB, _ := NewStandardID(0x201)
	idC, _ := NewStandardID(0x202)
	d := &DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{
			{ID: idA, Name: MessageName("A")},
			{ID: idB, Name: MessageName("B")},
		},
	}
	d.buildIndexes() // idIndex: A->0, B->1

	if d.MessageByID(idB) == nil {
		t.Fatal("B must be found before the in-place replace")
	}
	// Replace the message at the cached index in place with a different id.
	d.Messages[1].ID = idC
	if got := d.MessageByID(idB); got != nil {
		t.Errorf("in-bounds but wrong cached index must return nil, got %+v", got)
	}
	if d.MessageByID(idA) == nil {
		t.Error("A must still be found")
	}
}

func TestMessageByName_WrongCachedIndexGuard(t *testing.T) {
	idA, _ := NewStandardID(0x200)
	idB, _ := NewStandardID(0x201)
	d := &DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{
			{ID: idA, Name: MessageName("A")},
			{ID: idB, Name: MessageName("B")},
		},
	}
	d.buildIndexes() // nameIndex: A->0, B->1

	if d.MessageByName(MessageName("B")) == nil {
		t.Fatal("B must be found before the in-place replace")
	}
	d.Messages[1].Name = MessageName("Renamed")
	if got := d.MessageByName(MessageName("B")); got != nil {
		t.Errorf("in-bounds but wrong cached index must return nil, got %+v", got)
	}
	if d.MessageByName(MessageName("A")) == nil {
		t.Error("A must still be found")
	}
}

func TestSignalByName_WrongCachedIndexGuard(t *testing.T) {
	m := DBCMessage{
		Name: MessageName("Msg"),
		Signals: []DBCSignal{
			{Name: SignalName("A")},
			{Name: SignalName("B")},
		},
	}
	m.buildSignalIndex() // signalIndex: A->0, B->1

	if m.SignalByName(SignalName("B")) == nil {
		t.Fatal("B must be found before the in-place replace")
	}
	m.Signals[1].Name = SignalName("Renamed")
	if got := m.SignalByName(SignalName("B")); got != nil {
		t.Errorf("in-bounds but wrong cached index must return nil, got %+v", got)
	}
	if m.SignalByName(SignalName("A")) == nil {
		t.Error("A must still be found")
	}
}
