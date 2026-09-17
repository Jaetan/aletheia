// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The three indexed lookups (message by ID, message by name, signal by name)
// freeze positions when the index is built. A caller may then shrink the
// public slice, so a cached position falls out of range, or overwrite an
// element in place, so the position stays in range but names something else.
// Either way the lookup answers not found rather than panicking or returning
// the wrong element. The tests build the indexes through the unexported
// builders, which is why they live in the package.

package aletheia

import "testing"

// indexedLookup is one lookup over a container holding entries A and B with
// its index built: found reports whether the entry named A or B is found,
// shrink drops B's position, and overwrite keeps B's position but changes
// the key stored there.
type indexedLookup struct {
	name      string
	found     func(key string) bool
	shrink    func()
	overwrite func()
}

func indexedLookups(t *testing.T) []indexedLookup {
	t.Helper()
	idA, _ := NewStandardID(0x200)
	idB, _ := NewStandardID(0x201)
	idC, _ := NewStandardID(0x202)
	ids := map[string]StandardID{"A": idA, "B": idB}
	byID := &DBCDefinition{Messages: []DBCMessage{{ID: idA, Name: "A"}, {ID: idB, Name: "B"}}}
	byID.buildIndexes()
	byName := &DBCDefinition{Messages: []DBCMessage{{ID: idA, Name: "A"}, {ID: idB, Name: "B"}}}
	byName.buildIndexes()
	msg := DBCMessage{Name: "Msg", Signals: []DBCSignal{{Name: "A"}, {Name: "B"}}}
	msg.buildSignalIndex()
	return []indexedLookup{
		{
			name:      "MessageByID",
			found:     func(k string) bool { return byID.MessageByID(ids[k]) != nil },
			shrink:    func() { byID.Messages = byID.Messages[:1] },
			overwrite: func() { byID.Messages[1].ID = idC },
		},
		{
			name:      "MessageByName",
			found:     func(k string) bool { return byName.MessageByName(MessageName(k)) != nil },
			shrink:    func() { byName.Messages = byName.Messages[:1] },
			overwrite: func() { byName.Messages[1].Name = "Renamed" },
		},
		{
			name:      "SignalByName",
			found:     func(k string) bool { return msg.SignalByName(SignalName(k)) != nil },
			shrink:    func() { msg.Signals = msg.Signals[:1] },
			overwrite: func() { msg.Signals[1].Name = "Renamed" },
		},
	}
}

// A cached position that has fallen out of range reads as not found, and
// the surviving entry is still found.
func TestIndexedLookups_StalePositionReadsAsNotFound(t *testing.T) {
	for _, l := range indexedLookups(t) {
		t.Run(l.name, func(t *testing.T) {
			if !l.found("B") {
				t.Fatal("B must be found before the slice is shrunk")
			}
			l.shrink()
			if l.found("B") {
				t.Error("a stale cached position must read as not found")
			}
			if !l.found("A") {
				t.Error("A must still be found after the shrink")
			}
		})
	}
}

// A cached position that is in range but names another element reads as not
// found: the guard compares the key, not only the bound.
func TestIndexedLookups_WrongPositionReadsAsNotFound(t *testing.T) {
	for _, l := range indexedLookups(t) {
		t.Run(l.name, func(t *testing.T) {
			if !l.found("B") {
				t.Fatal("B must be found before the overwrite")
			}
			l.overwrite()
			if l.found("B") {
				t.Error("an in-range but wrong cached position must read as not found")
			}
			if !l.found("A") {
				t.Error("A must still be found")
			}
		})
	}
}
