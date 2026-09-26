// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// The constructor builds the lookup indexes, so a definition made through it
// answers by index what a definition populated by hand answers by scanning,
// and the two agree on every message, present or absent.
func TestNewDBCDefinition_IndexesWhatAHandBuiltDefinitionScans(t *testing.T) {
	byHand := testDBC()
	indexed := aletheia.NewDBCDefinition(byHand.Version, byHand.Messages)
	if indexed.Version != byHand.Version || len(indexed.Messages) != len(byHand.Messages) {
		t.Fatalf("the constructor did not keep what it was given: %+v", indexed)
	}
	present := standardID(t, 0x123)
	absent := standardID(t, 0x124)
	for _, id := range []aletheia.CANID{present, absent} {
		got, want := indexed.MessageByID(id), byHand.MessageByID(id)
		if (got == nil) != (want == nil) || (got != nil && got.Name != want.Name) {
			t.Errorf("MessageByID(%v): indexed %v, scanned %v", id, got, want)
		}
	}
	for _, name := range []aletheia.MessageName{"EngineData", "Missing"} {
		got, want := indexed.MessageByName(name), byHand.MessageByName(name)
		if (got == nil) != (want == nil) || (got != nil && got.ID.Value() != want.ID.Value()) {
			t.Errorf("MessageByName(%q): indexed %v, scanned %v", name, got, want)
		}
	}
}
