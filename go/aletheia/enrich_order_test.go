//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"testing"
)

// twinIDDefinition is a definition carrying one standard and one extended
// message of the same identifier value, each with a Speed signal at a
// different position, so that which frame's Speed an enrichment reports says
// in which order the two frames were merged.
func twinIDDefinition(t *testing.T) DBCDefinition {
	t.Helper()
	sid, err := NewStandardID(0x100)
	if err != nil {
		t.Fatal(err)
	}
	eid, err := NewExtendedID(0x100)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := NewDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	speed := func(start BitPosition) DBCSignal {
		return DBCSignal{
			Name: "Speed", StartBit: start, BitLength: 8, ByteOrder: LittleEndian,
			Factor:   Rational{Numerator: 1, Denominator: 1},
			Offset:   Rational{Numerator: 0, Denominator: 1},
			Minimum:  Rational{Numerator: 0, Denominator: 1},
			Maximum:  Rational{Numerator: 255, Denominator: 1},
			Presence: AlwaysPresent{},
		}
	}
	return DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{
			{ID: sid, Name: "Std", DLC: dlc, Sender: "ECU", Signals: []DBCSignal{speed(0)}},
			{ID: eid, Name: "Ext", DLC: dlc, Sender: "ECU", Signals: []DBCSignal{speed(8)}},
		},
	}
}

// An end-of-stream enrichment reads the last frame of every message in the
// cross-binding order, ascending identifier value and then standard before
// extended, and the first frame carrying a signal supplies it, so a signal
// two messages both carry reads from the standard one. The order is read off
// the merge rather than off a sort of two keys, and the sort of two equal
// keys is whatever the map yielded, so the trial is repeated: a merge that
// ignored the kind would read the other value about half the time.
func TestEnrichment_MergesStandardBeforeExtended(t *testing.T) {
	if findFFILibrary() == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	dbc := twinIDDefinition(t)
	ctx := context.Background()
	never := []Formula{Eventually{Inner: Atomic{Predicate: GreaterThan{Signal: "Speed", Value: IntRational(200)}}}}
	for trial := range 12 {
		c := newFFIClient(t)
		if _, err := c.ParseDBC(ctx, dbc); err != nil {
			t.Fatalf("ParseDBC: %v", err)
		}
		if err := c.SetProperties(ctx, never); err != nil {
			t.Fatalf("SetProperties: %v", err)
		}
		if err := c.StartStream(ctx); err != nil {
			t.Fatalf("StartStream: %v", err)
		}
		// The extended frame carries 7 where its Speed sits, the standard
		// one 100; neither reaches 200, so the property fails at the end of
		// the stream and its enrichment merges both frames.
		if _, err := c.SendFrame(ctx, Timestamp{Microseconds: 1000}, dbc.Messages[1].ID, dbc.Messages[1].DLC,
			FramePayload{0, 7, 0, 0, 0, 0, 0, 0}, nil, nil); err != nil {
			t.Fatalf("SendFrame (extended): %v", err)
		}
		if _, err := c.SendFrame(ctx, Timestamp{Microseconds: 2000}, dbc.Messages[0].ID, dbc.Messages[0].DLC,
			FramePayload{100, 0, 0, 0, 0, 0, 0, 0}, nil, nil); err != nil {
			t.Fatalf("SendFrame (standard): %v", err)
		}
		result, err := c.EndStream(ctx)
		if err != nil {
			t.Fatalf("EndStream: %v", err)
		}
		if len(result.Results) != 1 || result.Results[0].Verdict != Fails || result.Results[0].Enrichment == nil {
			t.Fatalf("trial %d: want one enriched failure at the end of the stream, got %+v", trial, result.Results)
		}
		if got := result.Results[0].Enrichment.Signals["Speed"]; got != IntRational(100) {
			t.Fatalf("trial %d: Speed = %v, want 100, the standard frame's, read first", trial, got)
		}
	}
}
