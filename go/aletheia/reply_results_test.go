// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "testing"

// resultReader reads a reply holding one property result, the result's JSON
// text, answering the results it read.
type resultReader func(t *testing.T, result string) ([]PropertyResult, error)

// resultReaders are the two replies holding property results: a frame's batch
// and the end of a stream.
var resultReaders = []struct {
	name string
	read resultReader
}{
	{"frame batch", func(t *testing.T, result string) ([]PropertyResult, error) {
		t.Helper()
		fr, err := parseFrameResponse(`{"type":"property_batch","results":[` + result + `]}`)
		if err != nil {
			return nil, err
		}
		batch, ok := fr.(PropertyBatch)
		if !ok {
			t.Fatalf("read as %T, want a PropertyBatch", fr)
		}
		return batch.Results, nil
	}},
	{"end of stream", func(_ *testing.T, result string) ([]PropertyResult, error) {
		sr, err := parseStreamResponse(`{"status":"complete","results":[` + result + `],"warnings":[]}`)
		if err != nil {
			return nil, err
		}
		return sr.Results, nil
	}},
}

// streamWarning reads the end of a stream holding one warning, the warning's
// JSON text.
func streamWarning(warning string) (*StreamResult, error) {
	return parseStreamResponse(`{"status":"complete","results":[],"warnings":[` + warning + `]}`)
}

// refusedRow is an entry a reader refuses and what its refusal says came.
type refusedRow struct {
	entry, came string
}

// requireRowsRefused holds that read refuses each row's entry at place
// expecting expected, the refusal naming what came.
func requireRowsRefused(t *testing.T, read func(*testing.T, string) error, place, expected string, rows []refusedRow) {
	t.Helper()
	for _, row := range rows {
		t.Run(row.came, func(t *testing.T) {
			requireReplyRefusal(t, read(t, row.entry), "reply "+place+": expected "+expected+", got "+row.came)
		})
	}
}

// requireResultRowsRefused holds requireRowsRefused of both result readers.
func requireResultRowsRefused(t *testing.T, place, expected string, rows []refusedRow) {
	t.Helper()
	for _, reader := range resultReaders {
		t.Run(reader.name, func(t *testing.T) {
			requireRowsRefused(t, func(t *testing.T, result string) error {
				_, err := reader.read(t, result)
				return err
			}, place, expected, rows)
		})
	}
}

// Each of a property result's three statuses is read as its verdict by both
// readers.
func TestPropertyResult_EachStatusIsReadAsItsVerdict(t *testing.T) {
	statuses := []struct {
		result string
		want   Verdict
	}{
		{`{"type":"property","status":"fails","property_index":0,"timestamp":5,"reason":"r"}`, Fails},
		{`{"type":"property","status":"holds","property_index":0}`, Holds},
		{`{"type":"property","status":"unresolved","property_index":0,"reason":"r"}`, Unresolved},
	}
	for _, reader := range resultReaders {
		t.Run(reader.name, func(t *testing.T) {
			for _, status := range statuses {
				results, err := reader.read(t, status.result)
				if err != nil {
					t.Errorf("%s: %v, want it read", status.result, err)
					continue
				}
				if len(results) != 1 || results[0].Verdict != status.want {
					t.Errorf("%s: read as %+v, want one result of verdict %v", status.result, results, status.want)
				}
			}
		})
	}
}

// A property result's type is "property", any other refused at its place, a
// word as well as nothing or a number.
func TestPropertyResult_TypeOtherThanPropertyIsRefusedAtItsPlace(t *testing.T) {
	requireResultRowsRefused(t, "results/type", `"property"`, []refusedRow{
		{`{"type":"verdict","status":"holds","property_index":0}`, `"verdict"`},
		{`{"status":"holds","property_index":0}`, "nothing"},
		{`{"type":0,"status":"holds","property_index":0}`, "number"},
	})
}

// A property result's status is "fails", "holds" or "unresolved", any other
// refused at its place, a word as well as nothing or a number.
func TestPropertyResult_StatusOutsideFailsHoldsAndUnresolvedIsRefusedAtItsPlace(t *testing.T) {
	requireResultRowsRefused(t, "results/status", `"fails", "holds" or "unresolved"`, []refusedRow{
		{`{"type":"property","status":"bogus","property_index":0,"reason":"r"}`, `"bogus"`},
		{`{"type":"property","property_index":0,"reason":"r"}`, "nothing"},
		{`{"type":"property","status":0,"property_index":0,"reason":"r"}`, "number"},
	})
}

// An end-of-stream warning's kind is "uncached_atom", read as
// WarningUncachedAtom, any other refused at its place, a word as well as
// nothing or a number.
func TestStreamWarning_KindOtherThanUncachedAtomIsRefusedAtItsPlace(t *testing.T) {
	sr, err := streamWarning(`{"kind":"uncached_atom","property_index":3,"detail":"d"}`)
	if err != nil {
		t.Fatalf("uncached_atom: %v, want it read", err)
	}
	want := StreamWarning{Kind: WarningUncachedAtom, PropertyIndex: 3, Detail: "d"}
	if len(sr.Warnings) != 1 || sr.Warnings[0] != want {
		t.Errorf("read as %+v, want [%+v]", sr.Warnings, want)
	}
	requireRowsRefused(t, func(_ *testing.T, warning string) error {
		_, err := streamWarning(warning)
		return err
	}, "warnings/kind", `"uncached_atom"`, []refusedRow{
		{`{"kind":"stale_atom","property_index":0,"detail":"d"}`, `"stale_atom"`},
		{`{"property_index":0,"detail":"d"}`, "nothing"},
		{`{"kind":0,"property_index":0,"detail":"d"}`, "number"},
	})
}
