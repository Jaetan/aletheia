// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"cmp"
	"testing"
)

// The enrichment merges the last frame of every message in the order
// compareFrameKeys gives, which the end-to-end test observes only through
// the order a map yields its keys in. Held here directly, each pair both
// ways round, so an order that reads the packed key whole, ignores the kind,
// or answers the same for every pair is refused on every run.
func TestCompareFrameKeysOrdersByValueThenStandardFirst(t *testing.T) {
	std := func(v uint16) uint64 {
		id, err := NewStandardID(v)
		if err != nil {
			t.Fatal(err)
		}
		return canIDKey(id)
	}
	ext := func(v uint32) uint64 {
		id, err := NewExtendedID(v)
		if err != nil {
			t.Fatal(err)
		}
		return canIDKey(id)
	}
	cases := []struct {
		name string
		a, b uint64
		want int
	}{
		{"one value, standard before extended", std(0x100), ext(0x100), -1},
		{"a lower standard before a higher one", std(0x100), std(0x7FF), -1},
		{"a lower extended before a higher standard", ext(0x100), std(0x200), -1},
		{"a key beside itself", std(0x100), std(0x100), 0},
		{"an extended beside itself", ext(0x1FFFFFFF), ext(0x1FFFFFFF), 0},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if got := cmp.Compare(compareFrameKeys(tc.a, tc.b), 0); got != tc.want {
				t.Errorf("compareFrameKeys(%#x, %#x) has sign %d, want %d", tc.a, tc.b, got, tc.want)
			}
			if got := cmp.Compare(compareFrameKeys(tc.b, tc.a), 0); got != -tc.want {
				t.Errorf("compareFrameKeys(%#x, %#x) has sign %d, want %d", tc.b, tc.a, got, -tc.want)
			}
		})
	}
}
