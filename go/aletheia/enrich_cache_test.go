// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "testing"

// The extraction cache stores up to maxExtractCache results across its inner
// maps: storing a key it already holds again does not count twice, the last
// new key that fits is taken and the next is refused, a stored result is
// still read back once it is full, and a cleared cache takes keys again.
func TestExtractCache_HoldsUpToItsBound(t *testing.T) {
	c := newExtractCache()
	metas := [2]frameMeta{{idValue: 1, dlc: 8}, {idValue: 2, isExtended: true, dlc: 8}}
	r := &ExtractionResult{}
	key := func(i int) []byte { return []byte{byte(i), byte(i >> 8)} }
	for i := range maxExtractCache - 1 {
		if !c.put(metas[i%2], key(i), r) {
			t.Fatalf("put %d of %d refused", i+1, maxExtractCache)
		}
	}
	if !c.put(metas[0], key(0), r) {
		t.Fatal("storing a held key again was refused")
	}
	if !c.put(metas[1], key(maxExtractCache-1), r) {
		t.Fatal("the last key that fits was refused: storing a held key again counted")
	}
	if c.put(metas[0], key(maxExtractCache), r) {
		t.Error("a key past the bound was stored")
	}
	if got, ok := c.get(metas[1], key(1)); !ok || got != r {
		t.Error("a stored result was not read back from the full cache")
	}
	c.clear()
	if !c.put(metas[0], key(maxExtractCache), r) {
		t.Error("the cleared cache refused a key")
	}
}
