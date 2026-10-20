//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// A DBC load between two reads of the real library's allocation count leaves
// the second above the first. The count is the runtime's own and only grows,
// so whatever else the process runs between the reads, a load that allocates
// is enough to raise it, and a read that does not reach the runtime is not.
// TestMain's backend started the runtime with the real library, so both
// reads answer a count.
func TestAllocatedBytes_GrowsAcrossALoad(t *testing.T) {
	client := ffiClient(t)
	before, ok := aletheia.AllocatedBytes()
	if !ok {
		t.Fatal("AllocatedBytes answered no count before the load, with a backend open")
	}
	if _, err := client.ParseDBCText(t.Context(), ffiEndpointDBC); err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	after, ok := aletheia.AllocatedBytes()
	if !ok {
		t.Fatal("AllocatedBytes answered no count after the load, with a backend open")
	}
	if after <= before {
		t.Errorf("allocated bytes read %d after the load and %d before it, want the count to grow", after, before)
	}
}
