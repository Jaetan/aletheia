// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// A batch's two views partition its results: the violation is the one result
// that fails, and the satisfactions are every result that holds, in order.
// A batch of satisfactions alone has no violation.
func TestPropertyBatch_ViolationAndSatisfactionsPartitionTheResults(t *testing.T) {
	holds := func(i uint) aletheia.PropertyResult {
		return aletheia.PropertyResult{PropertyIndex: aletheia.PropertyIndex(i), Verdict: aletheia.Holds}
	}
	fails := aletheia.PropertyResult{PropertyIndex: 7, Verdict: aletheia.Fails}
	mixed := aletheia.PropertyBatch{Results: []aletheia.PropertyResult{holds(1), holds(2), fails}}
	if v := mixed.FirstViolation(); v == nil || v.PropertyIndex != 7 {
		t.Errorf("FirstViolation = %v, want property 7", v)
	}
	sat := mixed.Satisfactions()
	if len(sat) != 2 || sat[0].PropertyIndex != 1 || sat[1].PropertyIndex != 2 {
		t.Errorf("Satisfactions = %v, want properties 1 and 2", sat)
	}
	allHold := aletheia.PropertyBatch{Results: []aletheia.PropertyResult{holds(3)}}
	if v := allHold.FirstViolation(); v != nil {
		t.Errorf("FirstViolation of a batch that holds = %v, want nil", v)
	}
	if sat := allHold.Satisfactions(); len(sat) != 1 || sat[0].PropertyIndex != 3 {
		t.Errorf("Satisfactions = %v, want property 3", sat)
	}
	onlyFails := aletheia.PropertyBatch{Results: []aletheia.PropertyResult{fails}}
	if sat := onlyFails.Satisfactions(); len(sat) != 0 {
		t.Errorf("Satisfactions of a violation alone = %v, want none", sat)
	}
}
