// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import "testing"

// growStack recurses with a wide frame until the goroutine's stack must grow,
// which copies every live frame below it, the caller's included.
func growStack(n int) int {
	var pad [512]byte
	pad[n%512] = byte(n)
	if n == 0 {
		return int(pad[0])
	}
	return growStack(n-1) + int(pad[n%512])
}

// TestStateHandleSurvivesStackCopy: a session handle held live in a frame
// while the stack is copied does not end the process. The kernel's handle is
// a GHC StablePtr, an index into a table and not an address, and the Go
// runtime ends the process when it copies a stack holding a value below 4096
// in a pointer slot; so the handle is an integer on the Go side.
func TestStateHandleSurvivesStackCopy(t *testing.T) {
	_, state := ffiSession(t)
	if growStack(4000) == 0 {
		t.Fatal("the recursion did not run")
	}
	t.Logf("handle %v held live across the growth", state)
}
