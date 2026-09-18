// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"errors"
	"strings"
	"testing"
	"time"
)

// The helpers the tests inside the package share; helpers_test.go carries the
// same claims for the tests outside, which cannot reach an unexported name.

// bounded is the context a test hands the client: a call the client answers
// takes milliseconds, so a deadline of two seconds turns a hang, such as a lock
// left held by an earlier call, into a failure of this test rather than of
// the whole binary. A test that cancels makes its own.
func bounded(t *testing.T) context.Context {
	t.Helper()
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	t.Cleanup(cancel)
	return ctx
}

// closeWithin closes the client, failing the test rather than hanging it
// when Close cannot take the lock within two seconds: Close waits for the lock with no
// context, by design, so a lock an earlier call left held would otherwise
// block the whole binary.
func closeWithin(t *testing.T, c *Client) error {
	t.Helper()
	done := make(chan error, 1)
	go func() { done <- c.Close() }()
	select {
	case err := <-done:
		return err
	case <-time.After(2 * time.Second):
		t.Fatal("Close did not return within two seconds: the client lock is still held")
		return nil
	}
}

// recvWithin receives from ch, failing the test rather than hanging it when
// nothing sends within two seconds: the goroutines the tests park answer in
// milliseconds once released, so a longer wait is a call that never came.
func recvWithin[T any](t *testing.T, ch <-chan T) T {
	t.Helper()
	select {
	case v := <-ch:
		return v
	case <-time.After(2 * time.Second):
		t.Fatal("nothing was received within two seconds")
		var zero T
		return zero
	}
}

// requireErrorContains holds that the failure is the package's error type,
// through whatever wraps it, and that its message carries the substring.
func requireErrorContains(t *testing.T, err error, substr string) {
	t.Helper()
	if err == nil {
		t.Fatal("expected error, got nil")
	}
	var e *Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *Error, got %T: %v", err, err)
	}
	if !strings.Contains(err.Error(), substr) {
		t.Errorf("expected error containing %q, got: %v", substr, err)
	}
}
