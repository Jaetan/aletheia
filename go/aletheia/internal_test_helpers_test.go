// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"errors"
	"strings"
	"testing"
)

// The helpers the tests inside the package share; helpers_test.go carries the
// same claims for the tests outside, which cannot reach an unexported name.

// ctx is for the tests that do not cancel; one that does makes its own.
var ctx = context.Background()

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
