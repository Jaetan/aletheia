package aletheia

import (
	"context"
	"errors"
	"strings"
	"testing"
)

// ctx is the default context for internal-package tests that don't exercise
// cancellation. Tests that DO exercise cancellation create their own
// context.WithCancel or context.WithTimeout in-test.
var ctx = context.Background()

// requireErrorContains asserts err is a non-nil *Error whose message
// contains substr. Uses errors.As for proper unwrapping (G-6 review finding).
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
