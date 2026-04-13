package aletheia

import (
	"errors"
	"strings"
	"testing"
)

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
