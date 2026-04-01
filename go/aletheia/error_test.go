package aletheia_test

import (
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestErrorResponse(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"error","message":"no DBC loaded"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestBackendError(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.RespondErr(aletheia.NewMockError("connection lost")),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.ParseDBC(testDBC())
	if err == nil {
		t.Fatal("expected error from backend")
	}
}

func TestMockBackendExhaustion(t *testing.T) {
	mock := aletheia.NewMockBackend() // no responses
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.ParseDBC(testDBC())
	if err == nil {
		t.Fatal("expected error when mock exhausted")
	}
}

func TestUseAfterClose(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()

	// Calling after Close should return a state error, not crash.
	err = c.ParseDBC(testDBC())
	if err == nil {
		t.Fatal("expected error after Close")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrState {
		t.Errorf("expected ErrState, got %s", aErr.Kind)
	}

	// Double-close should be safe.
	c.Close()
}

func TestErrorKindString(t *testing.T) {
	tests := []struct {
		kind aletheia.ErrorKind
		want string
	}{
		{aletheia.ErrProtocol, "protocol"},
		{aletheia.ErrValidation, "validation"},
		{aletheia.ErrState, "state"},
		{aletheia.ErrFFI, "ffi"},
		{aletheia.ErrorKind(99), "unknown"},
	}
	for _, tt := range tests {
		if got := tt.kind.String(); got != tt.want {
			t.Errorf("ErrorKind(%d).String() = %q, want %q", tt.kind, got, tt.want)
		}
	}
}

func TestDoubleClose(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("first close: %v", err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("second close: %v", err)
	}
}
