// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The cancellation tests live in the package itself so they can implement
// the sealed [Backend] interface and control FFI timing call by call.

import (
	"context"
	"errors"
	"strings"
	"testing"
	"unsafe"
)

// routingBackend implements [Backend] by counting every call and handing it
// to one hook with its ordinal. The doubles below build on it and differ only
// in the hook, which answers at once: no test here parks a call or runs one
// beside another.
type routingBackend struct {
	calls int
	hook  func(n int) (string, error)
}

func (*routingBackend) backend() {}

func (b *routingBackend) Init() (unsafe.Pointer, error) {
	var sentinel byte
	return unsafe.Pointer(&sentinel), nil
}

func (b *routingBackend) Process(_ unsafe.Pointer, _ string) (string, error) {
	b.calls++
	return b.hook(b.calls)
}

func (b *routingBackend) callCount() int { return b.calls }

func (b *routingBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CANID, _ DLC, _ []byte, _ *bool, _ *bool) (string, error) {
	return b.Process(nil, "")
}
func (b *routingBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return b.Process(nil, "")
}
func (b *routingBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CANID) (string, error) {
	return b.Process(nil, "")
}
func (b *routingBackend) StartStreamBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *routingBackend) EndStreamBinary(_ unsafe.Pointer) (string, error) { return b.Process(nil, "") }
func (b *routingBackend) FormatDBCBinary(_ unsafe.Pointer) (string, error) { return b.Process(nil, "") }
func (b *routingBackend) ExtractSignalsBinary(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) (string, error) {
	return b.Process(nil, "")
}
func (b *routingBackend) BuildFrameBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []SignalInjection) ([]byte, error) {
	_, err := b.Process(nil, "")
	return nil, err
}
func (b *routingBackend) UpdateFrameBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte, _ []SignalInjection) ([]byte, error) {
	_, err := b.Process(nil, "")
	return nil, err
}
func (b *routingBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) ([]byte, error) {
	return nil, ErrBinaryPathUnsupported
}
func (b *routingBackend) Close(_ unsafe.Pointer) {}

// newAnsweringBackend is a routingBackend that answers resp to every call at
// once, so a test counts the calls that reached the FFI without parking any.
func newAnsweringBackend(resp string) *routingBackend {
	b := &routingBackend{}
	b.hook = func(int) (string, error) { return resp, nil }
	return b
}

// newClientOver builds a Client over backend and closes it when the test ends.
func newClientOver(t *testing.T, backend Backend) *Client {
	t.Helper()
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() { _ = c.Close() })
	return c
}

// cancelTriggerBackend cancels the test's context from inside its
// cancelAfter-th call, so a mid-batch cancellation lands deterministically:
// that call runs to completion (CANCELLATION.md section 1.1) and the client's
// per-frame check sees the cancelled context on the next iteration.
type cancelTriggerBackend struct {
	routingBackend
}

func newCancelTriggerBackend(cancelAfter int, cancel context.CancelFunc, resp string) *cancelTriggerBackend {
	b := &cancelTriggerBackend{}
	b.hook = func(n int) (string, error) {
		if n == cancelAfter {
			cancel()
		}
		return resp, nil
	}
	return b
}

// A method called with an already-cancelled context returns the wrapped
// ctx.Err() without reaching the FFI (CANCELLATION.md section 1.1).
func TestClient_CancelAtEntry(t *testing.T) {
	backend := newAnsweringBackend(`{"status":"success"}`)
	c := newClientOver(t, backend)

	cctx, cancel := context.WithCancel(t.Context())
	cancel()

	err := c.SetProperties(cctx, nil)
	if err == nil {
		t.Fatal("expected cancellation error, got nil")
	}
	if !errors.Is(err, context.Canceled) {
		t.Errorf("expected context.Canceled, got %v", err)
	}
	if !strings.HasPrefix(err.Error(), "SetProperties: ") {
		t.Errorf("expected method-prefixed error, got %q", err.Error())
	}
	if backend.callCount() != 0 {
		t.Errorf("FFI was called %d times; the pre-FFI guard did not honor cancellation", backend.callCount())
	}
}

// A caller waiting for the client lock is released by its context, without
// acquiring the lock or reaching the FFI. The test holds the lock itself, as a
// caller inside an FFI call would, so the waiting caller's select has its
// context as the only ready case: the path a cancellation arriving while it
// waits takes. This is why the lock is a channel and not a sync.Mutex, whose
// Lock cannot wait under a context and would block here for good.
func TestClient_CancelWhileWaitingOnLock(t *testing.T) {
	backend := newAnsweringBackend(`{"status":"success"}`)
	c := newClientOver(t, backend)
	c.lockCh <- struct{}{} // held, as by a caller inside an FFI call

	cctx, cancel := context.WithCancel(t.Context())
	cancel()
	err := c.SetProperties(cctx, nil)
	if !errors.Is(err, context.Canceled) {
		t.Errorf("expected context.Canceled, got %v", err)
	}
	if err != nil && !strings.HasPrefix(err.Error(), "SetProperties: ") {
		t.Errorf("expected method-prefixed error, got %q", err.Error())
	}
	if got := backend.callCount(); got != 0 {
		t.Errorf("the waiting caller reached the FFI: callCount=%d", got)
	}
	if held := len(c.lockCh); held != 1 {
		t.Errorf("the waiting caller changed a lock it never took: %d held, want 1", held)
	}

	c.unlock()
	if err := c.SetProperties(t.Context(), nil); err != nil {
		t.Errorf("a call after the lock is released: %v", err)
	}
}

// When the context fires mid-batch, SendFrames returns the committed prefix
// and the wrapped ctx.Err(), and sends no frame after the cancellation point
// (CANCELLATION.md section 3.2).
func TestClient_CancelDuringBatch(t *testing.T) {
	const total = 10
	const cancelAfter = 3

	bctx, cancel := context.WithCancel(t.Context())
	defer cancel()

	backend := newCancelTriggerBackend(cancelAfter, cancel, `{"status":"ack"}`)
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() { _ = c.Close() })

	sid, _ := NewStandardID(0x123)
	dlc, _ := NewDLC(8)
	frames := make([]Frame, total)
	for i := range frames {
		frames[i] = Frame{
			Timestamp: Timestamp{Microseconds: int64(i+1) * 1000},
			ID:        sid,
			DLC:       dlc,
			Data:      FramePayload{0, 0, 0, 0, 0, 0, 0, 0},
		}
	}

	results, err := c.SendFrames(bctx, frames)
	if !errors.Is(err, context.Canceled) {
		t.Fatalf("expected context.Canceled, got %v", err)
	}
	if !strings.HasPrefix(err.Error(), "SendFrames: ") {
		t.Errorf("expected method-prefixed error, got %q", err.Error())
	}
	if len(results) != cancelAfter {
		t.Errorf("commit-prefix length: got %d, want %d (frames before cancellation)", len(results), cancelAfter)
	}
	if got := backend.callCount(); got != cancelAfter {
		t.Errorf("backend hit %d times (want %d, no FFI past cancellation)", got, cancelAfter)
	}
}

// An FFI call already in progress runs to completion when the context fires
// mid-call, and the next call sees the cancellation (CANCELLATION.md
// section 1.1, second clause). The backend cancels the context from inside the
// call, so the cancellation lands while the call is in flight on every run.
func TestClient_NoCancelOnInFlightFFI(t *testing.T) {
	cctx, cancel := context.WithCancel(t.Context())
	backend := newCancelTriggerBackend(1, cancel, `{"status":"success"}`)
	c := newClientOver(t, backend)

	if err := c.SetProperties(cctx, nil); err != nil {
		t.Errorf("the in-flight call did not run to completion: %v", err)
	}
	if cctx.Err() == nil {
		t.Fatal("the backend was never entered, so nothing was cancelled mid-call")
	}
	err := c.SetProperties(cctx, nil)
	if !errors.Is(err, context.Canceled) {
		t.Errorf("expected context.Canceled on the next call, got %v", err)
	}
	if got := backend.callCount(); got != 1 {
		t.Errorf("the call after the cancellation reached the FFI: callCount=%d", got)
	}
}

// An unlock of a lock nobody holds is a defect inside the package, and it
// fails at once instead of turning the defect into a wait a later caller
// inherits. The guide names this fault as the exception to its no-panic
// rule, and the probe over the package holds it to exactly this message.
func TestClient_UnlockNotHeldFails(t *testing.T) {
	c := newClientOver(t, newAnsweringBackend(`{"status":"success"}`))

	recovered := func() (r any) {
		defer func() { r = recover() }()
		c.unlock()
		return nil
	}()

	const want = "aletheia: unlock of a lock that is not held"
	if got := recovered; got != want {
		t.Errorf("unlock of a lock nobody holds: recovered %v, want %q", got, want)
	}
}
