// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The cancellation tests live in the package itself so they can implement
// the sealed [Backend] interface and control FFI timing call by call.

import (
	"context"
	"errors"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"
	"unsafe"
)

// routingBackend implements [Backend] by counting every call and handing it
// to one hook with its ordinal. The two doubles below embed it and differ
// only in the hook. Synchronisation is by channels and the scheduler, never
// by wall-clock time: a hang shows as the test binary's timeout.
type routingBackend struct {
	mu    sync.Mutex
	calls int
	hook  func(n int) (string, error)
}

func (*routingBackend) backend() {}

func (b *routingBackend) Init() (unsafe.Pointer, error) {
	var sentinel byte
	return unsafe.Pointer(&sentinel), nil
}

func (b *routingBackend) Process(_ unsafe.Pointer, _ string) (string, error) {
	b.mu.Lock()
	b.calls++
	n := b.calls
	b.mu.Unlock()
	return b.hook(n)
}

func (b *routingBackend) callCount() int {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.calls
}

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

// gateBackend parks every call on a release channel before answering, so a
// test can hold the client lock inside an FFI call for as long as it needs.
// entered closes on the first call, which lets a test wait for the FFI to be
// entered without polling.
type gateBackend struct {
	routingBackend
	release     chan struct{}
	entered     chan struct{}
	enteredOnce sync.Once
	releaseOnce sync.Once // the test and the teardown may both release
	resp        string
}

func newGateBackend(resp string) *gateBackend {
	b := &gateBackend{release: make(chan struct{}), entered: make(chan struct{}), resp: resp}
	b.hook = func(int) (string, error) {
		b.enteredOnce.Do(func() { close(b.entered) })
		// A park with no bound would hang the binary when the test that
		// should release it fails first; a call the tests park is released
		// within a second, so three is the bound of a defect, not a delay.
		select {
		case <-b.release:
			return b.resp, nil
		case <-time.After(3 * time.Second):
			return "", errors.New("gate: the parked call was never released")
		}
	}
	return b
}

// releaseWorker unblocks every call parked on release; safe to call twice.
func (b *gateBackend) releaseWorker() {
	b.releaseOnce.Do(func() { close(b.release) })
}

// newGatedClient builds a Client over a gateBackend and owns its teardown:
// release the worker, then close the client, on any test exit including a
// failing assertion's runtime.Goexit. The order matters, since a call parked
// on release holds the client lock and Close would wait for it. The Python
// gated_backend helper does the same in its finally clause. Tests must not
// add a Close of their own.
func newGatedClient(t *testing.T, resp string) (*Client, *gateBackend) {
	t.Helper()
	backend := newGateBackend(resp)
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() {
		backend.releaseWorker()
		_ = closeWithin(t, c)
	})
	return c, backend
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
	c, backend := newGatedClient(t, `{"status":"success"}`)

	cctx, cancel := context.WithCancel(context.Background())
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

// A goroutine waiting for the client lock is cancelled by its context
// without ever acquiring the lock or reaching the FFI. This is why the lock
// is a channel and not a sync.Mutex, whose Lock cannot wait under a context;
// the test guards against a Mutex that would notice cancellation only after
// acquiring.
func TestClient_CancelWhileWaitingOnLock(t *testing.T) {
	c, backend := newGatedClient(t, `{"status":"success"}`)

	// A takes the lock and parks inside the FFI call until release.
	aDone := make(chan error, 1)
	go func() {
		aDone <- c.SetProperties(context.Background(), nil)
	}()
	recvWithin(t, backend.entered)

	// B queues on the lock under a cancellable context.
	bctx, cancelB := context.WithCancel(context.Background())
	bDone := make(chan error, 1)
	go func() {
		bDone <- c.SetProperties(bctx, nil)
	}()

	// lockWaiters counts goroutines inside the lock's select; A is past it,
	// so a count of one means B is parked. Gosched yields without sleeping.
	for c.lockWaiters.Load() < 1 {
		runtime.Gosched()
	}

	cancelB()

	err := recvWithin(t, bDone)
	if !errors.Is(err, context.Canceled) {
		t.Errorf("B: expected context.Canceled, got %v", err)
	}
	if !strings.HasPrefix(err.Error(), "SetProperties: ") {
		t.Errorf("B: expected method-prefixed error, got %q", err.Error())
	}
	if got := backend.callCount(); got != 1 {
		t.Errorf("B reached the FFI: callCount=%d (want 1, only A)", got)
	}

	backend.releaseWorker()
	if err := recvWithin(t, aDone); err != nil {
		t.Errorf("A: unexpected error %v", err)
	}
}

// When the context fires mid-batch, SendFrames returns the committed prefix
// and the wrapped ctx.Err(), and sends no frame after the cancellation point
// (CANCELLATION.md section 3.2).
func TestClient_CancelDuringBatch(t *testing.T) {
	const total = 10
	const cancelAfter = 3

	bctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	backend := newCancelTriggerBackend(cancelAfter, cancel, `{"status":"ack"}`)
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() { _ = closeWithin(t, c) })

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
// section 1.1, second clause).
func TestClient_NoCancelOnInFlightFFI(t *testing.T) {
	c, backend := newGatedClient(t, `{"status":"success"}`)

	cctx, cancel := context.WithCancel(context.Background())

	done := make(chan error, 1)
	go func() {
		done <- c.SetProperties(cctx, nil)
	}()
	recvWithin(t, backend.entered)

	cancel()

	// Yield so a goroutine that wrongly returned on cancellation gets the
	// chance to write done before the non-blocking check below.
	for range 8 {
		runtime.Gosched()
	}
	select {
	case err := <-done:
		t.Fatalf("call returned before release; cancellation is not cooperative at the FFI boundary: err=%v", err)
	default:
	}

	backend.releaseWorker()
	if err := recvWithin(t, done); err != nil {
		t.Errorf("expected nil error from the completed in-flight call, got %v", err)
	}

	err := c.SetProperties(cctx, nil)
	if !errors.Is(err, context.Canceled) {
		t.Errorf("expected context.Canceled on the next call, got %v", err)
	}
}

// An unlock of a lock nobody holds is a defect inside the package, and it
// fails at once instead of turning the defect into a wait a later caller
// inherits. The guide names this fault as the exception to its no-panic
// rule, and the probe over the package holds it to exactly this message.
func TestClient_UnlockNotHeldFails(t *testing.T) {
	c, _ := newGatedClient(t, `{"status":"success"}`)

	// On a goroutine, so an unlock that blocks fails the bounded wait rather
	// than running to the test deadline.
	recovered := make(chan any, 1)
	go func() {
		defer func() { recovered <- recover() }()
		c.unlock()
	}()

	const want = "aletheia: unlock of a lock that is not held"
	if got := recvWithin(t, recovered); got != want {
		t.Errorf("unlock of a lock nobody holds: recovered %v, want %q", got, want)
	}
}
