package aletheia

// Cancellation tests live in the internal package so they can implement the
// sealed [Backend] interface for fine-grained control over FFI timing.
// External-package callers cannot do this — the seal is intentional.

import (
	"context"
	"errors"
	"strings"
	"sync"
	"testing"
	"time"
	"unsafe"
)

// gateBackend is a minimal Backend used to drive cancellation tests. Each
// method that the tests exercise blocks on a release channel before returning
// a canned response, allowing the test to hold the client lock for as long as
// needed. The struct also records how many times Process was hit so the test
// can assert "the cancelled goroutine never reached the FFI."
type gateBackend struct {
	mu      sync.Mutex
	calls   int
	release chan struct{}
	resp    string
}

func newGateBackend(resp string) *gateBackend {
	return &gateBackend{
		release: make(chan struct{}),
		resp:    resp,
	}
}

func (*gateBackend) backend() {}

func (b *gateBackend) Init() (unsafe.Pointer, error) {
	var sentinel byte
	return unsafe.Pointer(&sentinel), nil
}

func (b *gateBackend) Process(_ unsafe.Pointer, _ string) (string, error) {
	b.mu.Lock()
	b.calls++
	b.mu.Unlock()
	<-b.release
	return b.resp, nil
}

func (b *gateBackend) callCount() int {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.calls
}

// All other Backend methods route to Process so the gate-and-count semantics
// apply uniformly. Tests only need a couple of these — the rest exist to
// satisfy the interface.
func (b *gateBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CanID, _ DLC, _ []byte) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CanID) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) StartStreamBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) EndStreamBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) FormatDbcBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) ExtractSignalsBinary(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) (string, error) {
	return b.Process(nil, "")
}
func (b *gateBackend) BuildFrameBin(_ unsafe.Pointer, _ CanID, _ DLC, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	_, _ = b.Process(nil, "")
	return nil, nil
}
func (b *gateBackend) UpdateFrameBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	_, _ = b.Process(nil, "")
	return nil, nil
}
func (b *gateBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) ([]byte, error) {
	return nil, ErrBinaryPathUnsupported
}
func (b *gateBackend) Close(_ unsafe.Pointer) {}

// TestClient_CancelAtEntry verifies the pre-FFI guard: a method called with
// an already-cancelled context returns the wrapped ctx.Err() without making
// the FFI call. This is CANCELLATION.md §1.1 at its most direct.
func TestClient_CancelAtEntry(t *testing.T) {
	backend := newGateBackend(`{"status":"success"}`)
	defer close(backend.release)

	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer c.Close()

	cctx, cancel := context.WithCancel(context.Background())
	cancel() // cancel BEFORE the call

	err = c.SetProperties(cctx, nil)
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
		t.Errorf("FFI was called %d times — pre-FFI guard did not honor cancellation", backend.callCount())
	}
}

// TestClient_CancelWhileWaitingOnLock verifies the load-bearing behavior of
// the channel-based semaphore (the reason it replaced sync.Mutex): a goroutine
// waiting for the client lock can be cancelled by its context.Context without
// ever acquiring the lock or hitting the FFI.
//
// sync.Mutex.Lock has no native ctx-aware variant — a Mutex-based design would
// force the waiter to acquire the lock first, and only then notice cancellation
// at a post-lock check. This test specifically guards against regressing to
// that behavior.
func TestClient_CancelWhileWaitingOnLock(t *testing.T) {
	backend := newGateBackend(`{"status":"success"}`)
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer c.Close()

	// Goroutine A: holds the lock by sitting inside backend.Process, which
	// blocks on `release` until the test fires it. SetProperties takes the
	// client lock and stays inside the FFI call until release.
	aDone := make(chan error, 1)
	aReached := make(chan struct{}) // closed once A's FFI call has been entered
	go func() {
		// We need to know when A is INSIDE the Process call (and therefore
		// holds the client lock). Detect that by polling backend.calls;
		// AddChecks → SetProperties → processLocked → backend.Process is the
		// path, and Process records its entry before blocking on `release`.
		aDone <- c.SetProperties(context.Background(), nil)
	}()
	deadline := time.Now().Add(2 * time.Second)
	for backend.callCount() == 0 && time.Now().Before(deadline) {
		time.Sleep(time.Millisecond)
	}
	if backend.callCount() == 0 {
		t.Fatal("goroutine A never reached the backend — test setup broken")
	}
	close(aReached)
	// At this point A holds the client lock and is blocked inside Process.

	// Goroutine B: tries to acquire the lock under a cancellable ctx.
	// The lock is held, so B will queue on lockCh's send branch.
	bctx, cancelB := context.WithCancel(context.Background())
	bDone := make(chan error, 1)
	go func() {
		bDone <- c.SetProperties(bctx, nil)
	}()

	// Give B time to start blocking on the lock. (We can't deterministically
	// detect "blocked on a channel send" without instrumentation, but a
	// short sleep is plenty for the scheduler to park the goroutine.)
	time.Sleep(50 * time.Millisecond)

	// Cancel B's context while it's still waiting on the lock.
	cancelB()

	// B must return promptly with the wrapped ctx error.
	select {
	case err := <-bDone:
		if !errors.Is(err, context.Canceled) {
			t.Errorf("B: expected context.Canceled, got %v", err)
		}
		if !strings.HasPrefix(err.Error(), "SetProperties: ") {
			t.Errorf("B: expected method-prefixed error, got %q", err.Error())
		}
	case <-time.After(2 * time.Second):
		t.Fatal("B: did not return after ctx cancellation — lock acquisition is not ctx-aware")
	}

	// B must NEVER have hit the FFI (callCount stays at 1 — A's call only).
	if got := backend.callCount(); got != 1 {
		t.Errorf("B reached the FFI: callCount=%d (want 1, only A)", got)
	}

	// Release A and let it complete.
	close(backend.release)
	select {
	case err := <-aDone:
		if err != nil {
			t.Errorf("A: unexpected error %v", err)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("A: never returned after release")
	}
}

// cancelTriggerBackend fires ctx cancellation from inside Process at the
// configured call number, so tests can deterministically force a mid-batch
// cancellation. The cancellation hits while the FFI call is "in flight" —
// per §1.1 the call still runs to completion, and the per-iteration ctx.Err()
// guard catches the cancellation on the NEXT iteration.
type cancelTriggerBackend struct {
	mu          sync.Mutex
	calls       int
	cancelAfter int
	cancel      context.CancelFunc
	resp        string
}

func (*cancelTriggerBackend) backend() {}

func (b *cancelTriggerBackend) Init() (unsafe.Pointer, error) {
	var sentinel byte
	return unsafe.Pointer(&sentinel), nil
}

func (b *cancelTriggerBackend) Process(_ unsafe.Pointer, _ string) (string, error) {
	b.mu.Lock()
	b.calls++
	n := b.calls
	b.mu.Unlock()
	if n == b.cancelAfter {
		b.cancel()
	}
	return b.resp, nil
}

func (b *cancelTriggerBackend) callCount() int {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.calls
}

func (b *cancelTriggerBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CanID, _ DLC, _ []byte) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CanID) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) StartStreamBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) EndStreamBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) FormatDbcBinary(_ unsafe.Pointer) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) ExtractSignalsBinary(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) (string, error) {
	return b.Process(nil, "")
}
func (b *cancelTriggerBackend) BuildFrameBin(_ unsafe.Pointer, _ CanID, _ DLC, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	_, _ = b.Process(nil, "")
	return nil, nil
}
func (b *cancelTriggerBackend) UpdateFrameBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	_, _ = b.Process(nil, "")
	return nil, nil
}
func (b *cancelTriggerBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) ([]byte, error) {
	return nil, ErrBinaryPathUnsupported
}
func (b *cancelTriggerBackend) Close(_ unsafe.Pointer) {}

// TestClient_CancelDuringBatch verifies CANCELLATION.md §3.2 commit-prefix-
// and-report: when ctx fires mid-batch, the returned slice contains the
// committed prefix and the wrapped ctx.Err() is the returned error. The
// remaining frames after the cancellation point are not sent to the FFI.
//
// Determinism comes from a backend that fires ctx cancellation from INSIDE
// the cancelAfter-th Process call. By contract, that in-flight call runs to
// completion (§1.1); the per-iteration guard catches the cancelled ctx at
// the start of the NEXT iteration, returning a `cancelAfter`-frame committed
// prefix.
func TestClient_CancelDuringBatch(t *testing.T) {
	const total = 10
	const cancelAfter = 3

	bctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	backend := &cancelTriggerBackend{
		cancelAfter: cancelAfter,
		cancel:      cancel,
		resp:        `{"status":"ack"}`,
	}
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer c.Close()

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
		t.Errorf("backend hit %d times (want %d — no FFI past cancellation)", got, cancelAfter)
	}
}

// TestClient_NoCancelOnInFlightFFI verifies CANCELLATION.md §1.1 second
// clause: an FFI call already in progress runs to completion when ctx fires
// mid-call. The next call sees the cancellation.
func TestClient_NoCancelOnInFlightFFI(t *testing.T) {
	backend := newGateBackend(`{"status":"success"}`)
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer c.Close()

	cctx, cancel := context.WithCancel(context.Background())

	// Start the call; backend.Process blocks on `release`.
	done := make(chan error, 1)
	go func() {
		done <- c.SetProperties(cctx, nil)
	}()

	// Wait for the FFI to be entered.
	deadline := time.Now().Add(2 * time.Second)
	for backend.callCount() == 0 && time.Now().Before(deadline) {
		time.Sleep(time.Millisecond)
	}
	if backend.callCount() == 0 {
		t.Fatal("FFI never entered — test setup broken")
	}

	// Fire cancellation mid-FFI. The call must NOT abort.
	cancel()
	time.Sleep(20 * time.Millisecond) // give the cancellation time to "do nothing"

	select {
	case err := <-done:
		t.Fatalf("call returned before release — cooperative-at-FFI-boundaries violated: err=%v", err)
	default:
		// Good — call still running.
	}

	// Release. The call returns its real result with nil error (no propagation
	// of the cancellation; the in-flight call ran to completion).
	close(backend.release)

	select {
	case err := <-done:
		if err != nil {
			t.Errorf("expected nil error from completed in-flight call, got %v", err)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("call never returned after release")
	}

	// Subsequent call honors the cancellation (cancelled ctx is sticky).
	err = c.SetProperties(cctx, nil)
	if !errors.Is(err, context.Canceled) {
		t.Errorf("expected context.Canceled on next call, got %v", err)
	}
}
