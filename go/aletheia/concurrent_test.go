package aletheia_test

import (
	"sync"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// TestExtractSignals_MockBinaryFallthrough is a regression guard for the
// Mock+DBC parity gap in extractSignalsLocked (R12 H1). After ParseDBC
// populates the signal-name cache, the binary extraction path is exercised
// first — but MockBackend returns ErrBinaryPathUnsupported, which must
// trigger the JSON fallback via ExtractSignalsBinary. Without the fall-
// through, extractSignalsLocked silently returned nil and enrichment
// yielded empty values against MockBackend.
//
// This test exercises the symmetric public entry point ExtractSignals;
// both methods now share the same fall-through pattern, so a parity
// regression here would reproduce the private-method bug.
func TestExtractSignals_MockBinaryFallthrough(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // ParseDBC
		aletheia.Respond(`{
			"status":"success",
			"values":[{"name":"Speed","value":150.0}],
			"errors":[],
			"absent":[]
		}`), // ExtractSignals via JSON fallback
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	// ParseDBC populates signalNames — the binary path is now active.
	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	result, err := c.ExtractSignals(sid, dlc8(), aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0})
	if err != nil {
		t.Fatalf("ExtractSignals fell through to a real failure: %v", err)
	}
	if len(result.Values) != 1 || result.Values[0].Name != "Speed" || result.Values[0].Value != 150.0 {
		t.Errorf("expected Speed=150.0 via JSON fallback, got %+v", result.Values)
	}
}

// TestClient_Concurrent exercises the goroutine-safety guarantee documented in
// doc.go and CLAUDE.md. It fires N worker goroutines issuing AddChecks against
// one Client while a terminator goroutine calls Close repeatedly. The
// MockBackend is preloaded with enough canned success responses to absorb
// every call's JSON exchange — run this with `go test -race` to validate both
// the sync.Mutex serialization and the double-close guarantee.
func TestClient_Concurrent(t *testing.T) {
	const workers = 8
	const iterationsPerWorker = 4
	// Each AddChecks sends one JSON command. Over-provision to avoid mock
	// exhaustion if the scheduler lets several workers race past the closed
	// check before the Close goroutine latches.
	totalResponses := workers*iterationsPerWorker + 16
	responses := make([]aletheia.MockResponse, totalResponses)
	for i := range responses {
		responses[i] = aletheia.Respond(`{"status":"success"}`)
	}
	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}

	checks := []aletheia.CheckResult{
		aletheia.CheckSignal("Speed").NeverExceeds(220),
	}

	var wg sync.WaitGroup
	wg.Add(workers)
	for w := 0; w < workers; w++ {
		go func() {
			defer wg.Done()
			for i := 0; i < iterationsPerWorker; i++ {
				// AddChecks is safe whether the client is open or closed — a
				// closed client returns an *aletheia.Error with ErrState, not
				// a panic. The invariant under test is that the Client never
				// data-races or panics, not that every call succeeds.
				_ = c.AddChecks(checks)
			}
		}()
	}

	// Concurrent Close: repeated calls from a separate goroutine.
	// sync.Once inside Close guarantees the backend state is freed exactly once.
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := 0; i < 4; i++ {
			_ = c.Close()
		}
	}()

	wg.Wait()

	// Terminal Close must still succeed (double-close guarantee).
	if err := c.Close(); err != nil {
		t.Errorf("final Close returned error: %v", err)
	}
}
