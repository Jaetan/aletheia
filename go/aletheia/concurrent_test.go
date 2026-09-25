//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"errors"
	"sync"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// Workers issue AddChecks against one client while another goroutine closes
// it repeatedly. The guarantee under test is the one the Client documentation
// states: the client never races or panics, a call on the closed client
// returns a state error, the session is freed once, and the last Close still
// returns nil. The race detector is the judge, so the suite runs under -race.
// A call that reaches the backend renders its check's diagnostic through the
// kernel, so the test needs the kernel as -race needs cgo.
func TestClient_Concurrent(t *testing.T) {
	ctx := bounded(t)
	const workers = 8
	const iterationsPerWorker = 4
	// one JSON command per AddChecks, with slack for calls that overtake Close
	responses := make([]aletheia.MockResponse, workers*iterationsPerWorker+16)
	for i := range responses {
		responses[i] = aletheia.Respond(`{"status":"success"}`)
	}
	c, err := aletheia.NewClient(aletheia.NewMockBackend(responses...))
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	checks := []aletheia.CheckResult{aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))}

	errs := make(chan error, workers*iterationsPerWorker)
	var wg sync.WaitGroup
	for range workers {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for range iterationsPerWorker {
				errs <- c.AddChecks(ctx, checks)
			}
		}()
	}
	wg.Add(1)
	go func() {
		defer wg.Done()
		for range 4 {
			_ = closeWithin(t, c)
		}
	}()
	wg.Wait()
	close(errs)

	for err := range errs {
		if err == nil {
			continue
		}
		var e *aletheia.Error
		if !errors.As(err, &e) || e.Kind != aletheia.ErrState {
			t.Errorf("a call on the closing client returned %v, want a state error or nil", err)
		}
	}
	if err := closeWithin(t, c); err != nil {
		t.Errorf("final Close returned error: %v", err)
	}
}
