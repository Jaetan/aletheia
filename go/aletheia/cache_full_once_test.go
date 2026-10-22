//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// cache.full is one warning per fill of the extraction cache: on the first
// frame past its bound, not on every frame after, and once more after a new
// stream empties the cache.

package aletheia_test

import (
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

func TestCacheFull_FiresOncePerFill(t *testing.T) {
	const bound = aletheia.MaxExtractCache
	var responses []aletheia.MockResponse
	queueFrames := func(n int) {
		for i := range n {
			responses = append(responses, violationAt(int64(i)+1, "core"), extractionOf("Speed", 245))
		}
	}
	queueFrames(bound + 2)
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // the second StartStream
	queueFrames(bound + 1)
	logOpt, buf := warnLog()
	c, _ := startedClientOpts(t, []aletheia.Formula{speedBelow220}, responses, logOpt)

	// Bytes 0 and 1 make each payload a new cache key.
	send := func(i int) { sendFrame(t, c, int64(i)+1, byte(i), byte(i>>8), 0, 0, 0, 0, 0, 0) }
	fulls := func() int { return strings.Count(buf.String(), "cache.full") }

	for i := range bound {
		send(i)
	}
	if n := fulls(); n != 0 {
		t.Fatalf("cache.full fired %d times before the cache was full", n)
	}
	send(bound)
	if n := fulls(); n != 1 {
		t.Fatalf("cache.full fired %d times on the first frame past the bound, want 1", n)
	}
	send(bound + 1)
	if n := fulls(); n != 1 {
		t.Errorf("cache.full fired %d times over two frames past the bound, want 1", n)
	}
	if err := c.StartStream(t.Context()); err != nil {
		t.Fatal(err)
	}
	for i := range bound + 1 {
		send(i)
	}
	if n := fulls(); n != 2 {
		t.Errorf("cache.full fired %d times over two fills, want 2", n)
	}
	if !strings.Contains(buf.String(), "size=256") {
		t.Errorf("cache.full carries no size=256 field: %s", buf.String())
	}
}
