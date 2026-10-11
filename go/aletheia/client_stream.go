// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"errors"
	"fmt"
	"iter"
	"log/slog"
	"slices"
)

// --- Signal operations ---

// ExtractSignals decodes all signals from a CAN frame using the loaded DBC.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) ExtractSignals(ctx context.Context, id CANID, dlc DLC, data FramePayload) (*ExtractionResult, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "ExtractSignals")
	defer release()
	if err != nil {
		return nil, err
	}

	// The binary path once the signal-name cache holds the ID; only
	// ErrBinaryPathUnsupported (the MockBackend) falls back to JSON, any
	// other error propagates, as in Python's commit-to-binary contract.
	key := canIDKey(id)
	if names, ok := c.signalNames[key]; ok {
		buf, err := c.backend.ExtractSignalsBin(c.state, id, dlc, []byte(data))
		if err == nil {
			return parseExtractionBin(buf, names)
		}
		if !errors.Is(err, ErrBinaryPathUnsupported) {
			return nil, err
		}
	}

	// Fallback: JSON path.
	resp, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, []byte(data))
	if err != nil {
		return nil, err
	}
	return parseExtractionResponse(resp)
}

// BuildFrame encodes signal values into a CAN frame payload.
// Requires a prior ParseDBC call to populate the signal index.
//
// The argument order (id, dlc, signals) is UpdateFrame's and the Python and
// C++ bindings' build_frame(id, dlc, signals).
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) BuildFrame(ctx context.Context, id CANID, dlc DLC, signals []SignalValue) (FramePayload, error) {
	release, err := c.acquire(ctx, "BuildFrame")
	defer release()
	if err != nil {
		return nil, err
	}
	injections, err := c.resolveInjections(signals, id, "BuildFrame")
	if err != nil {
		return nil, err
	}
	payload, err := c.backend.BuildFrameBin(c.state, id, dlc, injections)
	if err != nil {
		return nil, err
	}
	return FramePayload(payload), nil
}

// UpdateFrame modifies specific signals in an existing CAN frame.
// Requires a prior ParseDBC call to populate the signal index.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) UpdateFrame(ctx context.Context, id CANID, dlc DLC, data FramePayload, signals []SignalValue) (FramePayload, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "UpdateFrame")
	defer release()
	if err != nil {
		return nil, err
	}
	injections, err := c.resolveInjections(signals, id, "UpdateFrame")
	if err != nil {
		return nil, err
	}
	payload, err := c.backend.UpdateFrameBin(c.state, id, dlc, []byte(data), injections)
	if err != nil {
		return nil, err
	}
	return FramePayload(payload), nil
}

// --- Streaming LTL operations ---
//
// Expected call sequence: SetProperties → StartStream → SendFrame* → EndStream.
// StartStream resets the extraction cache and last-frame tracking.
// SetProperties may be called again after EndStream to install new properties.

// SetProperties installs LTL properties for stream monitoring.
// Automatically derives diagnostic metadata from the formula structure for
// violation enrichment.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SetProperties(ctx context.Context, properties []Formula) error {
	props := make([]map[string]any, 0, len(properties))
	for _, f := range properties {
		m, err := serializeFormula(f)
		if err != nil {
			return err
		}
		props = append(props, m)
	}
	cmd, err := serializeCommand("setProperties", map[string]any{
		"properties": props,
	})
	if err != nil {
		return err
	}
	// Hold lock for both the backend call and the diagnostics update
	// to prevent SendFrame from seeing stale diags between the two.
	release, err := c.acquire(ctx, "SetProperties")
	defer release()
	if err != nil {
		return err
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	// Build into a temp slice first: buildDiagnostic renders predicate
	// thresholds via the kernel and fails if the GHC runtime is not up (a
	// mock-backend client with no FFIBackend), so a failure must not leave
	// c.diags half-populated.
	diags := make([]PropertyDiagnostic, len(properties))
	for i, f := range properties {
		d, err := buildDiagnostic(f)
		if err != nil {
			return err
		}
		diags[i] = d
	}
	c.diags = diags
	c.cache = newExtractCache()
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelInfo, "properties.set",
			slog.Int("count", len(properties)))
	}
	return nil
}

// AddChecks extracts formulas from the given checks, prepends any default checks
// set via WithDefaultChecks, and calls SetProperties.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) AddChecks(ctx context.Context, checks []CheckResult) error {
	all := make([]Formula, 0, len(c.defaultChecks)+len(checks))
	for _, dc := range c.defaultChecks {
		all = append(all, dc.Formula())
	}
	for _, ch := range checks {
		all = append(all, ch.Formula())
	}
	return c.SetProperties(ctx, all)
}

// StartStream begins a new LTL monitoring stream.
// SetProperties must be called before StartStream.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) StartStream(ctx context.Context) error {
	// Hold lock for both the backend call and the cache clear
	// to prevent SendFrame from using a stale cache.
	release, err := c.acquire(ctx, "StartStream")
	defer release()
	if err != nil {
		return err
	}
	resp, err := c.backend.StartStreamBinary(c.state)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	if c.cache != nil {
		c.cache.clear()
	}
	// Track last frames only when diagnostics are set — lastFrames feeds EOS
	// enrichment, which requires diags. Matches Python's conditional tracking.
	if c.diags != nil {
		c.lastFrames = make(map[uint64]lastFrameData)
	} else {
		c.lastFrames = nil
	}
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelInfo, "stream.started")
	}
	return nil
}

// SendFrame sends a CAN frame to the active monitoring stream.
// Returns Ack or Violation depending on whether any property was violated.
// Violations are automatically enriched with signal values and a human-readable
// formula description when diagnostics are available.
// For batch operations, see [Client.SendFrames].
//
// CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are
// passed as *bool — pass nil for CAN 2.0B frames where the bits do
// not exist on the wire.  The Aletheia kernel does not consume
// BRS / ESI; they are pass-through metadata for binding consumers
// and the JSON wire shape.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendFrame(
	ctx context.Context, ts Timestamp,
	id CANID, dlc DLC, data FramePayload,
	brs *bool, esi *bool,
) (FrameResponse, error) {
	release, err := c.acquire(ctx, "SendFrame")
	defer release()
	if err != nil {
		return nil, err
	}
	return c.sendFrameLocked(ctx, ts, id, dlc, data, brs, esi)
}

// SendFrames sends multiple CAN frames in a single batch, amortizing lock
// acquisition. The batch is atomic: no other goroutine can interleave frames
// between members. Returns a response for each frame. A [Violation] is a normal
// response and does not stop the batch. Processing stops at the first transport
// or validation error; earlier successful responses are still returned.
//
// Honors ctx cancellation at frame boundaries (commit-prefix-and-report per
// CANCELLATION.md §3.2): if ctx fires mid-batch, the returned slice contains
// the responses for the committed prefix and the wrapped ctx.Err() is the
// returned error. The remaining frames after the cancellation point are NOT
// sent to the FFI; the caller can resume by re-calling SendFrames with the
// uncommitted suffix.
func (c *Client) SendFrames(ctx context.Context, frames []Frame) ([]FrameResponse, error) {
	release, err := c.acquire(ctx, "SendFrames")
	defer release()
	if err != nil {
		return nil, err
	}
	results := make([]FrameResponse, 0, len(frames))
	for i, f := range frames {
		// Per-frame ctx check between FFI calls — the cancellation
		// boundary in batch mode. The most recent FFI call (if one was
		// in flight when ctx fired) ran to completion and was appended.
		if err := ctx.Err(); err != nil {
			return results, fmt.Errorf("SendFrames: %w", err)
		}
		resp, err := c.sendFrameLocked(ctx, f.Timestamp, f.ID, f.DLC, f.Data, f.BRS, f.ESI)
		if err != nil {
			return results, fmt.Errorf("SendFrames frame %d: %w", i, err)
		}
		results = append(results, resp)
	}
	return results, nil
}

// SendFramesSeq sends frames lazily, yielding one (FrameResponse, error) pair
// per frame as the returned [iter.Seq2] is ranged. It is the streaming variant
// of [Client.SendFrames] — the same relationship as strings.SplitSeq to
// strings.Split — and the Go analogue of Python's send_frames_iter.
//
// Use it when the source is a live producer (a channel, a socket, a log
// reader): frames are pulled from the input one at a time and each response is
// yielded immediately, so neither the full input slice nor the full response
// slice is ever materialized. Wrap an existing slice with slices.Values:
//
//	for resp, err := range client.SendFramesSeq(ctx, slices.Values(frames)) {
//		if err != nil { /* handle; iteration has stopped */ break }
//		_ = resp
//	}
//
// Contract (commit-prefix-and-report, per CANCELLATION.md §3.2): each yielded
// (resp, nil) is a frame already committed to the stream state — durable, not
// rolled back. On the first failing frame the sequence yields (nil, err) once
// and then ends; no frame after a failure is sent. Cancellation is the standard
// range protocol: break the loop (or let ctx fire) and the remaining frames are
// never sent, while every pair already yielded stays committed.
//
// The returned sequence is SINGLE-USE: range it exactly once. Unlike
// strings.SplitSeq (pure, so harmless to re-range), this sends to a stateful
// stream — ranging the same returned value twice would re-send the frames and
// corrupt the stream. The peer bindings are single-use by construction (a
// consumed Iterator/Stream/generator); Go's iter.Seq2 is a re-invocable
// closure, so this is a caller obligation rather than a type guarantee.
//
// Locking differs from SendFrames deliberately: SendFrames holds the client
// lock for the whole batch (atomic — no goroutine can interleave). This form
// acquires and releases per frame, never across a yield, because the consumer
// paces the stream and holding the lock across arbitrary consumer code would
// starve Close and any concurrent caller for an unbounded time (matching
// Python's per-frame-locked lazy form). Consequently another goroutine's call
// may interleave between this stream's frames; a single stream is sequential, so
// concurrent streaming on one client is already a misuse.
func (c *Client) SendFramesSeq(ctx context.Context, frames iter.Seq[Frame]) iter.Seq2[FrameResponse, error] {
	return func(yield func(FrameResponse, error) bool) {
		i := 0
		for f := range frames {
			// Per-frame acquire (ctx-aware) and release, both inside the closure,
			// which returns, so the release runs, BEFORE the yield: the lock is
			// never held across consumer code (the 1-deep semaphore would
			// deadlock a re-entrant consumer and starve Close otherwise). The
			// release is deferred, so a panic between the acquire and the FFI
			// return cannot leak the semaphore either.
			resp, err := func() (FrameResponse, error) {
				release, err := c.acquire(ctx, "SendFramesSeq")
				defer release()
				if err != nil {
					return nil, err // acquire has named the method
				}
				resp, err := c.sendFrameLocked(ctx, f.Timestamp, f.ID, f.DLC, f.Data, f.BRS, f.ESI)
				if err != nil {
					return nil, fmt.Errorf("SendFramesSeq frame %d: %w", i, err)
				}
				return resp, nil
			}()
			if err != nil {
				yield(nil, err)
				return
			}
			if !yield(resp, nil) {
				return // the consumer stopped; the remaining frames are never sent
			}
			i++
		}
	}
}

// SendError sends a CAN error event (no ID, no payload). Error frames signal
// a bus error detected by a CAN controller and are acknowledged without LTL
// evaluation — they carry no payload for signal extraction.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendError(ctx context.Context, ts Timestamp) error {
	release, err := c.acquire(ctx, "SendError")
	defer release()
	if err != nil {
		return err
	}
	if err := ts.validate(); err != nil {
		return err
	}
	resp, err := c.backend.SendErrorBinary(c.state, ts)
	if err != nil {
		return err
	}
	if err := parseEventAck(resp); err != nil {
		return err
	}
	if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
		c.logger.LogAttrs(ctx, slog.LevelDebug, "error_event.sent",
			slog.Int64("ts", ts.Microseconds), slog.String("response", "ack"))
	}
	return nil
}

// SendRemote sends a CAN remote frame event (ID but no payload). Remote frames
// request transmission of the data frame with a matching ID (CAN 2.0B only;
// deprecated in CAN-FD). Acknowledged without LTL evaluation.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendRemote(ctx context.Context, ts Timestamp, id CANID) error {
	release, err := c.acquire(ctx, "SendRemote")
	defer release()
	if err != nil {
		return err
	}
	if err := ts.validate(); err != nil {
		return err
	}
	resp, err := c.backend.SendRemoteBinary(c.state, ts, id)
	if err != nil {
		return err
	}
	if err := parseEventAck(resp); err != nil {
		return err
	}
	if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
		c.logger.LogAttrs(ctx, slog.LevelDebug, "remote_event.sent",
			slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
			slog.Bool("extended", id.IsExtended()), slog.String("response", "ack"))
	}
	return nil
}

// sendFrameLocked is SendFrame under the lock the caller holds; ctx reaches
// slog so request-scoped attributes land in the records.
func (c *Client) sendFrameLocked(
	ctx context.Context, ts Timestamp,
	id CANID, dlc DLC, data FramePayload,
	brs *bool, esi *bool,
) (FrameResponse, error) {
	if err := ts.validate(); err != nil {
		return nil, err
	}
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	resp, err := c.backend.SendFrameBinary(c.state, ts, id, dlc, []byte(data), brs, esi)
	if err != nil {
		return nil, err
	}
	fr, err := parseFrameResponse(resp)
	if err != nil {
		return nil, err
	}
	// The last frame per CAN ID feeds end-of-stream enrichment; the payload
	// is copied so the caller's later writes cannot reach it.
	if c.lastFrames != nil {
		dataCopy := make(FramePayload, len(data))
		copy(dataCopy, data)
		c.lastFrames[canIDKey(id)] = lastFrameData{id: id, dlc: dlc, data: dataCopy}
	}
	// A PropertyBatch carries mid-stream satisfactions and at most one
	// terminal violation; every failing entry is enriched from this frame
	// through the cached per-frame extraction, not from the last-seen
	// frames the end-of-stream path uses.
	if b, ok := fr.(PropertyBatch); ok && c.diags != nil {
		for i := range b.Results {
			if b.Results[i].Verdict == Fails {
				c.enrichStreamingViolation(ctx, &b.Results[i], id, dlc, data)
			}
		}
		fr = b
	}
	if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
		response := "ack"
		if b, ok := fr.(PropertyBatch); ok {
			response = "satisfaction"
			if slices.ContainsFunc(b.Results, func(r PropertyResult) bool { return r.Verdict == Fails }) {
				response = "violation"
			}
		}
		c.logger.LogAttrs(ctx, slog.LevelDebug, "frame.processed",
			slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
			slog.Bool("extended", id.IsExtended()), slog.String("response", response))
	}
	return fr, nil
}

// EndStream finalizes the monitoring stream and returns verdicts for all properties.
// Failed and Unresolved verdicts are enriched with signal names, formula description,
// and the most recent signal values per CAN ID when available. Earlier frames in the
// stream are not retained.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) EndStream(ctx context.Context) (*StreamResult, error) {
	release, err := c.acquire(ctx, "EndStream")
	defer release()
	if err != nil {
		return nil, err
	}
	resp, err := c.backend.EndStreamBinary(c.state)
	if err != nil {
		return nil, err
	}
	sr, err := parseStreamResponse(resp)
	if err != nil {
		return nil, err
	}
	c.enrichEndOfStream(ctx, sr.Results)
	c.lastFrames = nil
	if c.logger != nil {
		for _, w := range sr.Warnings {
			if w.Kind == "uncached_atom" {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "endstream.uncached_atom",
					slog.Int("property_index", w.PropertyIndex),
					slog.String("detail", w.Detail))
			}
		}
		numFails, numUnresolved := 0, 0
		for _, r := range sr.Results {
			switch r.Verdict {
			case Fails:
				numFails++
			case Unresolved:
				numUnresolved++
			}
		}
		c.logger.LogAttrs(ctx, slog.LevelInfo, "stream.ended",
			slog.Int("numResults", len(sr.Results)),
			slog.Int("numFails", numFails),
			slog.Int("numUnresolved", numUnresolved),
			slog.Int("numWarnings", len(sr.Warnings)))
	}
	return sr, nil
}
