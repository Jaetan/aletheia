// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"errors"
	"log/slog"
	"maps"
	"slices"
)

// enrichStreamingViolation attaches a ViolationEnrichment to a failing
// entry of a PropertyBatch from the current frame's payload, through the
// cached extraction of extractSignalValues. The property index is read
// directly, the kernel proving it below the number of properties
// SetProperties installed. A refused extraction is returned. Caller holds the
// client lock.
func (c *Client) enrichStreamingViolation(ctx context.Context, pr *PropertyResult, id CANID, dlc DLC, data FramePayload) error {
	diag := c.diags[pr.PropertyIndex]
	values, err := c.extractSignalValues(ctx, diag, id, dlc, data)
	if err != nil {
		return err
	}
	reason := formatEnrichedReason(diag, values, pr.Reason)
	pr.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     pr.Reason,
	}
	return nil
}

// enrichEndOfStream adds a ViolationEnrichment to every Fails/Unresolved
// result, extracting each last-seen frame at most once per EndStream (the
// uniform cross-binding extract-once shape).
//
// Three passes: collect the results to enrich, each property index read
// directly, the kernel proving it below the number of properties
// SetProperties installed; extract the last-seen frames for the signals any
// collected diagnostic wants ([Client.extractLastFrames]); then distribute
// the merged values to each result, filtered to the signals its own
// diagnostic references. A refused frame extraction is returned. A result
// whose signals have no value still gets an enrichment with the
// formula-description fallback reason.
//
// Caller must hold the client lock.  ctx is forwarded to slog so
// request-scoped attrs propagate into structured-log records.
func (c *Client) enrichEndOfStream(ctx context.Context, results []PropertyResult) error {
	if len(c.diags) == 0 {
		return nil
	}
	type pending struct {
		pr   *PropertyResult
		diag PropertyDiagnostic
	}
	var todo []pending
	for i := range results {
		pr := &results[i]
		if pr.Verdict != Fails && pr.Verdict != Unresolved {
			continue
		}
		todo = append(todo, pending{pr: pr, diag: c.diags[pr.PropertyIndex]})
	}
	if len(todo) == 0 {
		return nil
	}
	// Union of signal names wanted by any pending diagnostic.
	wanted := make(map[SignalName]bool)
	for _, p := range todo {
		for _, s := range p.diag.Signals {
			wanted[s] = true
		}
	}
	merged, err := c.extractLastFrames(ctx, wanted)
	if err != nil {
		return err
	}
	for _, p := range todo {
		var values map[SignalName]Rational
		for _, sig := range p.diag.Signals {
			if val, ok := merged[sig]; ok {
				if values == nil {
					values = make(map[SignalName]Rational)
				}
				values[sig] = val
			}
		}
		p.pr.Enrichment = &ViolationEnrichment{
			Signals:        values,
			FormulaDesc:    p.diag.FormulaDesc,
			EnrichedReason: formatEnrichedReason(p.diag, values, p.pr.Reason),
			CoreReason:     p.pr.Reason,
		}
	}
	return nil
}

// extractLastFrames extracts the last-seen frames in key order, for a
// deterministic merge, until every wanted signal has a value, merging
// first-frame-wins; wanted is emptied as the values arrive, and a pass that
// starts with it empty extracts nothing. A refused extraction is returned.
// Caller holds the client lock.
func (c *Client) extractLastFrames(ctx context.Context, wanted map[SignalName]bool) (map[SignalName]Rational, error) {
	merged := make(map[SignalName]Rational)
	for _, k := range slices.SortedFunc(maps.Keys(c.lastFrames), compareFrameKeys) {
		if len(wanted) == 0 {
			return merged, nil
		}
		lf := c.lastFrames[k]
		result, err := c.extractSignalsLocked(ctx, lf.id, lf.dlc, lf.data)
		if err != nil {
			return nil, err
		}
		for _, sv := range result.Values {
			if _, ok := merged[sv.Name]; !ok {
				merged[sv.Name] = sv.Value
			}
			delete(wanted, sv.Name)
		}
	}
	return merged, nil
}

// extractSignalValues extracts the signals a diagnostic names from a frame,
// through the cache; a refused extraction is returned and not cached. Caller
// holds the client lock.
func (c *Client) extractSignalValues(ctx context.Context, diag PropertyDiagnostic, id CANID, dlc DLC, data FramePayload) (map[SignalName]Rational, error) {
	if c.cache == nil {
		return nil, nil
	}
	meta := frameMeta{idValue: id.Value(), isExtended: id.IsExtended(), dlc: dlc.Value()}
	result, ok := c.cache.get(meta, data)
	if ok {
		if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
			c.logger.LogAttrs(ctx, slog.LevelDebug, "cache.hit",
				slog.Uint64("canId", uint64(id.Value())), slog.Uint64("dlc", uint64(dlc.Value())))
		}
	} else {
		if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
			c.logger.LogAttrs(ctx, slog.LevelDebug, "cache.miss",
				slog.Uint64("canId", uint64(id.Value())), slog.Uint64("dlc", uint64(dlc.Value())))
		}
		var err error
		result, err = c.extractSignalsLocked(ctx, id, dlc, data)
		if err != nil {
			return nil, err
		}
		if !c.cache.put(meta, data, result) && c.cache.noteFull() && c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "cache.full",
				slog.Int("size", maxExtractCache))
		}
	}
	values := make(map[SignalName]Rational)
	for _, sig := range diag.Signals {
		if val, found := result.Get(sig); found {
			values[sig] = val
		}
	}
	if len(values) == 0 {
		return nil, nil
	}
	return values, nil
}

// extractSignalsLocked extracts signals through the binary FFI, with the
// fallback contract of [Client.ExtractSignals]: only ErrBinaryPathUnsupported
// falls through to the JSON path (which is how a MockBackend-backed client
// still enriches once a DBC has filled the signal-name cache). Any other
// error, and a reply the reader refuses, is logged and returned, as Python's
// enrichment re-raises it. Caller holds the client lock.
func (c *Client) extractSignalsLocked(ctx context.Context, id CANID, dlc DLC, data FramePayload) (*ExtractionResult, error) {
	key := canIDKey(id)
	if names, ok := c.signalNames[key]; ok {
		buf, err := c.backend.ExtractSignalsBin(c.state, id, dlc, []byte(data))
		if err == nil {
			result, perr := parseExtractionBin(buf, names)
			if perr != nil {
				c.logExtractionFailure(ctx, "extraction.parse_failed", id, perr)
				return nil, perr
			}
			return result, nil
		}
		if !errors.Is(err, ErrBinaryPathUnsupported) {
			c.logExtractionFailure(ctx, "extraction.process_failed", id, err)
			return nil, err
		}
	}

	resp, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, []byte(data))
	if err != nil {
		c.logExtractionFailure(ctx, "extraction.process_failed", id, err)
		return nil, err
	}
	result, err := parseExtractionResponse(resp)
	if err != nil {
		c.logExtractionFailure(ctx, "extraction.parse_failed", id, err)
		return nil, err
	}
	return result, nil
}

// logExtractionFailure warns of a refused extraction under event.
func (c *Client) logExtractionFailure(ctx context.Context, event string, id CANID, err error) {
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelWarn, event,
			slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
	}
}
