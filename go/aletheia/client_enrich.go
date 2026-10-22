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
// cached extraction of extractSignalValues. Caller holds the client lock.
func (c *Client) enrichStreamingViolation(ctx context.Context, pr *PropertyResult, id CANID, dlc DLC, data FramePayload) {
	idx := int(pr.PropertyIndex)
	if idx >= len(c.diags) {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.property_index_oob",
				slog.Int("index", idx), slog.Int("count", len(c.diags)))
		}
		return
	}
	diag := c.diags[idx]
	values := c.extractSignalValues(ctx, diag, id, dlc, data)
	reason := formatEnrichedReason(diag, values, pr.Reason)
	pr.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     pr.Reason,
	}
}

// enrichEndOfStream adds a ViolationEnrichment to every Fails/Unresolved
// result, extracting each last-seen frame at most once per EndStream (the
// uniform cross-binding extract-once shape).
//
// Three passes: collect the results to enrich (warning on and excluding any
// out-of-bounds property index); extract the last-seen frames for the signals
// any collected diagnostic wants ([Client.extractLastFrames]); then
// distribute the merged values to each result, filtered to the signals its
// own diagnostic references. A failed frame extraction warns
// enrichment.extraction_failed once per frame per EndStream. A result whose
// signals have no value still gets an enrichment with the
// formula-description fallback reason.
//
// Caller must hold the client lock.  ctx is forwarded to slog so
// request-scoped attrs propagate into structured-log records.
func (c *Client) enrichEndOfStream(ctx context.Context, results []PropertyResult) {
	if len(c.diags) == 0 {
		return
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
		idx := int(pr.PropertyIndex)
		if idx >= len(c.diags) {
			if c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.property_index_oob",
					slog.Int("index", idx), slog.Int("count", len(c.diags)))
			}
			continue
		}
		todo = append(todo, pending{pr: pr, diag: c.diags[idx]})
	}
	if len(todo) == 0 {
		return
	}
	// Union of signal names wanted by any pending diagnostic.
	wanted := make(map[SignalName]bool)
	for _, p := range todo {
		for _, s := range p.diag.Signals {
			wanted[s] = true
		}
	}
	merged := c.extractLastFrames(ctx, wanted)
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
}

// extractLastFrames extracts the last-seen frames in key order, for a
// deterministic merge, until every wanted signal has a value, merging
// first-frame-wins; wanted is emptied as the values arrive, and a pass that
// starts with it empty extracts nothing. Caller holds the client lock.
func (c *Client) extractLastFrames(ctx context.Context, wanted map[SignalName]bool) map[SignalName]Rational {
	merged := make(map[SignalName]Rational)
	for _, k := range slices.SortedFunc(maps.Keys(c.lastFrames), compareFrameKeys) {
		if len(wanted) == 0 {
			return merged
		}
		lf := c.lastFrames[k]
		result := c.extractSignalsLocked(ctx, lf.id, lf.dlc, lf.data)
		if result == nil {
			if c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.extraction_failed",
					slog.Uint64("canId", uint64(lf.id.Value())))
			}
			continue
		}
		for _, sv := range result.Values {
			if _, ok := merged[sv.Name]; !ok {
				merged[sv.Name] = sv.Value
			}
			delete(wanted, sv.Name)
		}
	}
	return merged
}

// extractSignalValues extracts the signals a diagnostic names from a frame,
// through the cache. Caller holds the client lock.
func (c *Client) extractSignalValues(ctx context.Context, diag PropertyDiagnostic, id CANID, dlc DLC, data FramePayload) map[SignalName]Rational {
	if c.cache == nil {
		return nil
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
		result = c.extractSignalsLocked(ctx, id, dlc, data)
		if result != nil {
			if !c.cache.put(meta, data, result) && c.cache.noteFull() && c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "cache.full",
					slog.Int("size", maxExtractCache))
			}
		}
	}
	if result == nil {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.extraction_failed",
				slog.Uint64("canId", uint64(id.Value())))
		}
		return nil
	}
	values := make(map[SignalName]Rational)
	for _, sig := range diag.Signals {
		if val, found := result.Get(sig); found {
			values[sig] = val
		}
	}
	if len(values) == 0 {
		return nil
	}
	return values
}

// extractSignalsLocked extracts signals through the binary FFI, with the
// fallback contract of [Client.ExtractSignals]: only ErrBinaryPathUnsupported
// falls through to the JSON path (which is how a MockBackend-backed client
// still enriches once a DBC has filled the signal-name cache); any other
// error, and a buffer that does not parse, is logged and yields nil.
// Caller holds the client lock.
func (c *Client) extractSignalsLocked(ctx context.Context, id CANID, dlc DLC, data FramePayload) *ExtractionResult {
	key := canIDKey(id)
	if names, ok := c.signalNames[key]; ok {
		buf, err := c.backend.ExtractSignalsBin(c.state, id, dlc, []byte(data))
		if err == nil {
			result, perr := parseExtractionBin(buf, names)
			if perr != nil {
				if c.logger != nil {
					c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.parse_failed",
						slog.Uint64("canId", uint64(id.Value())), slog.String("error", perr.Error()))
				}
				return nil
			}
			return result
		}
		if !errors.Is(err, ErrBinaryPathUnsupported) {
			if c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.process_failed",
					slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
			}
			return nil
		}
	}

	resp, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, []byte(data))
	if err != nil {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.process_failed",
				slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
		}
		return nil
	}
	result, err := parseExtractionResponse(resp)
	if err != nil {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.parse_failed",
				slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
		}
		return nil
	}
	return result
}
