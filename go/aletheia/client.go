package aletheia

import (
	"fmt"
	"io"
	"log/slog"
	"sync"
	"unsafe"
)

// Compile-time assertion: Client implements io.Closer.
var _ io.Closer = (*Client)(nil)

// ClientOption configures optional [Client] behavior.
type ClientOption func(*Client)

// WithLogger sets a structured logger for operational events.
// When nil (default), no logging occurs and there is zero overhead.
func WithLogger(l *slog.Logger) ClientOption {
	return func(c *Client) { c.logger = l }
}

// Client provides Aletheia operations over a Backend.
// A Client is safe for concurrent use from multiple goroutines; calls are
// serialized internally because the underlying LTL automaton is sequential.
// Create with [NewClient] and close with [Client.Close] (implements [io.Closer]).
type Client struct {
	backend    Backend
	state      unsafe.Pointer
	mu         sync.Mutex
	closeOnce  sync.Once
	closed     bool
	logger     *slog.Logger                   // nil = no logging
	diags      []PropertyDiagnostic           // one per property, auto-derived
	cache      *extractCache                  // extraction cache for enrichment
	lastFrames map[lastFrameKey]lastFrameData // last frame seen per CAN ID, for EOS enrichment
}

// NewClient creates a Client backed by the given Backend.
// It calls backend.Init() to create a session.
func NewClient(backend Backend, opts ...ClientOption) (*Client, error) {
	state, err := backend.Init()
	if err != nil {
		return nil, err
	}
	c := &Client{backend: backend, state: state}
	for _, opt := range opts {
		opt(c)
	}
	return c, nil
}

// Close finalizes the session. The Client must not be used after Close.
// Close is safe to call concurrently or multiple times.
func (c *Client) Close() error {
	c.closeOnce.Do(func() {
		c.mu.Lock()
		defer c.mu.Unlock()
		if c.state != nil {
			c.backend.Close(c.state)
			c.state = nil
			c.closed = true
		}
	})
	return nil
}

// process sends input to the backend under the client mutex, rejecting calls after Close.
func (c *Client) process(input string) (string, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.processLocked(input)
}

// processLocked sends input to the backend. Caller must hold c.mu.
func (c *Client) processLocked(input string) (string, error) {
	if c.closed {
		return "", stateError("client is closed")
	}
	return c.backend.Process(c.state, input)
}

// lastFrameKey distinguishes standard and extended CAN IDs in the last-frame map.
type lastFrameKey struct {
	value    uint32
	extended bool
}

// lastFrameData stores the last frame seen for a CAN ID, for EOS enrichment.
type lastFrameData struct {
	id   CanID
	dlc  DLC
	data FramePayload
}

// validatePayload checks that the payload length matches the DLC byte count.
func validatePayload(dlc DLC, data FramePayload) error {
	expected := dlc.ToBytes()
	if len(data) != expected {
		return validationError(fmt.Sprintf("payload length %d does not match DLC %d (expected %d bytes)", len(data), dlc.Value(), expected))
	}
	return nil
}

// --- DBC operations ---

// ParseDBC sends a DBC definition to the Agda core for parsing and loading.
// Subsequent signal extraction and frame building use this parsed definition.
func (c *Client) ParseDBC(dbc DbcDefinition) error {
	dbcMap, err := serializeDBC(dbc)
	if err != nil {
		return err
	}
	cmd, err := serializeCommand("parseDBC", map[string]any{
		"dbc": dbcMap,
	})
	if err != nil {
		return err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return err
	}
	return parseSuccessResponse(resp)
}

// ValidateDBC checks a DBC definition for structural issues (overlapping signals,
// factor-zero, DLC violations, etc.) and returns all found issues.
func (c *Client) ValidateDBC(dbc DbcDefinition) (*ValidationResult, error) {
	dbcMap, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("validateDBC", map[string]any{
		"dbc": dbcMap,
	})
	if err != nil {
		return nil, err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return nil, err
	}
	return parseValidationResponse(resp)
}

// FormatDBC returns the currently loaded DBC definition as parsed by the Agda core.
// Call ParseDBC first.
func (c *Client) FormatDBC() (*DbcDefinition, error) {
	cmd, err := serializeCommand("formatDBC", nil)
	if err != nil {
		return nil, err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return nil, err
	}
	return parseDbcResponse(resp)
}

// --- Signal operations ---

// ExtractSignals decodes all signals from a CAN frame using the loaded DBC.
func (c *Client) ExtractSignals(id CanID, dlc DLC, data FramePayload) (*ExtractionResult, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("extractAllSignals", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     bytesToIntSlice(data),
	})
	if err != nil {
		return nil, err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return nil, err
	}
	return parseExtractionResponse(resp)
}

// BuildFrame encodes signal values into a CAN frame payload.
func (c *Client) BuildFrame(id CanID, signals []SignalValue, dlc DLC) (FramePayload, error) {
	cmd, err := serializeCommand("buildFrame", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"signals":  serializeSignalValues(signals),
	})
	if err != nil {
		return nil, err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return nil, err
	}
	return parseFrameDataResponse(resp)
}

// UpdateFrame modifies specific signals in an existing CAN frame.
func (c *Client) UpdateFrame(id CanID, dlc DLC, data FramePayload, signals []SignalValue) (FramePayload, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("updateFrame", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     bytesToIntSlice(data),
		"signals":  serializeSignalValues(signals),
	})
	if err != nil {
		return nil, err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return nil, err
	}
	return parseFrameDataResponse(resp)
}

// --- Streaming LTL operations ---
//
// Expected call sequence: SetProperties → StartStream → SendFrame* → EndStream.
// StartStream resets the extraction cache and last-frame tracking.
// SetProperties may be called again after EndStream to install new properties.

// SetProperties installs LTL properties for stream monitoring.
// Automatically derives diagnostic metadata from the formula structure for
// violation enrichment.
func (c *Client) SetProperties(properties []Formula) error {
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
	c.mu.Lock()
	defer c.mu.Unlock()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	c.diags = make([]PropertyDiagnostic, len(properties))
	for i, f := range properties {
		c.diags[i] = BuildDiagnostic(f)
	}
	c.cache = newExtractCache()
	if c.logger != nil {
		c.logger.Info("properties.set", "count", len(properties))
	}
	return nil
}

// StartStream begins a new LTL monitoring stream.
// SetProperties must be called before StartStream.
func (c *Client) StartStream() error {
	cmd, err := serializeCommand("startStream", nil)
	if err != nil {
		return err
	}
	// Hold lock for both the backend call and the cache clear
	// to prevent SendFrame from using a stale cache.
	c.mu.Lock()
	defer c.mu.Unlock()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	if c.cache != nil {
		c.cache.clear()
	}
	c.lastFrames = make(map[lastFrameKey]lastFrameData)
	if c.logger != nil {
		c.logger.Info("stream.started")
	}
	return nil
}

// SendFrame sends a CAN frame to the active monitoring stream.
// Returns Ack or Violation depending on whether any property was violated.
// Violations are automatically enriched with signal values and a human-readable
// formula description when diagnostics are available.
func (c *Client) SendFrame(ts Timestamp, id CanID, dlc DLC, data FramePayload) (FrameResponse, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.closed {
		return nil, stateError("client is closed")
	}
	if ts.Microseconds < 0 {
		return nil, validationError("negative timestamp")
	}
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	resp, err := c.backend.SendFrameBinary(c.state, ts, id, dlc, []byte(data))
	if err != nil {
		return nil, err
	}
	fr, err := parseFrameResponse(resp)
	if err != nil {
		return nil, err
	}
	// Track last frame per CAN ID for EOS enrichment.
	// Copy data to prevent caller mutation from corrupting stored frames.
	if c.lastFrames != nil {
		dataCopy := make(FramePayload, len(data))
		copy(dataCopy, data)
		c.lastFrames[lastFrameKey{value: id.Value(), extended: id.IsExtended()}] = lastFrameData{id: id, dlc: dlc, data: dataCopy}
	}
	if v, ok := fr.(Violation); ok && c.diags != nil {
		c.enrichViolation(&v, id, dlc, data)
		if c.logger != nil {
			c.logger.Debug("frame.processed", "ts", ts.Microseconds, "canId", id.Value(), "extended", id.IsExtended(), "response", "violation")
		}
		return v, nil
	}
	if c.logger != nil {
		c.logger.Debug("frame.processed", "ts", ts.Microseconds, "canId", id.Value(), "extended", id.IsExtended(), "response", "ack")
	}
	return fr, nil
}

// EndStream finalizes the monitoring stream and returns verdicts for all properties.
// Failed verdicts are enriched with signal names, formula description, and the most
// recent signal values per CAN ID when available. Earlier frames in the stream are
// not retained.
func (c *Client) EndStream() (*StreamResult, error) {
	cmd, err := serializeCommand("endStream", nil)
	if err != nil {
		return nil, err
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	sr, err := parseStreamResponse(resp)
	if err != nil {
		return nil, err
	}
	numFails := 0
	if c.diags != nil {
		for i := range sr.Results {
			if sr.Results[i].Verdict == Fails {
				numFails++
				c.enrichPropertyResult(&sr.Results[i])
			}
		}
	}
	c.lastFrames = nil
	if c.logger != nil {
		c.logger.Info("stream.ended", "numResults", len(sr.Results), "numFails", numFails)
	}
	return sr, nil
}

// enrichViolation adds a ViolationEnrichment to a Violation. Caller must hold c.mu.
func (c *Client) enrichViolation(v *Violation, id CanID, dlc DLC, data FramePayload) {
	idx := int(v.PropertyIndex)
	if idx >= len(c.diags) {
		if c.logger != nil {
			c.logger.Warn("enrichment.property_index_oob", "index", idx, "count", len(c.diags))
		}
		return
	}
	diag := c.diags[idx]
	values := c.extractSignalValues(diag, id, dlc, data)
	reason := formatEnrichedReason(diag, values, v.Reason)
	v.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     v.Reason,
	}
}

// enrichPropertyResult adds a ViolationEnrichment to a failed PropertyResult,
// including last-known signal values from tracked frames. Caller must hold c.mu.
func (c *Client) enrichPropertyResult(pr *PropertyResult) {
	idx := int(pr.PropertyIndex)
	if idx >= len(c.diags) {
		if c.logger != nil {
			c.logger.Warn("enrichment.property_index_oob", "index", idx, "count", len(c.diags))
		}
		return
	}
	diag := c.diags[idx]
	values := c.extractLastKnownValues(diag)
	reason := formatEnrichedReason(diag, values, pr.Reason)
	pr.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     pr.Reason,
	}
}

// extractLastKnownValues extracts signal values from the last-seen frames for
// all signals referenced in a diagnostic. Caller must hold c.mu.
func (c *Client) extractLastKnownValues(diag PropertyDiagnostic) map[SignalName]PhysicalValue {
	if len(c.lastFrames) == 0 || len(diag.Signals) == 0 {
		return nil
	}
	wanted := make(map[SignalName]bool, len(diag.Signals))
	for _, s := range diag.Signals {
		wanted[s] = true
	}
	values := make(map[SignalName]PhysicalValue)
	// Try extraction against all last-seen frames to find matching signals.
	for _, lf := range c.lastFrames {
		result := c.extractSignalsLocked(lf.id, lf.dlc, lf.data)
		if result == nil {
			if c.logger != nil {
				c.logger.Warn("enrichment.extraction_failed", "canId", lf.id.Value())
			}
			continue
		}
		for _, sv := range result.Values {
			if wanted[sv.Name] {
				values[sv.Name] = sv.Value
				delete(wanted, sv.Name)
			}
		}
		if len(wanted) == 0 {
			break
		}
	}
	if len(values) == 0 {
		return nil
	}
	return values
}

// extractSignalValues extracts signal values for a diagnostic from a frame, using the cache.
// Caller must hold c.mu.
func (c *Client) extractSignalValues(diag PropertyDiagnostic, id CanID, dlc DLC, data FramePayload) map[SignalName]PhysicalValue {
	if c.cache == nil {
		return nil
	}
	key := frameKey{idValue: id.Value(), isExtended: id.IsExtended(), dlc: dlc.Value(), data: string(data)}
	result, ok := c.cache.get(key)
	if ok {
		if c.logger != nil {
			c.logger.Debug("cache.hit", "canId", id.Value(), "dlc", dlc.Value())
		}
	} else {
		if c.logger != nil {
			c.logger.Debug("cache.miss", "canId", id.Value(), "dlc", dlc.Value())
		}
		result = c.extractSignalsLocked(id, dlc, data)
		if result != nil {
			if !c.cache.put(key, result) && c.logger != nil {
				c.logger.Warn("cache.full", "size", maxExtractCache)
			}
		}
	}
	if result == nil {
		if c.logger != nil {
			c.logger.Warn("enrichment.extraction_failed", "canId", id.Value())
		}
		return nil
	}
	values := make(map[SignalName]PhysicalValue)
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

// extractSignalsLocked performs signal extraction via processLocked. Caller must hold c.mu.
func (c *Client) extractSignalsLocked(id CanID, dlc DLC, data FramePayload) *ExtractionResult {
	cmd, err := serializeCommand("extractAllSignals", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     bytesToIntSlice(data),
	})
	if err != nil {
		if c.logger != nil {
			c.logger.Warn("extraction.serialize_failed", "canId", id.Value(), "error", err)
		}
		return nil
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		if c.logger != nil {
			c.logger.Warn("extraction.process_failed", "canId", id.Value(), "error", err)
		}
		return nil
	}
	result, err := parseExtractionResponse(resp)
	if err != nil {
		if c.logger != nil {
			c.logger.Warn("extraction.parse_failed", "canId", id.Value(), "error", err)
		}
		return nil
	}
	return result
}
