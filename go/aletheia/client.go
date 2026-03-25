package aletheia

import (
	"io"
	"sync"
	"unsafe"
)

// Compile-time assertion: Client implements io.Closer.
var _ io.Closer = (*Client)(nil)

// Client provides Aletheia operations over a Backend.
// A Client is safe for concurrent use from multiple goroutines.
// Create with [NewClient] and close with [Client.Close] (implements [io.Closer]).
type Client struct {
	backend   Backend
	state     unsafe.Pointer
	mu        sync.Mutex
	closeOnce sync.Once
	closed    bool
	diags     []PropertyDiagnostic // one per property, auto-derived
	cache     *extractCache        // extraction cache for enrichment
}

// NewClient creates a Client backed by the given Backend.
// It calls backend.Init() to create a session.
func NewClient(backend Backend) (*Client, error) {
	state, err := backend.Init()
	if err != nil {
		return nil, err
	}
	return &Client{backend: backend, state: state}, nil
}

// Close finalizes the session. The Client must not be used after Close.
// Close is safe to call concurrently or multiple times.
func (c *Client) Close() error {
	c.closeOnce.Do(func() {
		c.mu.Lock()
		defer c.mu.Unlock()
		if c.backend != nil && c.state != nil {
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

// --- DBC operations ---

// ParseDBC sends a DBC definition to the Agda core for parsing and loading.
// Subsequent signal extraction and frame building use this parsed definition.
func (c *Client) ParseDBC(dbc DbcDefinition) error {
	cmd, err := serializeCommand("parseDBC", map[string]any{
		"dbc": serializeDBC(dbc),
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
	cmd, err := serializeCommand("validateDBC", map[string]any{
		"dbc": serializeDBC(dbc),
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
	byteSlice := make([]uint8, len(data))
	copy(byteSlice, data)
	cmd, err := serializeCommand("extractAllSignals", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     byteSlice,
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
	byteSlice := make([]uint8, len(data))
	copy(byteSlice, data)
	cmd, err := serializeCommand("updateFrame", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     byteSlice,
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

// SetProperties installs LTL properties for stream monitoring.
// Automatically derives diagnostic metadata from the formula structure for
// violation enrichment.
func (c *Client) SetProperties(properties []Formula) error {
	props := make([]map[string]any, 0, len(properties))
	for _, f := range properties {
		props = append(props, serializeFormula(f))
	}
	cmd, err := serializeCommand("setProperties", map[string]any{
		"properties": props,
	})
	if err != nil {
		return err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	// Auto-derive diagnostics from formula structure.
	c.mu.Lock()
	c.diags = make([]PropertyDiagnostic, len(properties))
	for i, f := range properties {
		c.diags[i] = BuildDiagnostic(f)
	}
	c.cache = newExtractCache()
	c.mu.Unlock()
	return nil
}

// StartStream begins a new LTL monitoring stream.
// SetProperties must be called before StartStream.
func (c *Client) StartStream() error {
	cmd, err := serializeCommand("startStream", nil)
	if err != nil {
		return err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	c.mu.Lock()
	if c.cache != nil {
		c.cache.clear()
	}
	c.mu.Unlock()
	return nil
}

// SendFrame sends a CAN frame to the active monitoring stream.
// Returns Ack or Violation depending on whether any property was violated.
// Violations are automatically enriched with signal values and a human-readable
// formula description when diagnostics are available.
func (c *Client) SendFrame(ts Timestamp, id CanID, dlc DLC, data FramePayload) (FrameResponse, error) {
	input, err := serializeDataFrame(ts, id, dlc, data)
	if err != nil {
		return nil, err
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	resp, err := c.processLocked(input)
	if err != nil {
		return nil, err
	}
	fr, err := parseFrameResponse(resp)
	if err != nil {
		return nil, err
	}
	if v, ok := fr.(Violation); ok && c.diags != nil {
		c.enrichViolation(&v, id, dlc, data)
		return v, nil
	}
	return fr, nil
}

// EndStream finalizes the monitoring stream and returns verdicts for all properties.
// Failed verdicts are enriched with signal names and formula description.
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
	if c.diags != nil {
		for i := range sr.Results {
			if sr.Results[i].Verdict == Fails {
				c.enrichPropertyResult(&sr.Results[i])
			}
		}
	}
	return sr, nil
}

// enrichViolation adds a ViolationEnrichment to a Violation. Caller must hold c.mu.
func (c *Client) enrichViolation(v *Violation, id CanID, dlc DLC, data FramePayload) {
	idx := int(v.PropertyIndex)
	if idx >= len(c.diags) {
		return
	}
	diag := c.diags[idx]
	values := c.extractSignalValues(diag, id, dlc, data)
	reason := formatEnrichedReason(diag, values)
	v.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
	}
}

// enrichPropertyResult adds a ViolationEnrichment to a failed PropertyResult. Caller must hold c.mu.
func (c *Client) enrichPropertyResult(pr *PropertyResult) {
	idx := int(pr.PropertyIndex)
	if idx >= len(c.diags) {
		return
	}
	diag := c.diags[idx]
	pr.Enrichment = &ViolationEnrichment{
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: "violated: " + diag.FormulaDesc,
	}
}

// extractSignalValues extracts signal values for a diagnostic from a frame, using the cache.
// Caller must hold c.mu.
func (c *Client) extractSignalValues(diag PropertyDiagnostic, id CanID, dlc DLC, data FramePayload) map[SignalName]PhysicalValue {
	if c.cache == nil {
		return nil
	}
	key := frameKey{idValue: id.Value(), isExtended: id.IsExtended(), dlc: dlc.Value(), data: string(data)}
	result, ok := c.cache.get(key)
	if !ok {
		result = c.extractSignalsLocked(id, dlc, data)
		if result != nil {
			c.cache.put(key, result)
		}
	}
	if result == nil {
		return nil
	}
	values := make(map[SignalName]PhysicalValue)
	for _, sig := range diag.Signals {
		if val, found := result.Get(sig); found {
			values[sig] = val
		}
	}
	return values
}

// extractSignalsLocked calls ExtractSignals without acquiring the mutex. Caller must hold c.mu.
func (c *Client) extractSignalsLocked(id CanID, dlc DLC, data FramePayload) *ExtractionResult {
	byteSlice := make([]uint8, len(data))
	copy(byteSlice, data)
	cmd, err := serializeCommand("extractAllSignals", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     byteSlice,
	})
	if err != nil {
		return nil
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil
	}
	result, err := parseExtractionResponse(resp)
	if err != nil {
		return nil
	}
	return result
}
