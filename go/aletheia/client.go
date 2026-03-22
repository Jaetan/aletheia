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
func (c *Client) ExtractSignals(id CanID, data FramePayload) (*ExtractionResult, error) {
	byteSlice := make([]uint8, 8)
	for i := 0; i < 8; i++ {
		byteSlice[i] = data[i]
	}
	cmd, err := serializeCommand("extractAllSignals", map[string]any{
		"canId": id.Value(),
		"data":  byteSlice,
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
func (c *Client) BuildFrame(id CanID, signals []SignalValue) (*FramePayload, error) {
	cmd, err := serializeCommand("buildFrame", map[string]any{
		"canId":   id.Value(),
		"signals": serializeSignalValues(signals),
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
func (c *Client) UpdateFrame(id CanID, data FramePayload, signals []SignalValue) (*FramePayload, error) {
	byteSlice := make([]uint8, 8)
	for i := 0; i < 8; i++ {
		byteSlice[i] = data[i]
	}
	cmd, err := serializeCommand("updateFrame", map[string]any{
		"canId":   id.Value(),
		"data":    byteSlice,
		"signals": serializeSignalValues(signals),
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
	return parseSuccessResponse(resp)
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
	return parseSuccessResponse(resp)
}

// SendFrame sends a CAN frame to the active monitoring stream.
// Returns Ack or Violation depending on whether any property was violated.
func (c *Client) SendFrame(ts Timestamp, id CanID, data FramePayload) (FrameResponse, error) {
	input, err := serializeDataFrame(ts, id, data)
	if err != nil {
		return nil, err
	}
	resp, err := c.process(input)
	if err != nil {
		return nil, err
	}
	return parseFrameResponse(resp)
}

// EndStream finalizes the monitoring stream and returns verdicts for all properties.
func (c *Client) EndStream() (*StreamResult, error) {
	cmd, err := serializeCommand("endStream", nil)
	if err != nil {
		return nil, err
	}
	resp, err := c.process(cmd)
	if err != nil {
		return nil, err
	}
	return parseStreamResponse(resp)
}
