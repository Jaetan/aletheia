package aletheia

import (
	"errors"
	"fmt"
	"unsafe"
)

// MockResponse is a canned response paired with an optional error.
type MockResponse struct {
	JSON string
	Err  error
}

// MockBackend implements [Backend] with canned JSON responses for testing.
// Each call to Process pops the next response from the queue. If the queue
// is exhausted, Process returns an error.
type MockBackend struct {
	responses []MockResponse
	cursor    int
	Inputs    []string // records all JSON inputs sent to Process
}

// NewMockBackend creates a MockBackend preloaded with the given responses.
func NewMockBackend(responses ...MockResponse) *MockBackend {
	return &MockBackend{responses: responses}
}

// Respond is a convenience for adding a successful JSON response.
func Respond(jsonStr string) MockResponse {
	return MockResponse{JSON: jsonStr}
}

// RespondErr is a convenience for adding an error response.
func RespondErr(err error) MockResponse {
	return MockResponse{Err: err}
}

// mockSentinel provides a non-nil address for Init's return value. The Backend
// contract requires Init to return non-nil on success, and Client.process checks
// c.closed rather than c.state for the use-after-close guard.
var mockSentinel byte

// Init returns a dummy non-nil pointer. The MockBackend does not use state.
func (m *MockBackend) Init() (unsafe.Pointer, error) {
	return unsafe.Pointer(&mockSentinel), nil
}

// NewMockError creates a simple error for use with [RespondErr].
func NewMockError(msg string) error { return errors.New(msg) }

// Process returns the next canned response, recording the input.
func (m *MockBackend) Process(_ unsafe.Pointer, input string) (string, error) {
	m.Inputs = append(m.Inputs, input)
	if m.cursor >= len(m.responses) {
		return "", fmt.Errorf("mock backend: no more responses (got %d calls, have %d responses)", m.cursor+1, len(m.responses))
	}
	resp := m.responses[m.cursor]
	m.cursor++
	if resp.Err != nil {
		return "", resp.Err
	}
	return resp.JSON, nil
}

// SendFrameBinary delegates to Process by building the JSON string via
// serializeDataFrame. This keeps mock tests working without the real .so.
func (m *MockBackend) SendFrameBinary(_ unsafe.Pointer, ts Timestamp, id CanID, dlc DLC, data []byte) (string, error) {
	input := serializeDataFrame(ts, id, dlc, FramePayload(data))
	return m.Process(nil, input)
}

// SendErrorBinary returns an ack response (error events are always acknowledged).
func (m *MockBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return `{"status":"ack"}`, nil
}

// SendRemoteBinary returns an ack response (remote frame events are always acknowledged).
func (m *MockBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CanID) (string, error) {
	return `{"status":"ack"}`, nil
}

// StartStreamBinary delegates to Process with a JSON startStream command.
func (m *MockBackend) StartStreamBinary(state unsafe.Pointer) (string, error) {
	cmd, err := serializeCommand("startStream", nil)
	if err != nil {
		return "", err
	}
	return m.Process(state, cmd)
}

// EndStreamBinary delegates to Process with a JSON endStream command.
func (m *MockBackend) EndStreamBinary(state unsafe.Pointer) (string, error) {
	cmd, err := serializeCommand("endStream", nil)
	if err != nil {
		return "", err
	}
	return m.Process(state, cmd)
}

// FormatDbcBinary delegates to Process with a JSON formatDBC command.
func (m *MockBackend) FormatDbcBinary(state unsafe.Pointer) (string, error) {
	cmd, err := serializeCommand("formatDBC", nil)
	if err != nil {
		return "", err
	}
	return m.Process(state, cmd)
}

// ExtractSignalsBinary delegates to Process with a JSON extractAllSignals command.
func (m *MockBackend) ExtractSignalsBinary(state unsafe.Pointer, id CanID, dlc DLC, data []byte) (string, error) {
	cmd, err := serializeCommand("extractAllSignals", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     bytesToIntSlice(data),
	})
	if err != nil {
		return "", err
	}
	return m.Process(state, cmd)
}

// BuildFrameBinary delegates to Process with a JSON buildFrame command.
// Signal indices and rationals are serialized back into named signal values
// for compatibility with the JSON protocol.
func (m *MockBackend) BuildFrameBinary(state unsafe.Pointer, id CanID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) (string, error) {
	signals := make([]map[string]any, 0, numSignals)
	for i := uint32(0); i < numSignals; i++ {
		signals = append(signals, map[string]any{
			"index":       indices[i],
			"numerator":   nums[i],
			"denominator": dens[i],
		})
	}
	cmd, err := serializeCommand("buildFrame", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"signals":  signals,
	})
	if err != nil {
		return "", err
	}
	return m.Process(state, cmd)
}

// UpdateFrameBinary delegates to Process with a JSON updateFrame command.
// Signal indices and rationals are serialized back into named signal values
// for compatibility with the JSON protocol.
func (m *MockBackend) UpdateFrameBinary(state unsafe.Pointer, id CanID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) (string, error) {
	signals := make([]map[string]any, 0, numSignals)
	for i := uint32(0); i < numSignals; i++ {
		signals = append(signals, map[string]any{
			"index":       indices[i],
			"numerator":   nums[i],
			"denominator": dens[i],
		})
	}
	cmd, err := serializeCommand("updateFrame", map[string]any{
		"canId":    id.Value(),
		"extended": id.IsExtended(),
		"dlc":      dlc.Value(),
		"data":     bytesToIntSlice(data),
		"signals":  signals,
	})
	if err != nil {
		return "", err
	}
	return m.Process(state, cmd)
}

// BuildFrameBin delegates to BuildFrameBinary and parses the JSON response.
func (m *MockBackend) BuildFrameBin(state unsafe.Pointer, id CanID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error) {
	resp, err := m.BuildFrameBinary(state, id, dlc, numSignals, indices, nums, dens)
	if err != nil {
		return nil, err
	}
	return parseFrameDataResponse(resp)
}

// UpdateFrameBin delegates to UpdateFrameBinary and parses the JSON response.
func (m *MockBackend) UpdateFrameBin(state unsafe.Pointer, id CanID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error) {
	resp, err := m.UpdateFrameBinary(state, id, dlc, data, numSignals, indices, nums, dens)
	if err != nil {
		return nil, err
	}
	return parseFrameDataResponse(resp)
}

// ExtractSignalsBin is not supported by MockBackend — returns an error.
// The Client falls back to the JSON path when the signal name cache is not populated.
func (m *MockBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) ([]byte, error) {
	return nil, protocolError("extract_signals_bin requires FFI backend")
}

// Close is a no-op for the mock backend.
func (m *MockBackend) Close(_ unsafe.Pointer) {}
