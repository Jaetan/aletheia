package aletheia

import (
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
func NewMockError(msg string) error { return fmt.Errorf("%s", msg) }

// Process returns the next canned response, recording the input.
func (m *MockBackend) Process(_ unsafe.Pointer, input string) (string, error) {
	m.Inputs = append(m.Inputs, input)
	if m.cursor >= len(m.responses) {
		return "", fmt.Errorf("MockBackend: no more responses (got %d calls, have %d responses)", m.cursor+1, len(m.responses))
	}
	resp := m.responses[m.cursor]
	m.cursor++
	if resp.Err != nil {
		return "", resp.Err
	}
	return resp.JSON, nil
}

// Close is a no-op for the mock backend.
func (m *MockBackend) Close(_ unsafe.Pointer) {}
