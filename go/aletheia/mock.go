// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"errors"
	"fmt"
	"strings"
	"sync"
	"unsafe"
)

// MockResponse is a canned response paired with an optional error.
type MockResponse struct {
	JSON string
	Err  error
}

// MockBackend is the [Backend] a test drives: every call takes the next
// response from a queue the test filled, and a call past the end is a refusal
// naming the operation that starved.
//
// It is safe to use from several goroutines. Every entry point takes the same
// lock, because a deployment watching several buses shares one client's
// backend across the calls its methods make.
type MockBackend struct {
	mu        sync.Mutex
	responses []MockResponse
	cursor    int
	inputs    []string // records all JSON inputs sent to Process
}

func (*MockBackend) backend() {}

// NewMockBackend creates a MockBackend preloaded with the given responses.
func NewMockBackend(responses ...MockResponse) *MockBackend {
	return &MockBackend{responses: responses}
}

// Inputs returns a copy of the recorded inputs so callers cannot race with
// ongoing Process calls.
func (m *MockBackend) Inputs() []string {
	m.mu.Lock()
	defer m.mu.Unlock()
	out := make([]string, len(m.inputs))
	copy(out, m.inputs)
	return out
}

// Respond is a convenience for adding a successful JSON response.
func Respond(jsonStr string) MockResponse {
	return MockResponse{JSON: jsonStr}
}

// RespondErr is a convenience for adding an error response.
func RespondErr(err error) MockResponse {
	return MockResponse{Err: err}
}

// RespondParseDBC is the answer the kernel gives to a definition it parsed:
// the definition itself and any warnings. A test uses it to give the client a
// known definition, which is what fills its signal lookup, without the
// library. A definition that cannot be encoded comes back as the queued
// error, so the test fails at that response rather than on a later one.
func RespondParseDBC(dbc DBCDefinition, warnings ...ValidationIssue) MockResponse {
	dbcJSON, err := serializeDBC(dbc)
	if err != nil {
		return MockResponse{Err: fmt.Errorf("RespondParseDBC: serialize DBC: %w", err)}
	}
	wireWarnings := make([]map[string]any, 0, len(warnings))
	for _, w := range warnings {
		wireWarnings = append(wireWarnings, map[string]any{
			"severity": w.Severity.String(),
			"code":     string(w.Code),
			"detail":   w.Detail,
		})
	}
	raw, err := json.Marshal(map[string]any{
		"status":   "success",
		"dbc":      dbcJSON,
		"warnings": wireWarnings,
	})
	if err != nil {
		return MockResponse{Err: fmt.Errorf("RespondParseDBC: marshal JSON: %w", err)}
	}
	return MockResponse{JSON: string(raw)}
}

// mockSentinel is an address to hand back from Init, which must answer
// something that is not nil. The mock keeps no state behind it, and the client
// knows it is closed by its own flag rather than by this pointer.
var mockSentinel byte

// Init answers the sentinel address.
func (m *MockBackend) Init() (unsafe.Pointer, error) {
	return unsafe.Pointer(&mockSentinel), nil
}

// NewMockError creates a simple error for use with [RespondErr].
func NewMockError(msg string) error { return errors.New(msg) }

// Process returns the next canned response, recording the input.
func (m *MockBackend) Process(_ unsafe.Pointer, input string) (string, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.processLocked(input)
}

// mockOpName is the operation to name when the queue runs out. A binary call
// records a sentinel that already names it, so that is used as it stands;
// every other command arrives through Process, which is what the refusal calls
// it, as the Rust mock does.
func mockOpName(input string) string {
	if strings.HasPrefix(input, "<binary:") {
		return input
	}
	return "process"
}

// processLocked is the inner implementation of Process. Caller must hold m.mu.
func (m *MockBackend) processLocked(input string) (string, error) {
	m.inputs = append(m.inputs, input)
	if m.cursor >= len(m.responses) {
		return "", stateError(fmt.Sprintf("mock backend: no queued response for %s", mockOpName(input)))
	}
	resp := m.responses[m.cursor]
	m.cursor++
	if resp.Err != nil {
		return "", resp.Err
	}
	return resp.JSON, nil
}

// Each method below records a sentinel naming its operation rather than a
// JSON command, because the library takes these calls as binary and there is
// no JSON for a test to imitate. The sentinel records that the call was made;
// what it carried is checked against the library itself, by the round-trip
// tests such as TestCrossBinding_SendFrameBrsEsiPassthrough. The Python and
// C++ mocks record the same names.

// SendFrameBinary records a frame.
func (m *MockBackend) SendFrameBinary(
	state unsafe.Pointer, _ Timestamp,
	_ CANID, _ DLC, _ []byte,
	_ *bool, _ *bool,
) (string, error) {
	return m.Process(state, "<binary:sendFrame>")
}

// SendErrorBinary records an error event.
func (m *MockBackend) SendErrorBinary(state unsafe.Pointer, _ Timestamp) (string, error) {
	return m.Process(state, "<binary:sendError>")
}

// SendRemoteBinary records a remote frame.
func (m *MockBackend) SendRemoteBinary(state unsafe.Pointer, _ Timestamp, _ CANID) (string, error) {
	return m.Process(state, "<binary:sendRemote>")
}

// StartStreamBinary records the start of a stream.
func (m *MockBackend) StartStreamBinary(state unsafe.Pointer) (string, error) {
	return m.Process(state, "<binary:startStream>")
}

// EndStreamBinary records the end of one.
func (m *MockBackend) EndStreamBinary(state unsafe.Pointer) (string, error) {
	return m.Process(state, "<binary:endStream>")
}

// FormatDBCBinary records a request for the loaded definition.
func (m *MockBackend) FormatDBCBinary(state unsafe.Pointer) (string, error) {
	return m.Process(state, "<binary:formatDBC>")
}

// ExtractSignalsBinary records an extraction.
func (m *MockBackend) ExtractSignalsBinary(state unsafe.Pointer, _ CANID, _ DLC, _ []byte) (string, error) {
	return m.Process(state, "<binary:extractAllSignals>")
}

// BuildFrameBin records a frame build and reads the payload out of the queued
// response, which is how a test says what the kernel would have built.
func (m *MockBackend) BuildFrameBin(state unsafe.Pointer, _ CANID, _ DLC, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	resp, err := m.Process(state, "<binary:buildFrameBin>")
	if err != nil {
		return nil, err
	}
	return parseFrameDataResponse(resp)
}

// UpdateFrameBin records a frame update and reads its payload the same way.
func (m *MockBackend) UpdateFrameBin(state unsafe.Pointer, _ CANID, _ DLC, _ []byte, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	resp, err := m.Process(state, "<binary:updateFrameBin>")
	if err != nil {
		return nil, err
	}
	return parseFrameDataResponse(resp)
}

// ExtractSignalsBin refuses with [ErrBinaryPathUnsupported]: the packed
// extraction is the library's, and a mock cannot produce it. The client knows
// that one error and asks again through the JSON path, which the mock does
// answer; any other error it passes on, so a real decode failure is never read
// as a reason to try the other path.
func (m *MockBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) ([]byte, error) {
	return nil, ErrBinaryPathUnsupported
}

// Close is a no-op for the mock backend.
func (m *MockBackend) Close(_ unsafe.Pointer) {}

// The interface is satisfied here, so a drift in its signatures fails the
// build rather than the first test that uses the mock.
var _ Backend = (*MockBackend)(nil)
