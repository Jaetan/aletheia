package aletheia

import "unsafe"

// Backend abstracts the FFI boundary to the Agda core.
// Production code uses [FFIBackend]; tests use [MockBackend].
type Backend interface {
	// Init creates a new session and returns an opaque state handle.
	Init() (unsafe.Pointer, error)
	// Process sends a JSON command and returns the JSON response.
	Process(state unsafe.Pointer, input string) (string, error)
	// Close finalizes and frees the session state.
	Close(state unsafe.Pointer)
}
