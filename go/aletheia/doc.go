// Package aletheia provides a Go client for the Aletheia formally verified
// CAN frame analysis system. It wraps libaletheia-ffi.so via cgo/dlopen.
//
// The core logic (signal extraction, LTL evaluation, DBC validation) runs
// inside the Agda-verified Haskell core. This package handles lifecycle
// management, JSON protocol serialization, and Go-idiomatic type safety.
//
// Basic usage:
//
//	backend, err := aletheia.NewFFIBackend("/path/to/libaletheia-ffi.so")
//	if err != nil { log.Fatal(err) }
//
//	client, err := aletheia.NewClient(backend)
//	if err != nil { log.Fatal(err) }
//	defer client.Close()
//
//	if err = client.ParseDBC(dbc); err != nil { log.Fatal(err) }
//	result, err := client.ExtractSignals(canID, dlc, frameData)
package aletheia
