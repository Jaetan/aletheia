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
//	ctx := context.Background()
//	parsed, err := client.ParseDBC(ctx, dbc)
//	if err != nil { log.Fatal(err) }
//	_ = parsed.Warnings // non-fatal validation issues, if any
//	result, err := client.ExtractSignals(ctx, canID, dlc, frameData)
//
// Cancellation: every operation method takes a context.Context as its first
// parameter and honors cancellation cooperatively at FFI boundaries — see
// docs/architecture/CANCELLATION.md for the full contract. NewClient and
// Close do NOT take ctx (construction and teardown are synchronous and
// uncancellable by design).
//
// Functional options:
//
//	backend, err := aletheia.NewFFIBackend(
//	    "/path/to/libaletheia-ffi.so",
//	    aletheia.WithRTSCores(4),
//	    aletheia.WithFFILogger(slog.Default()),
//	)
//	if err != nil { log.Fatal(err) }
//
//	client, err := aletheia.NewClient(
//	    backend,
//	    aletheia.WithLogger(slog.Default()),
//	    aletheia.WithDefaultChecks(defaultCheck),
//	)
//	if err != nil { log.Fatal(err) }
//
// Observability event vocabulary:
//
// When a *slog.Logger is wired in (via WithLogger or WithFFILogger), the
// Client and FFIBackend emit structured records with the following event
// names. Cross-binding parity is asserted against the C++ Logger and the
// Python logger adapter — any drift here is a finding.
//
//	rts.cores_mismatch              (FFIBackend, Warn)
//	dbc.parsed                      (Client, Info)
//	properties.set                  (Client, Info)
//	stream.started                  (Client, Info)
//	stream.ended                    (Client, Info)
//	error_event.sent                (Client, Debug)
//	remote_event.sent               (Client, Debug)
//	frame.processed                 (Client, Debug)
//	cache.hit                       (Client, Debug)
//	cache.miss                      (Client, Debug)
//	cache.full                      (Client, Warn)
//	enrichment.property_index_oob   (Client, Warn)
//	enrichment.extraction_failed    (Client, Warn)
//	extraction.process_failed       (Client, Warn)
//	extraction.parse_failed         (Client, Warn)
package aletheia
