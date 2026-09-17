// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Package aletheia is the Go client for Aletheia, the formally verified CAN
// frame analysis system. It wraps libaletheia-ffi.so through cgo and dlopen:
// signal extraction, LTL evaluation and DBC validation run in the
// Agda-verified core, and this package owns the session lifecycle, the JSON
// protocol and the Go types.
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
// Every operation method takes a context.Context first and honours
// cancellation at FFI boundaries; docs/architecture/CANCELLATION.md is the
// contract. NewClient and Close take no context: construction and teardown
// are synchronous and cannot be cancelled.
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
// Streaming adequacy: the streaming evaluator is sound, and it asks of the
// trace that every property's signal be observed at least once, the
// AllObserved obligation of Aletheia.Protocol.Adequacy.StreamingWarm
// (streaming-warms-cache), which the FFI does not check. A property whose
// signal no frame carries may finalise as [Unresolved], the three-valued
// Kleene "unsure", rather than [Holds] or [Fails]; the verdicts reported stay
// sound. The section "Streaming Semantics: Soundness vs. Completeness" of
// docs/architecture/PROTOCOL.md is the contract.
//
// Log events: with a *slog.Logger wired in through WithLogger or
// WithFFILogger, the Client and the FFIBackend emit records under these
// names, which docs/LOG_EVENTS.yaml pins across the four bindings:
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
//	endstream.uncached_atom         (Client, Warn)
package aletheia
