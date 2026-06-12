// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Tracer-bullet test: exercises the full FFI lifecycle against the real
//! `libaletheia-ffi.so` — load → RTS init → one command round-trip → free →
//! close. Set `ALETHEIA_LIB` to the built shared library (run_ci / CI does this).

use aletheia::Client;

#[test]
fn rts_lifecycle_round_trip() {
    let client =
        Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?");

    // Minimal valid command: parse an (empty) DBC. We assert only that a JSON
    // response carrying a status field comes back — the point of this slice is
    // the lifecycle and GHC-allocated-memory ownership, not command semantics.
    let cmd = r#"{"type":"command","command":"parseDBC","dbc":{"version":"1.0","messages":[]}}"#;
    let resp = client.process(cmd).expect("process round-trip");

    assert!(
        resp.contains("\"status\""),
        "expected a JSON status field in the response, got: {resp}"
    );
    // Client::drop closes the StreamState handle.
}
