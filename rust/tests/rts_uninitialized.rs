// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Point 2: the rational renderer is *vocal* when the GHC RTS is uninitialised.
//!
//! Its own test binary because the GHC RTS is process-global and one-shot: any real
//! `Client`/`AsyncClient` (`Client::new()`) in the same binary would bring the RTS
//! up and defeat the assertion. This binary creates ONLY a mock-backed client, so
//! the RTS stays down, and a render (`add_checks` → `set_properties` builds the
//! per-property diagnostics, which render the predicate threshold) must return a
//! typed runtime-not-initialised error rather than self-initialising or fabricating
//! a value. Mirrors C++'s dedicated `rts_init_renderer_uninitialized_tests` binary.

use aletheia::{check, Client, MockBackend};

#[test]
fn renderer_is_vocal_when_the_rts_is_uninitialised() {
    let m = MockBackend::new();
    // Ack the setProperties wire send so the flow reaches the (vocal) render that
    // builds the per-property diagnostics — the render, not the wire call, is what
    // must fail here (set_properties sends, then renders the diagnostics).
    m.respond_json(r#"{"status":"ack"}"#);
    let c = Client::with_backend(Box::new(m));

    let err = c
        .add_checks(&[check::signal("Speed").never_exceeds(120)])
        .expect_err("rendering a threshold with the RTS down must be vocal, not silent");

    // Assert the SPECIFIC error. `format_rational` loads the `.so` (for its symbols)
    // BEFORE checking the RTS, so a missing library surfaces as a different
    // (library-load) error — this test is only meaningful as "RTS down" when the
    // `.so` is present, so pin the exact message rather than accept any `Err`.
    let msg = err.to_string();
    assert!(
        msg.contains("runtime not initialized"),
        "expected the runtime-not-initialised error (the .so must be present so this is not a \
         missing-library error); got: {msg}"
    );
}
