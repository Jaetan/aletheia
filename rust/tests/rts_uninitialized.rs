// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The rational renderer, decimal parsing and each YAML loader are *vocal* when
//! the GHC RTS is uninitialised, a loader returning the parser's refusal
//! unlocated and its own refusal of a document answering on the document, and
//! the allocation count answers no count.
//!
//! Its own test binary because the GHC RTS is process-global and one-shot: any real
//! `Client`/`AsyncClient` (`Client::new()`) in the same binary would bring the RTS
//! up and defeat the assertion. This binary creates ONLY a mock-backed client, so
//! the RTS stays down, and a render (`add_checks` → `set_properties` builds the
//! per-property diagnostics, which render the predicate threshold) must return a
//! typed runtime-not-initialised error rather than self-initialising or fabricating
//! a value. Mirrors C++'s dedicated `rts_init_renderer_uninitialized_tests` binary.

use aletheia::{check, Client, Error, MockBackend, Rational};

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

    // Match the variant, not a message substring: RTS-down is its own typed error.
    // `format_rational` checks the runtime latch before loading anything, so it
    // answers this whether or not the `.so` could be loaded.
    assert!(
        matches!(err, Error::RtsNotInitialized),
        "expected Error::RtsNotInitialized; got: {err:?}"
    );
}

#[test]
fn from_decimal_is_vocal_when_the_rts_is_uninitialised() {
    // Decimal parsing delegates to the kernel (RTS-gated, exactly like the
    // renderer); with no backend up it must return the typed RTS-down error, not
    // self-initialise or fabricate a value.
    let err =
        Rational::from_decimal("3.14").expect_err("from_decimal with the RTS down must be vocal");
    assert!(
        matches!(err, Error::RtsNotInitialized),
        "expected Error::RtsNotInitialized; got: {err:?}"
    );
}

#[test]
fn the_allocation_count_is_none_when_the_rts_is_uninitialised() {
    // No backend has started the runtime, so there is no count, and the read
    // must not call the kernel's entry, which needs the runtime up.
    assert_eq!(aletheia::allocated_bytes(), None);
}

/// The refusal a number read answers while the runtime is down.
#[cfg(feature = "yaml")]
const RUNTIME_DOWN: &str = "GHC runtime not initialized: call aletheia::start_runtime or build a \
                            Client before rendering or parsing a number";

/// A load reading a number with the RTS down returns the decimal parser's
/// refusal as it is: the typed runtime error, its text, unlocated.
#[cfg(feature = "yaml")]
fn assert_the_runtime_refusal<T: std::fmt::Debug>(loaded: Result<T, Error>) {
    let err = loaded.expect_err("a load reading a number with the RTS down must be refused");
    assert!(
        matches!(err, Error::RtsNotInitialized),
        "expected Error::RtsNotInitialized; got: {err:?}"
    );
    assert_eq!(err.to_string(), RUNTIME_DOWN);
    assert_eq!((err.location(), err.key()), (None, None));
}

#[cfg(feature = "yaml")]
#[test]
fn every_yaml_loader_returns_the_runtime_refusal_unlocated_when_the_rts_is_uninitialised() {
    const DOCUMENT: &str =
        "checks:\n  - name: c\n    signal: Speed\n    condition: never_exceeds\n    value: 11.5\n";
    // A when-then check reads its time bound first.
    const WHEN_THEN: &str = "checks:\n  - name: w\n    when:\n      signal: Brake\n      \
                             condition: exceeds\n      value: 50\n    then:\n      signal: Light\n      \
                             condition: equals\n      value: 1\n    within_ms: 100\n";
    assert_the_runtime_refusal(aletheia::load_checks_from_yaml(DOCUMENT));
    assert_the_runtime_refusal(aletheia::load_checks_from_yaml(WHEN_THEN));
    let path = std::env::temp_dir().join(format!("aletheia_rts_down_{}.yaml", std::process::id()));
    std::fs::write(&path, DOCUMENT).expect("write the checks file");
    let loaded = aletheia::load_checks_from_yaml_file(&path);
    let _ = std::fs::remove_file(&path);
    assert_the_runtime_refusal(loaded);
}

#[cfg(feature = "yaml")]
#[test]
fn a_yaml_loader_s_own_refusal_answers_on_its_document_when_the_rts_is_uninitialised() {
    let err = aletheia::load_checks_from_yaml("not: a checks list\n")
        .expect_err("a document holding no checks list must be refused");
    assert!(
        matches!(err, Error::Validation { code: None, .. }),
        "expected Error::Validation with no code; got: {err:?}"
    );
    assert_eq!(err.to_string(), "YAML must contain a 'checks' list");
}
