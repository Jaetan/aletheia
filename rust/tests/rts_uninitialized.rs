// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The rational renderer, decimal parsing, the check builders and each YAML
//! loader are *vocal* when the GHC RTS is uninitialised: each answers
//! [`Error::RtsNotInitialized`] naming what it was doing, a loader returning
//! the parser's refusal unlocated and its own refusal of a document answering
//! on the document, and the allocation count answers no count.
//!
//! Its own test binary because the GHC RTS is process-global and one-shot: any real
//! `Client`/`AsyncClient` (`Client::new()`) in the same binary would bring the RTS
//! up and defeat the assertion. This binary creates ONLY a mock-backed client, so
//! the RTS stays down: a check's build is refused before any threshold could
//! render, and properties the double accepted are refused when `set_properties`
//! renders their thresholds into the per-property diagnostics, rather than
//! self-initialising or fabricating a value. Mirrors C++'s dedicated
//! `rts_init_renderer_uninitialized_tests` binary.

use aletheia::{check, Client, Error, Formula, MockBackend, Predicate, Rational};

/// The refusal while the runtime is down, after the words naming what the
/// call was doing.
fn runtime_down(operation: &str) -> String {
    format!(
        "GHC runtime not initialized: call aletheia::start_runtime or build a Client before \
         {operation}"
    )
}

/// A call made with the runtime down: the typed runtime error naming
/// `operation`, its text, unlocated.
fn assert_runtime_down<T: std::fmt::Debug>(answered: Result<T, Error>, operation: &str) {
    let err = answered.expect_err("a call with the RTS down must be vocal, not silent");
    // Match the variant, not a message substring: RTS-down is its own typed error.
    assert!(
        matches!(&err, Error::RtsNotInitialized { operation: named } if *named == operation),
        "expected Error::RtsNotInitialized before {operation}; got: {err:?}"
    );
    assert_eq!(err.to_string(), runtime_down(operation));
    assert_eq!((err.location(), err.key()), (None, None));
}

/// The formula `never_exceeds(220)` builds on `Speed`, written whole, since no
/// builder answers one while the runtime is down.
fn speed_at_most_220() -> Formula {
    Formula::Always(Box::new(Formula::Atomic(Predicate::LessThanOrEqual {
        signal: "Speed".to_string(),
        value: Rational::integer(220),
    })))
}

#[test]
fn a_check_s_build_returns_the_runtime_refusal_while_it_is_down() {
    // The kernel checks a check as it is built, so the build is refused before
    // its threshold could render, an inverted range's included.
    let sig = check::signal("Speed");
    assert_runtime_down(sig.clone().never_exceeds(220), "building a check");
    assert_runtime_down(sig.stays_between(10, 5), "building a check");
}

#[test]
fn properties_the_core_accepted_return_the_renderer_refusal_while_it_is_down() {
    // The double accepts what it is sent, so the refusal is the diagnostic's
    // render, after the command reached the backend. `format_rational` checks
    // the runtime latch before loading anything, so it answers this whether or
    // not the `.so` could be loaded.
    let m = MockBackend::new();
    m.respond_json(r#"{"status":"success"}"#);
    let c = Client::with_backend(Box::new(m.clone()));
    assert_runtime_down(c.set_properties(&[speed_at_most_220()]), "rendering");
    assert_eq!(m.captured().len(), 1, "the command reached the backend");
}

#[test]
fn from_decimal_is_vocal_when_the_rts_is_uninitialised() {
    // Decimal parsing delegates to the kernel (RTS-gated, exactly like the
    // renderer); with no backend up it must return the typed RTS-down error, not
    // self-initialise or fabricate a value.
    assert_runtime_down(Rational::from_decimal("3.14"), "parsing decimals");
}

#[test]
fn the_allocation_count_is_none_when_the_rts_is_uninitialised() {
    // No backend has started the runtime, so there is no count, and the read
    // must not call the kernel's entry, which needs the runtime up.
    assert_eq!(aletheia::allocated_bytes(), None);
}

#[cfg(feature = "yaml")]
#[test]
fn every_yaml_loader_returns_the_runtime_refusal_unlocated_when_the_rts_is_uninitialised() {
    const DOCUMENT: &str =
        "checks:\n  - name: c\n    signal: Speed\n    condition: never_exceeds\n    value: 11.5\n";
    // A when-then check reads its time bound first.
    const WHEN_THEN: &str = "checks:\n  - name: w\n    when:\n      signal: Brake\n      \
                             condition: exceeds\n      value: 50\n    then:\n      signal: Light\n      \
                             condition: equals\n      value: 1\n    within_us: 100000\n";
    assert_runtime_down(
        aletheia::load_checks_from_yaml(DOCUMENT),
        "parsing decimals",
    );
    assert_runtime_down(
        aletheia::load_checks_from_yaml(WHEN_THEN),
        "reading a time bound",
    );
    let path = std::env::temp_dir().join(format!("aletheia_rts_down_{}.yaml", std::process::id()));
    std::fs::write(&path, DOCUMENT).expect("write the checks file");
    let loaded = aletheia::load_checks_from_yaml_file(&path);
    let _ = std::fs::remove_file(&path);
    assert_runtime_down(loaded, "parsing decimals");
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
