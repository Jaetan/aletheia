// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed DBC document tests against the real `libaletheia-ffi.so`.
//!
//! Exercises the read side of Slice R1: `parse_dbc_text` returning the typed
//! [`Dbc`], the `format_dbc` export round-trip, and the mux-query / lookup
//! helpers. Set `ALETHEIA_LIB` to the built shared library (run_ci / CI does).

use aletheia::{CanId, Client, Presence};

/// The shared corpus `multiplexing.dbc` — two messages, single-multiplexor each.
const DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/multiplexing.dbc");

fn client() -> Client {
    Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

#[test]
fn parse_dbc_text_returns_typed_document() {
    let c = client();
    let (dbc, _warnings) = c.parse_dbc_text(DBC).expect("parse DBC text");

    let m = dbc
        .message_by_id(CanId::standard(100).expect("valid id"))
        .expect("message 100 present");
    assert!(m.is_multiplexed());
    assert_eq!(m.multiplexor_names(), vec!["Mode"]);

    let payload_a = m.signal_by_name("PayloadA").expect("PayloadA present");
    match &payload_a.presence {
        Presence::Multiplexed {
            multiplexor,
            values,
        } => {
            assert_eq!(multiplexor, "Mode");
            assert_eq!(values, &[0]);
        }
        Presence::Always => panic!("PayloadA should be multiplexed"),
    }

    // Lookup helpers resolve.
    assert!(dbc.message_by_name(&m.name).is_some());
}

#[test]
fn format_dbc_round_trips_the_loaded_document() {
    let c = client();
    let (parsed, _warnings) = c.parse_dbc_text(DBC).expect("parse DBC text");
    let exported = c.format_dbc().expect("format_dbc export");
    assert_eq!(
        parsed, exported,
        "parse_dbc_text then format_dbc must yield the same typed document"
    );
}

/// The attribute-bearing corpus fixture, so the round-trip is exercised against
/// the full typed `BA_*` vocabulary.
const ATTRS_DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/attributes.dbc");

#[test]
fn format_dbc_round_trips_typed_attributes() {
    let c = client();
    let (parsed, _warnings) = c.parse_dbc_text(ATTRS_DBC).expect("parse attributes DBC");
    assert!(
        !parsed.attributes.is_empty(),
        "attributes.dbc must carry attributes to exercise the typed model"
    );
    let exported = c.format_dbc().expect("format_dbc export");
    assert_eq!(
        parsed.attributes, exported.attributes,
        "the typed attribute vocabulary must survive parse → format_dbc"
    );
}

/// The comprehensive corpus fixture — messages, multiplexing, value tables,
/// env vars, signal groups, comments, and the full attribute vocabulary — so
/// the serialize round-trips exercise every part of `Dbc::to_value`.
const KITCHEN: &str = include_str!("../../python/tests/fixtures/dbc_corpus/kitchen_sink.dbc");

#[test]
fn parse_dbc_round_trips_the_serialized_document() {
    let c = client();
    let (from_text, _) = c.parse_dbc_text(KITCHEN).expect("parse DBC text");
    // parse_dbc serializes the typed document and feeds it back through the core
    // (the JSON path); a correct serialize re-parses to the same document.
    let (from_json, _) = c.parse_dbc(&from_text).expect("parse_dbc (JSON path)");
    assert_eq!(
        from_text, from_json,
        "parse_dbc_text → parse_dbc must round-trip the typed document"
    );
}

#[test]
fn format_dbc_text_round_trips_through_the_formatter() {
    let c = client();
    let (from_text, _) = c.parse_dbc_text(KITCHEN).expect("parse DBC text");
    // serialize → core .dbc formatter → re-parse must be the identity.
    let text = c.format_dbc_text(&from_text).expect("format_dbc_text");
    let (reparsed, _) = c.parse_dbc_text(&text).expect("re-parse formatted text");
    assert_eq!(
        from_text, reparsed,
        "format_dbc_text output must re-parse to the same typed document"
    );
}

#[test]
fn validate_dbc_reports_no_errors_for_the_valid_corpus() {
    let c = client();
    let (dbc, _) = c.parse_dbc_text(KITCHEN).expect("parse DBC text");
    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(
        !result.has_errors,
        "kitchen_sink is a valid DBC — validation found errors: {:?}",
        result.issues
    );
}

#[test]
fn validate_dbc_flags_an_invalid_document() {
    let c = client();
    let (mut dbc, _) = c.parse_dbc_text(KITCHEN).expect("parse DBC text");
    // Shrink a populated message to 0 bytes: every signal's bit range now
    // exceeds the DLC — a structural error the validator must report (pins the
    // has_errors == true branch the valid-corpus test never reaches).
    let msg = dbc
        .messages
        .iter_mut()
        .find(|m| !m.signals.is_empty())
        .expect("a message with signals");
    msg.dlc = 0;
    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(result.has_errors, "an over-DLC signal must be an error");
    assert!(!result.issues.is_empty(), "errors must carry issues");
}
