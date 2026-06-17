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

/// The attribute-bearing corpus fixture, so the pass-through round-trip claim is
/// actually exercised against non-empty `attributes`.
const ATTRS_DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/attributes.dbc");

#[test]
fn format_dbc_round_trips_attributes_passthrough() {
    let c = client();
    let (parsed, _warnings) = c.parse_dbc_text(ATTRS_DBC).expect("parse attributes DBC");
    assert!(
        !parsed.attributes.is_empty(),
        "attributes.dbc must carry attributes to exercise the pass-through"
    );
    let exported = c.format_dbc().expect("format_dbc export");
    assert_eq!(
        parsed.attributes, exported.attributes,
        "the raw-JSON attribute pass-through must survive parse → format_dbc"
    );
}
