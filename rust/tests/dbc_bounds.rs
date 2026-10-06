// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! DBC size-bound refusals against the real `libaletheia-ffi.so`.
//!
//! The kernel bounds the length of a DBC's lists and strings, and `parse_dbc`,
//! `parse_dbc_text`, `validate_dbc` and `format_dbc_text` refuse a document
//! past one of those bounds with `Error::InputBoundExceeded`, an error whose
//! text is the kernel's message exactly and which names the field that crossed
//! the bound. Each case here builds a small document with a list or string
//! past its limit, beside one with an identifier past its length bound, which
//! names no field. Set `ALETHEIA_LIB` to the built shared library (run_ci / CI
//! does).

use aletheia::{
    AttrScope, AttrType, Attribute, ByteOrder, Client, Dbc, DbcMessage, DbcSignal, EnvironmentVar,
    Error, Presence, Rational, SignalGroup,
};
use serde_json::json;

fn client() -> Client {
    Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

/// A one-bit unsigned signal at bit 0 with range [0, 1].
fn signal(name: &str) -> DbcSignal {
    DbcSignal {
        name: name.to_owned(),
        start_bit: 0,
        length: 1,
        byte_order: ByteOrder::LittleEndian,
        signed: false,
        factor: Rational::integer(1),
        offset: Rational::integer(0),
        minimum: Rational::integer(0),
        maximum: Rational::integer(1),
        unit: String::new(),
        receivers: Vec::new(),
        value_descriptions: Vec::new(),
        presence: Presence::Always,
    }
}

fn message(id: u32, signals: Vec<DbcSignal>) -> DbcMessage {
    DbcMessage {
        id,
        extended: false,
        name: format!("M{id}"),
        dlc: 8,
        sender: "ECU".to_owned(),
        senders: Vec::new(),
        signals,
    }
}

/// One message carrying one signal, and every other list empty.
fn base() -> Dbc {
    Dbc {
        version: "1.0".to_owned(),
        messages: vec![message(256, vec![signal("S")])],
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    }
}

/// `n` names `prefix0`, `prefix1`, ...
fn names(prefix: &str, n: usize) -> Vec<String> {
    (0..n).map(|i| format!("{prefix}{i}")).collect()
}

/// The base document with `n` empty signal groups.
fn with_signal_groups(n: usize) -> Dbc {
    Dbc {
        signal_groups: names("G", n)
            .into_iter()
            .map(|name| SignalGroup {
                name,
                signals: Vec::new(),
            })
            .collect(),
        ..base()
    }
}

/// The base document with `n` environment variables.
fn with_environment_vars(n: usize) -> Dbc {
    Dbc {
        environment_vars: names("E", n)
            .into_iter()
            .map(|name| EnvironmentVar {
                name,
                var_type: 0,
                initial: Rational::integer(0),
                minimum: Rational::integer(0),
                maximum: Rational::integer(1),
            })
            .collect(),
        ..base()
    }
}

/// `result` is the refusal `Error::InputBoundExceeded` carrying `kind`,
/// `observed` and `limit`, naming `field`, and carrying the kernel's
/// `message`, which is its text.
fn assert_refused<T: std::fmt::Debug>(
    result: Result<T, Error>,
    (kind, observed, limit): (&str, u64, u64),
    field: &str,
    message: &str,
) {
    let err = result.expect_err("a DBC past a size bound is refused");
    match &err {
        Error::InputBoundExceeded {
            code,
            message: m,
            bound_kind,
            observed: o,
            limit: l,
            field: f,
        } => {
            assert_eq!(code, "input_bound_exceeded");
            assert_eq!(m, message);
            assert_eq!((bound_kind.as_str(), *o, *l), (kind, observed, limit));
            assert_eq!(f.as_deref(), Some(field));
        }
        other => panic!("expected Error::InputBoundExceeded, got {other:?}"),
    }
    assert_eq!(err.to_string(), message);
}

#[test]
fn the_base_document_loads() {
    client()
        .parse_dbc(&base())
        .expect("the document every case widens loads");
}

#[test]
fn parse_dbc_refuses_too_many_signal_groups() {
    let dbc = with_signal_groups(10_001);
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "signal groups array",
        "ParseDBC: signal groups array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_refuses_too_many_environment_variables() {
    let dbc = with_environment_vars(10_001);
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "environment variables array",
        "ParseDBC: environment variables array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_refuses_too_many_unresolved_value_description_lines() {
    let mut dbc = base();
    let line = json!({ "id": 999, "extended": false, "signalName": "Q", "entries": [] });
    dbc.unresolved_value_descs = vec![line; 10_001];
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "unresolved value descriptions array",
        "ParseDBC: unresolved value descriptions array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_refuses_too_many_senders() {
    let mut dbc = base();
    dbc.messages[0].senders = names("N", 10_001);
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "senders array",
        "ParseDBC: senders array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_refuses_too_many_receivers() {
    let mut dbc = base();
    dbc.messages[0].signals[0].receivers = names("N", 10_001);
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "receivers array",
        "ParseDBC: receivers array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_refuses_too_many_signal_group_members() {
    let mut dbc = base();
    dbc.signal_groups = vec![SignalGroup {
        name: "G".to_owned(),
        signals: names("S", 1_025),
    }];
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 1_025, 1_024),
        "signal group members array",
        "ParseDBC: signal group members array: array cardinality 1025 exceeds limit 1024",
    );
}

#[test]
fn parse_dbc_refuses_too_many_enum_labels() {
    let mut dbc = base();
    dbc.attributes = vec![Attribute::Definition {
        name: "A".to_owned(),
        scope: AttrScope::Network,
        attr_type: AttrType::Enum {
            values: names("v", 10_001),
        },
    }];
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "enum labels array",
        "ParseDBC: enum labels array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_refuses_too_many_multiplex_values() {
    let mut dbc = base();
    let mut selector = signal("Mx");
    selector.length = 8;
    selector.maximum = Rational::integer(255);
    let mut selected = signal("S");
    selected.start_bit = 8;
    selected.presence = Presence::Multiplexed {
        multiplexor: "Mx".to_owned(),
        values: (0..1_025).collect(),
    };
    dbc.messages = vec![message(256, vec![selector, selected])];
    assert_refused(
        client().parse_dbc(&dbc),
        ("array_cardinality", 1_025, 1_024),
        "multiplex values array",
        "ParseDBC: multiplex values array: array cardinality 1025 exceeds limit 1024",
    );
}

#[test]
fn validate_dbc_refuses_too_many_environment_variables() {
    let dbc = with_environment_vars(10_001);
    assert_refused(
        client().validate_dbc(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "environment variables array",
        "ValidateDBC: environment variables array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn format_dbc_text_refuses_too_many_signal_groups() {
    let dbc = with_signal_groups(10_001);
    assert_refused(
        client().format_dbc_text(&dbc),
        ("array_cardinality", 10_001, 10_000),
        "signal groups array",
        "FormatDBCText: signal groups array: array cardinality 10001 exceeds limit 10000",
    );
}

#[test]
fn format_dbc_text_refuses_a_version_string_too_long() {
    let mut dbc = base();
    dbc.version = "x".repeat(65_537);
    assert_refused(
        client().format_dbc_text(&dbc),
        ("string_length", 65_537, 65_536),
        "version string",
        "FormatDBCText: version string: string length 65537 exceeds limit 65536",
    );
}

#[test]
fn format_dbc_text_refuses_too_many_nodes_derived_from_the_senders() {
    // With no nodes listed, the formatter derives them from the senders: ECU,
    // which sends both messages, and the 5001 further senders of each.
    let mut dbc = base();
    let mut first = message(256, vec![signal("S")]);
    first.senders = names("A", 5_001);
    let mut second = message(257, vec![signal("S")]);
    second.senders = names("B", 5_001);
    dbc.messages = vec![first, second];
    client()
        .parse_dbc(&dbc)
        .expect("the document is within every load bound");
    assert_refused(
        client().format_dbc_text(&dbc),
        ("array_cardinality", 10_003, 10_000),
        "nodes array",
        "FormatDBCText: nodes array: array cardinality 10003 exceeds limit 10000",
    );
}

#[test]
fn parse_dbc_text_refuses_a_version_string_too_long() {
    let text = client()
        .format_dbc_text(&base())
        .expect("the base document formats")
        .text;
    let long = text.replacen(
        "VERSION \"1.0\"",
        &format!("VERSION \"{}\"", "x".repeat(65_537)),
        1,
    );
    assert_ne!(long, text, "the formatted text carries the base version");
    assert_refused(
        client().parse_dbc_text(&long),
        ("string_length", 65_537, 65_536),
        "version string",
        "ParseDBCText: version string: string length 65537 exceeds limit 65536",
    );
}

#[test]
fn an_identifier_too_long_is_a_bound_that_names_no_field() {
    let name = "S".repeat(129);
    let dbc = Dbc {
        messages: vec![message(256, vec![signal(&name)])],
        ..base()
    };
    let kernel = format!(
        "ParseDBC: message 'M256', signal '{name}': identifier length 129 exceeds limit 128"
    );
    let err = client()
        .parse_dbc(&dbc)
        .expect_err("a signal name past its length bound is refused");
    match &err {
        Error::InputBoundExceeded {
            message,
            bound_kind,
            observed,
            limit,
            field,
            ..
        } => {
            assert_eq!(*message, kernel);
            assert_eq!(
                (bound_kind.as_str(), *observed, *limit),
                ("identifier_length", 129, 128)
            );
            assert_eq!(*field, None);
        }
        other => panic!("expected Error::InputBoundExceeded, got {other:?}"),
    }
    assert_eq!(err.to_string(), kernel);
}
