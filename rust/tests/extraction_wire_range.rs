// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The kernel's wire-range refusal of an extracted signal value, against the
//! real `libaletheia-ffi.so`.
//!
//! The kernel's batch categoriser refuses an extracted value whose reduced
//! numerator magnitude or denominator is above 9223372036854775807 on both
//! extraction paths, as a per-signal error entry carrying one message. Each
//! case here runs one 64-bit signal through the JSON path (the DBC loaded
//! through the raw `parseDBC` command, which leaves the client's signal-name
//! cache empty, so `extract_signals` falls back to JSON) and through the binary
//! path (the same DBC loaded through the typed `parse_dbc`), and holds the two
//! answers to one error entry with the kernel's message. Set `ALETHEIA_LIB` to
//! the built shared library (run_ci / CI does).

use aletheia::{
    ByteOrder, CanId, Client, Dbc, DbcMessage, DbcSignal, Dlc, ExtractionResult, Presence, Rational,
};
use serde_json::{json, Value};

/// The kernel's message for a value past the wire range, on either path.
const WIRE_RANGE_MESSAGE: &str =
    "extracted value's numerator or denominator exceeds the Int64 wire range";

/// The one message of every document here: standard id 0x100, eight bytes.
const MESSAGE_ID: u16 = 0x100;

fn client() -> Client {
    Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

fn rational(numerator: i64, denominator: i64) -> Rational {
    Rational::new(numerator, denominator).expect("valid rational")
}

/// A document holding one message `Msg` whose one signal `Big` reads all 64
/// bits little-endian and unsigned, scaled by `factor` and `offset` within
/// `[minimum, maximum]`.
fn big_signal_document(
    factor: Rational,
    offset: Rational,
    minimum: Rational,
    maximum: Rational,
) -> Dbc {
    Dbc {
        version: "1.0".to_owned(),
        messages: vec![DbcMessage {
            id: u32::from(MESSAGE_ID),
            extended: false,
            name: "Msg".to_owned(),
            dlc: 8,
            sender: "ECU".to_owned(),
            senders: Vec::new(),
            signals: vec![DbcSignal {
                name: "Big".to_owned(),
                start_bit: 0,
                length: 64,
                byte_order: ByteOrder::LittleEndian,
                signed: false,
                factor,
                offset,
                minimum,
                maximum,
                unit: String::new(),
                receivers: Vec::new(),
                value_descriptions: Vec::new(),
                presence: Presence::Always,
            }],
        }],
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    }
}

/// A rational on the wire: a bare integer when the denominator is 1, else a
/// `{"numerator", "denominator"}` object, as the typed client writes it.
fn rational_value(r: Rational) -> Value {
    if r.denominator() == 1 {
        json!(r.numerator())
    } else {
        json!({ "numerator": r.numerator(), "denominator": r.denominator() })
    }
}

/// The `parseDBC` command line `Client::parse_dbc` sends for a document of
/// [`big_signal_document`]'s shape: every list of the document present, the
/// `extended` flag omitted because the id is standard, presence flat, no value
/// description.
fn parse_dbc_command(dbc: &Dbc) -> String {
    let messages: Vec<Value> = dbc
        .messages
        .iter()
        .map(|m| {
            let signals: Vec<Value> = m
                .signals
                .iter()
                .map(|s| {
                    let byte_order = match s.byte_order {
                        ByteOrder::LittleEndian => "little_endian",
                        ByteOrder::BigEndian => "big_endian",
                    };
                    json!({
                        "name": s.name,
                        "startBit": s.start_bit,
                        "length": s.length,
                        "byteOrder": byte_order,
                        "signed": s.signed,
                        "factor": rational_value(s.factor),
                        "offset": rational_value(s.offset),
                        "minimum": rational_value(s.minimum),
                        "maximum": rational_value(s.maximum),
                        "unit": s.unit,
                        "receivers": s.receivers,
                        "valueDescriptions": [],
                        "presence": "always",
                    })
                })
                .collect();
            json!({
                "id": m.id,
                "name": m.name,
                "dlc": m.dlc,
                "sender": m.sender,
                "senders": m.senders,
                "signals": signals,
            })
        })
        .collect();
    json!({
        "type": "command",
        "command": "parseDBC",
        "dbc": {
            "version": dbc.version,
            "messages": messages,
            "nodes": [],
            "valueTables": [],
            "environmentVars": [],
            "signalGroups": [],
            "comments": [],
            "attributes": [],
            "unresolvedValueDescs": [],
        },
    })
    .to_string()
}

/// Extracts `data` from message 0x100 on a client that loaded `dbc` through the
/// raw `parseDBC` command: the signal-name cache stays empty, so the answer is
/// the JSON extraction entry's.
fn extract_through_json(dbc: &Dbc, data: &[u8]) -> ExtractionResult {
    let c = client();
    let reply = c
        .process(&parse_dbc_command(dbc))
        .expect("parseDBC round-trip");
    let parsed: Value = serde_json::from_str(&reply).expect("a JSON reply");
    assert!(
        parsed.get("dbc").is_some_and(Value::is_object),
        "the document loads through parseDBC, got: {reply}"
    );
    c.extract_signals(
        CanId::standard(MESSAGE_ID).expect("id"),
        Dlc::new(8).expect("dlc"),
        data,
    )
    .expect("extract_signals over the JSON path")
}

/// Extracts `data` from message 0x100 on a client that loaded `dbc` through the
/// typed `parse_dbc`: the signal names are cached, so the answer is the binary
/// extraction entry's.
fn extract_through_binary(dbc: &Dbc, data: &[u8]) -> ExtractionResult {
    let c = client();
    c.parse_dbc(dbc).expect("parse_dbc");
    c.extract_signals(
        CanId::standard(MESSAGE_ID).expect("id"),
        Dlc::new(8).expect("dlc"),
        data,
    )
    .expect("extract_signals over the binary path")
}

/// Asserts `ex` is the kernel's refusal of `Big`: no value, no absent signal,
/// one error entry carrying the wire-range message.
fn assert_big_refused(path: &str, ex: &ExtractionResult) {
    assert!(ex.values.is_empty(), "{path}: no value: {ex:?}");
    assert!(ex.absent.is_empty(), "{path}: no absent signal: {ex:?}");
    assert_eq!(ex.errors.len(), 1, "{path}: one error entry: {ex:?}");
    assert_eq!(ex.errors[0].name, "Big", "{path}: {ex:?}");
    assert_eq!(ex.errors[0].reason, WIRE_RANGE_MESSAGE, "{path}: {ex:?}");
}

/// Both paths refuse `data` under `dbc` with the same entry.
fn assert_both_paths_refuse(dbc: &Dbc, data: &[u8]) {
    let json_path = extract_through_json(dbc, data);
    let binary_path = extract_through_binary(dbc, data);
    assert_big_refused("JSON path", &json_path);
    assert_big_refused("binary path", &binary_path);
    assert_eq!(
        json_path.errors[0].reason, binary_path.errors[0].reason,
        "the two paths carry one reason"
    );
}

/// Raw 2^63 + 1 scaled by 1/2^62 and shifted by 1/5^27: the reduced value's
/// numerator and denominator are both past the wire range.
#[test]
fn a_value_whose_numerator_and_denominator_exceed_the_wire_range_is_refused_on_both_paths() {
    let dbc = big_signal_document(
        rational(1, 4_611_686_018_427_387_904),
        rational(1, 7_450_580_596_923_828_125),
        rational(1, 7_450_580_596_923_828_125),
        Rational::integer(3),
    );
    assert_both_paths_refuse(&dbc, &[0x01, 0, 0, 0, 0, 0, 0, 0x80]);
}

/// Raw 2^63 scaled by -1/5: the numerator is exactly -2^63, which an int64
/// holds but the symmetric magnitude bound refuses.
#[test]
fn a_numerator_of_minus_two_to_the_sixty_third_is_refused_on_both_paths() {
    let dbc = big_signal_document(
        rational(-1, 5),
        Rational::integer(0),
        Rational::integer(-3_689_348_814_741_910_323),
        Rational::integer(0),
    );
    assert_both_paths_refuse(&dbc, &[0, 0, 0, 0, 0, 0, 0, 0x80]);
}
