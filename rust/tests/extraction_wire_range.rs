// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The kernel's wire-range refusal of an extracted signal value, against the
//! real `libaletheia-ffi.so`.
//!
//! The kernel's batch categoriser refuses an extracted value whose reduced
//! numerator magnitude or denominator is past 2^128-1 on both extraction
//! paths, as a per-signal error entry carrying one message. The case here
//! runs one 132-bit CAN-FD signal through the JSON path (the DBC loaded
//! through the raw `parseDBC` command, after which the client's signal-name
//! cache is empty, so `extract_signals` falls back to JSON) and through the
//! binary path (the same DBC loaded through the typed `parse_dbc`), and holds
//! the two answers to one error entry with the kernel's message. Set
//! `ALETHEIA_LIB` to the built shared library (run_ci / CI does).

use aletheia::{
    ByteOrder, CanId, Client, Dbc, DbcMessage, DbcSignal, Dlc, Error, ExtractionResult,
    MockBackend, Presence, Rational,
};
use serde_json::Value;

/// The kernel's message for a value past the wire range, on either path.
const WIRE_RANGE_MESSAGE: &str = "extracted value's numerator or denominator magnitude exceeds \
                                  340282366920938463463374607431768211455";

/// The one message of the document: standard id 0x300, 64 bytes.
const MESSAGE_ID: u16 = 0x300;

/// The 64-byte length code.
fn dlc64() -> Dlc {
    Dlc::new(15).expect("dlc")
}

fn client() -> Client {
    Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

/// A document holding one message `Msg` whose one signal `Big` reads 132 bits
/// little-endian and unsigned at a tenth, declared within `[0, 2^128-1]`.
fn big_signal_document() -> Dbc {
    Dbc {
        version: "1.0".to_owned(),
        messages: vec![DbcMessage {
            id: u32::from(MESSAGE_ID),
            extended: false,
            name: "Msg".to_owned(),
            dlc: 64,
            sender: "ECU".to_owned(),
            senders: Vec::new(),
            signals: vec![DbcSignal {
                name: "Big".to_owned(),
                start_bit: 0,
                length: 132,
                byte_order: ByteOrder::LittleEndian,
                signed: false,
                factor: Rational::new(1, 10).expect("a tenth"),
                offset: Rational::integer(0),
                minimum: Rational::integer(0),
                maximum: Rational::from(u128::MAX),
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

/// The payload carrying the raw value (2^128-1)*10 - 1, which is
/// 9 * 2^128 + (2^128 - 11), little-endian: a tenth of it is within the
/// declared range, and its numerator in lowest terms is past 2^128-1.
fn past_the_bound_payload() -> Vec<u8> {
    let mut payload = vec![0u8; 64];
    payload[..16].copy_from_slice(&(u128::MAX - 10).to_le_bytes());
    payload[16] = 9;
    payload
}

/// The `parseDBC` command line `Client::parse_dbc` writes for `dbc`, as a
/// client over a mock records it.
fn parse_dbc_command(dbc: &Dbc) -> String {
    let mock = MockBackend::new();
    mock.respond_err(Error::NullResponse {
        entry: "aletheia_process",
    });
    let refused = Client::with_backend(Box::new(mock.clone())).parse_dbc(dbc);
    assert!(
        matches!(
            refused,
            Err(Error::NullResponse {
                entry: "aletheia_process"
            })
        ),
        "the mock answers the queued error, got: {refused:?}"
    );
    let mut captured = mock.captured();
    assert_eq!(captured.len(), 1, "one command: {captured:?}");
    captured.remove(0)
}

/// Extracts `data` from message 0x300 on a client that loaded `dbc` through the
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
    c.extract_signals(CanId::standard(MESSAGE_ID).expect("id"), dlc64(), data)
        .expect("extract_signals over the JSON path")
}

/// Extracts `data` from message 0x300 on a client that loaded `dbc` through the
/// typed `parse_dbc`: the signal names are cached, so the answer is the binary
/// extraction entry's.
fn extract_through_binary(dbc: &Dbc, data: &[u8]) -> ExtractionResult {
    let c = client();
    c.parse_dbc(dbc).expect("parse_dbc");
    c.extract_signals(CanId::standard(MESSAGE_ID).expect("id"), dlc64(), data)
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

/// A 132-bit CAN-FD signal at a tenth, its raw value (2^128-1)*10 - 1 within
/// the declared range, reduces to a numerator past the bound: both paths
/// refuse it with the same entry.
#[test]
fn a_numerator_past_the_bound_is_refused_on_both_paths() {
    let dbc = big_signal_document();
    let data = past_the_bound_payload();
    let json_path = extract_through_json(&dbc, &data);
    let binary_path = extract_through_binary(&dbc, &data);
    assert_big_refused("JSON path", &json_path);
    assert_big_refused("binary path", &binary_path);
    assert_eq!(
        json_path.errors[0].reason, binary_path.errors[0].reason,
        "the two paths carry one reason"
    );
}
