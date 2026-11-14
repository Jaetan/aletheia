// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

use super::{
    decode_format_dbc, AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder,
    CommentTarget, Dbc, Presence,
};
use crate::error::Error;
use crate::types::{CanId, Rational};
use crate::wire_json::{to_text, Wire};
use serde_json::{json, Value};

macro_rules! snapshot {
    ($name:literal) => {
        include_str!(concat!(
            "../../../python/tests/fixtures/dbc_corpus/parity_snapshots/",
            $name,
            ".json"
        ))
    };
}

const SNAPSHOTS: &[(&str, &str)] = &[
    ("minimal", snapshot!("minimal")),
    ("multiplexing", snapshot!("multiplexing")),
    ("value_tables", snapshot!("value_tables")),
    ("comments_groups", snapshot!("comments_groups")),
    ("env_vars", snapshot!("env_vars")),
    ("attributes", snapshot!("attributes")),
    ("extended_can", snapshot!("extended_can")),
    ("kitchen_sink", snapshot!("kitchen_sink")),
];

/// The DBC a `formatDBC` reply carrying `dbc`, the text of a DBC object,
/// reads to.
fn read(dbc: &str) -> Result<Dbc, Error> {
    decode_format_dbc(&format!(r#"{{"status":"success","dbc":{dbc}}}"#))
}

fn decode(json: &str) -> Dbc {
    read(json).expect("snapshot decodes to Dbc")
}

/// The DBC a reply carrying `v` reads to.
fn read_value(v: &Value) -> Result<Dbc, Error> {
    read(&v.to_string())
}

/// The kernel's JSON the writer gives `d`.
fn written(d: &Dbc) -> String {
    to_text(&Wire(d)).expect("a DBC is written")
}

/// Assert that `result` is the reply refusal printing `text`.
#[track_caller]
fn assert_refused(result: Result<Dbc, Error>, text: &str) {
    match result {
        Err(Error::Protocol(m)) => assert_eq!(m, text),
        other => panic!("expected the refusal {text:?}, got {other:?}"),
    }
}

/// Every committed corpus snapshot must decode: the empirical check that the
/// typed model matches the core's canonical wire shape (catches a wrong field
/// guess loudly rather than silently).
#[test]
fn all_corpus_snapshots_decode() {
    for (name, json) in SNAPSHOTS {
        read(json).unwrap_or_else(|e| panic!("snapshot {name} failed to decode: {e:?}"));
    }
}

/// The writer must be the exact inverse of the reader over the whole corpus,
/// in-process, so it reaches branches the all-standard kitchen_sink `.so`
/// round-trips can't: the `extended`-true path (extended_can) and every
/// attribute variant (attributes).
#[test]
fn serialize_round_trips_every_snapshot() {
    for (name, json) in SNAPSHOTS {
        let d = decode(json);
        let reparsed = read(&written(&d))
            .unwrap_or_else(|e| panic!("serialize round-trip {name} failed to re-decode: {e:?}"));
        assert_eq!(reparsed, d, "serialize round-trip mismatch for {name}");
    }
}

#[test]
fn multiplexing_presence_is_typed() {
    let d = decode(snapshot!("multiplexing"));
    let m = d
        .message_by_id(CanId::standard(100).expect("valid id"))
        .expect("message 100");
    assert!(m.is_multiplexed());
    let s = m.signal_by_name("PayloadA").expect("PayloadA");
    assert_eq!(
        s.presence,
        Presence::Multiplexed {
            multiplexor: "Mode".to_string(),
            values: vec![0]
        }
    );
    assert_eq!(m.multiplexor_names(), vec!["Mode"]);
    assert_eq!(m.multiplex_values("Mode"), vec![0_u128, 1, 2]);
}

#[test]
fn message_signals_split_by_presence() {
    let d = decode(snapshot!("multiplexing"));
    let m = d
        .message_by_id(CanId::standard(100).expect("valid id"))
        .expect("message 100");
    fn names(signals: Vec<&super::DbcSignal>) -> Vec<&str> {
        signals.iter().map(|s| s.name.as_str()).collect()
    }
    assert_eq!(
        names(m.always_present_signals()),
        vec!["Mode", "CommonCounter"]
    );
    assert_eq!(
        names(m.multiplexed_signals()),
        vec!["PayloadA", "PayloadB", "PayloadC"]
    );
    // A message with no multiplexor: every signal always present, none multiplexed.
    let plain = decode(snapshot!("minimal"));
    let engine = plain.message_by_name("EngineStatus").expect("EngineStatus");
    assert!(!engine.is_multiplexed());
    assert_eq!(engine.always_present_signals().len(), engine.signals.len());
    assert!(engine.multiplexed_signals().is_empty());
}

#[test]
fn message_by_name_finds_the_named_message_only() {
    let d = decode(snapshot!("minimal"));
    assert_eq!(
        d.message_by_name("BrakeStatus").map(|m| m.id),
        Some(512),
        "the second message, so a lookup that stops at the first is caught"
    );
    assert!(d.message_by_name("NoSuchMessage").is_none());
}

/// The multiplexing snapshot with `PayloadA`'s selector values written as
/// `member`, the member text in place of its `multiplex_values` key.
fn with_multiplex_values(member: &str) -> Result<Dbc, Error> {
    let mut v: Value = serde_json::from_str(snapshot!("multiplexing")).expect("valid JSON");
    let signal = v["messages"][0]["signals"][1]
        .as_object_mut()
        .expect("PayloadA");
    signal.remove("multiplex_values");
    signal.insert("@".to_string(), json!(0));
    read(&v.to_string().replace(r#""@":0"#, member))
}

#[test]
fn multiplex_values_are_whole_numbers_up_to_2_128_minus_1() {
    // Either end of the range and an empty array are read back; a value that
    // is not an array, an absent one, and an entry that is no natural number
    // or past 2^128-1 are refused at their place, as Go's reader refuses them.
    let read_back = |member: &str| match with_multiplex_values(member) {
        Ok(d) => d.messages[0].signals[1].presence.clone(),
        Err(e) => panic!("{member}: {e}"),
    };
    assert_eq!(
        read_back(r#""multiplex_values":[0,340282366920938463463374607431768211455]"#),
        Presence::Multiplexed {
            multiplexor: "Mode".to_string(),
            values: vec![0, u128::MAX],
        }
    );
    assert_eq!(
        read_back(r#""multiplex_values":[]"#),
        Presence::Multiplexed {
            multiplexor: "Mode".to_string(),
            values: Vec::new(),
        }
    );
    let place = "reply dbc/messages/signals/multiplex_values";
    for (member, refusal) in [
        (r#""multiplex_values":3"#, "expected array, got number"),
        (r#""absent":0"#, "expected array, got nothing"),
        (
            r#""multiplex_values":[340282366920938463463374607431768211456]"#,
            "expected number, got number",
        ),
        (r#""multiplex_values":[-1]"#, "expected number, got number"),
        (r#""multiplex_values":["3"]"#, "expected number, got string"),
        (
            r#""multiplex_values":[1,-1]"#,
            "expected number, got number",
        ),
    ] {
        assert_refused(
            with_multiplex_values(member),
            &format!("{place}: {refusal}"),
        );
    }
}

#[test]
fn a_comment_target_lacking_its_extended_flag_is_refused() {
    // The kernel writes the flag on every identifier, so each message and
    // signal comment target of the corpus carries it, false there; the flag
    // set true is read, and a target lacking it is refused at its place.
    let d = decode(snapshot!("comments_groups"));
    let on_ids: Vec<bool> =
        d.comments
            .iter()
            .filter_map(|c| match c.target {
                CommentTarget::Message { extended, .. }
                | CommentTarget::Signal { extended, .. } => Some(extended),
                _ => None,
            })
            .collect();
    assert!(!on_ids.is_empty() && on_ids.iter().all(|e| !e));
    let mut v: Value = serde_json::from_str(snapshot!("comments_groups")).expect("valid JSON");
    let target = &mut v["comments"]
        .as_array_mut()
        .expect("comments")
        .iter_mut()
        .find(|c| c["target"]["kind"] == "message")
        .expect("a message comment")["target"];
    target["extended"] = json!(true);
    let d = read_value(&v).expect("decodes");
    assert!(d
        .comments
        .iter()
        .any(|c| matches!(c.target, CommentTarget::Message { extended: true, .. })));
    let target = &mut v["comments"]
        .as_array_mut()
        .expect("comments")
        .iter_mut()
        .find(|c| c["target"]["kind"] == "message")
        .expect("a message comment")["target"];
    target.as_object_mut().expect("a target").remove("extended");
    assert_refused(
        read_value(&v),
        "reply dbc/comments/target/extended: expected boolean, got nothing",
    );
}

#[test]
fn extended_can_id_flag_decodes() {
    let d = decode(snapshot!("extended_can"));
    // At least one message is extended, at least one is standard.
    assert!(d.messages.iter().any(|m| m.extended));
    assert!(d.messages.iter().any(|m| !m.extended));
    for m in &d.messages {
        // can_id() must succeed for every core-parsed message.
        m.can_id().expect("valid CAN id");
    }
}

#[test]
fn message_by_id_disambiguates_standard_and_extended() {
    // extended_can.json carries both a standard and an extended message at
    // numeric id 256 — message_by_id must distinguish them by the flag.
    let d = decode(snapshot!("extended_can"));
    let std = d
        .message_by_id(CanId::standard(256).expect("valid std id"))
        .expect("standard message 256");
    assert!(!std.extended);
    let ext = d
        .message_by_id(CanId::extended(256).expect("valid ext id"))
        .expect("extended message 256");
    assert!(ext.extended);
    assert_ne!(std.name, ext.name, "the two id-256 messages are distinct");
}

#[test]
fn kitchen_sink_metadata_decodes() {
    let d = decode(snapshot!("kitchen_sink"));
    assert!(!d.nodes.is_empty(), "BU_ nodes");
    assert!(!d.comments.is_empty(), "CM_ comments");
    assert!(
        d.messages.iter().any(|m| !m.senders.is_empty()),
        "BO_TX_BU_ senders"
    );
    assert!(
        d.messages
            .iter()
            .flat_map(|m| &m.signals)
            .any(|s| !s.value_descriptions.is_empty()),
        "VAL_ value descriptions"
    );
}

#[test]
fn attributes_decode_to_typed_vocabulary() {
    // attributes.json exercises all 3 attr kinds, 5 attrType/attrValue kinds,
    // 7 scopes and 7 targets — spot-check the trickiest variants.
    let d = decode(snapshot!("attributes"));

    // Enum definition carries its ordered labels.
    let Some(Attribute::Definition {
        attr_type: AttrType::Enum { values },
        ..
    }) = d
        .attributes
        .iter()
        .find(|a| matches!(a, Attribute::Definition { name, .. } if name == "SignalPriority"))
    else {
        panic!("SignalPriority enum definition");
    };
    assert_eq!(*values, ["Low", "Normal", "High"].map(String::from));

    // A float-valued assignment carries an exact rational (85/2).
    let Some(Attribute::Assignment {
        value: AttrValue::Float(r),
        ..
    }) = d.attributes.iter().find(|a| {
        matches!(
            a,
            Attribute::Assignment {
                value: AttrValue::Float(_),
                ..
            }
        )
    })
    else {
        panic!("float-valued assignment");
    };
    assert_eq!(*r, Rational::new(85, 2).expect("valid rational"));

    // The relational (node, signal) target — the 7th, hardest variant.
    let Some(Attribute::Assignment {
        target: AttrTarget::NodeSig {
            node, id, signal, ..
        },
        ..
    }) = d.attributes.iter().find(|a| {
        matches!(
            a,
            Attribute::Assignment {
                target: AttrTarget::NodeSig { .. },
                ..
            }
        )
    })
    else {
        panic!("nodeSig-targeted assignment");
    };
    assert_eq!(
        (node.as_str(), *id, signal.as_str()),
        ("Sensor", 400, "Status")
    );
}

#[test]
fn each_scope_word_reads_to_its_scope() {
    // A scope read wrong is written back as itself, so neither the snapshots
    // nor the round trip see it: each word is read alone.
    for (word, scope) in [
        ("network", AttrScope::Network),
        ("node", AttrScope::Node),
        ("message", AttrScope::Message),
        ("signal", AttrScope::Signal),
        ("envVar", AttrScope::EnvVar),
        ("nodeMsg", AttrScope::NodeMsg),
        ("nodeSig", AttrScope::NodeSig),
    ] {
        let mut v: Value = serde_json::from_str(snapshot!("minimal")).expect("valid JSON");
        v["attributes"] = json!([{
            "kind": "definition",
            "name": "X",
            "scope": word,
            "attrType": { "kind": "string" }
        }]);
        let d = read_value(&v).expect("a definition decodes");
        let Some(Attribute::Definition { scope: read, .. }) = d.attributes.first() else {
            panic!("{word}: a definition");
        };
        assert_eq!(*read, scope, "{word}");
    }
}

#[test]
fn extended_target_decodes_extended_true() {
    // No corpus fixture has an extended attribute/comment target (all are
    // standard ids), so pin extended_flag's true-path directly — otherwise a
    // misnamed/mishandled flag would silently read false (the extended-id
    // conflation bug-class fixed for message_by_id in the read-side slice).
    let mut v: Value = serde_json::from_str(snapshot!("minimal")).expect("valid JSON");
    v["attributes"] = json!([{
        "kind": "assignment",
        "name": "X",
        "target": { "kind": "message", "id": 77, "extended": true },
        "value": { "kind": "int", "value": 1 }
    }]);
    let d = read_value(&v).expect("decode an extended-target attribute");
    let Some(Attribute::Assignment {
        target: AttrTarget::Message { id, extended },
        ..
    }) = d.attributes.first()
    else {
        panic!("message-targeted assignment");
    };
    assert_eq!((*id, *extended), (77, true));

    // And the writer keeps extended-true on the target, which no snapshot
    // reaches.
    assert_eq!(read(&written(&d)).expect("serialize round-trip"), d);
    let back: Value = serde_json::from_str(&written(&d)).expect("valid JSON");
    assert_eq!(back["attributes"][0]["target"]["extended"], json!(true));
}

#[test]
fn rational_object_form_round_trips() {
    // minimal.json carries a non-integer rational ({numerator,denominator}).
    let d = decode(snapshot!("minimal"));
    let has_fraction = d.messages.iter().flat_map(|m| &m.signals).any(|s| {
        [s.factor, s.offset, s.minimum, s.maximum]
            .iter()
            .any(|r| r.denominator() != 1)
    });
    assert!(
        has_fraction,
        "minimal should exercise a fractional rational"
    );
}

// ── The reader reads each place by kind: the kernel proves every range ──
// Each case edits the first message of the minimal snapshot, or its first
// signal, and reads the reply whole, so the refusal names its place from the
// reply's root.

/// The minimal snapshot with its first message edited by `edit`, read.
fn with_message(edit: impl FnOnce(&mut Value)) -> Result<Dbc, Error> {
    let mut v: Value = serde_json::from_str(snapshot!("minimal")).expect("valid JSON");
    edit(&mut v["messages"][0]);
    read_value(&v)
}

/// The minimal snapshot with its first signal edited by `edit`, read.
fn with_signal(edit: impl FnOnce(&mut Value)) -> Result<Dbc, Error> {
    with_message(|m| edit(&mut m["signals"][0]))
}

#[test]
fn a_message_identifier_is_read_at_the_width_its_flag_names() {
    // Either end of each width is read back; a negative one, no natural
    // number, is refused at its place whichever its flag.
    for (id, extended) in [(0, false), (0x7FF, false), (0x1FFF_FFFF, true)] {
        let d = with_message(|m| {
            m["id"] = json!(id);
            m["extended"] = json!(extended);
        })
        .unwrap_or_else(|e| panic!("{id}: {e}"));
        let m = &d.messages[0];
        assert_eq!((m.id, m.extended), (id, extended));
        let can_id = m.can_id().expect("a valid identifier");
        assert_eq!((can_id.value(), can_id.is_extended()), (id, extended));
    }
    for extended in [false, true] {
        assert_refused(
            with_message(|m| {
                m["id"] = json!(-1);
                m["extended"] = json!(extended);
            }),
            "reply dbc/messages/id: expected number, got number",
        );
    }
}

#[test]
fn message_rejects_invalid_dlc_byte_count() {
    // 9 is no CAN/CAN-FD byte count, so no length code stands for it.
    assert_refused(
        with_message(|m| m["dlc"] = json!(9)),
        "reply dbc/messages/dlc: expected number, got number",
    );
}

#[test]
fn message_accepts_canfd_dlc_byte_count() {
    let d = with_message(|m| m["dlc"] = json!(64)).expect("valid CAN-FD length");
    assert_eq!(d.messages[0].dlc, 64);
}

#[test]
fn message_rejects_non_bool_extended() {
    assert_refused(
        with_message(|m| m["extended"] = json!("true")),
        "reply dbc/messages/extended: expected boolean, got string",
    );
}

#[test]
fn a_signal_start_bit_is_read_anywhere_in_the_largest_frame() {
    // Either end of a CAN-FD frame's 512 bits is read back; a negative bit, no
    // natural number, is refused at its place.
    for bit in [0, 511] {
        let d = with_signal(|s| s["startBit"] = json!(bit)).expect("a start bit");
        assert_eq!(d.messages[0].signals[0].start_bit, bit);
    }
    assert_refused(
        with_signal(|s| s["startBit"] = json!(-1)),
        "reply dbc/messages/signals/startBit: expected number, got number",
    );
}

#[test]
fn a_signal_length_is_read_back_at_either_end() {
    for length in [1, 512] {
        let d = with_signal(|s| s["length"] = json!(length)).expect("a length");
        assert_eq!(d.messages[0].signals[0].length, length);
    }
}

#[test]
fn presence_rejects_multiplexed_with_missing_values() {
    assert_refused(
        with_signal(|s| {
            s["presence"] = json!("multiplexed");
            s["multiplexor"] = json!("Mode");
        }),
        "reply dbc/messages/signals/multiplex_values: expected array, got nothing",
    );
}

#[test]
fn presence_accepts_multiplexed_with_values() {
    let d = with_signal(|s| {
        s["presence"] = json!("multiplexed");
        s["multiplexor"] = json!("Mode");
        s["multiplex_values"] = json!([0, 1]);
    })
    .expect("a multiplexed signal");
    assert_eq!(
        d.messages[0].signals[0].presence,
        Presence::Multiplexed {
            multiplexor: "Mode".to_string(),
            values: vec![0, 1],
        }
    );
}

#[test]
fn a_presence_outside_always_and_multiplexed_is_refused_at_its_place() {
    // The signal carries a multiplexor and its selector values, so the word
    // alone is refused.
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_signal(|s| {
                s["presence"] = word;
                s["multiplexor"] = json!("Mode");
                s["multiplex_values"] = json!([2]);
            }),
            &format!(
                r#"reply dbc/messages/signals/presence: expected "always" or "multiplexed", got {came}"#
            ),
        );
    }
}

#[test]
fn a_byte_order_is_read_as_its_word() {
    for (word, order) in [
        ("little_endian", ByteOrder::LittleEndian),
        ("big_endian", ByteOrder::BigEndian),
    ] {
        let d = with_signal(|s| s["byteOrder"] = json!(word)).expect("a byte order");
        assert_eq!(d.messages[0].signals[0].byte_order, order, "{word}");
    }
}

#[test]
fn a_byte_order_outside_little_endian_and_big_endian_is_refused_at_its_place() {
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_signal(|s| s["byteOrder"] = word),
            &format!(
                r#"reply dbc/messages/signals/byteOrder: expected "little_endian" or "big_endian", got {came}"#
            ),
        );
    }
}

/// The minimal snapshot with its `key` list set to `entries`, read.
fn with_entries(key: &str, entries: Value) -> Result<Dbc, Error> {
    let mut v: Value = serde_json::from_str(snapshot!("minimal")).expect("valid JSON");
    v[key] = entries;
    read_value(&v)
}

#[test]
fn a_comment_target_kind_outside_its_words_is_refused_at_its_place() {
    // The target carries the environment variable the last word names, so the
    // word alone is refused.
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_entries(
                "comments",
                json!([{ "target": { "kind": word, "envVar": "E" }, "text": "t" }]),
            ),
            &format!(
                r#"reply dbc/comments/target/kind: expected "network", "node", "message", "signal" or "envVar", got {came}"#
            ),
        );
    }
}

#[test]
fn an_attribute_kind_outside_its_words_is_refused_at_its_place() {
    // The entry carries the target and value of an assignment, the last word,
    // so the word alone is refused.
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_entries(
                "attributes",
                json!([{
                    "kind": word,
                    "name": "X",
                    "target": { "kind": "network" },
                    "value": { "kind": "int", "value": 1 }
                }]),
            ),
            &format!(
                r#"reply dbc/attributes/kind: expected "definition", "default" or "assignment", got {came}"#
            ),
        );
    }
}

#[test]
fn an_attribute_scope_outside_its_words_is_refused_at_its_place() {
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_entries(
                "attributes",
                json!([{
                    "kind": "definition",
                    "name": "X",
                    "scope": word,
                    "attrType": { "kind": "string" }
                }]),
            ),
            &format!(
                r#"reply dbc/attributes/scope: expected "network", "node", "message", "signal", "envVar", "nodeMsg" or "nodeSig", got {came}"#
            ),
        );
    }
}

#[test]
fn an_attribute_type_kind_outside_its_words_is_refused_at_its_place() {
    // The type carries the bounds of a hex type, the last word, so the word
    // alone is refused.
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_entries(
                "attributes",
                json!([{
                    "kind": "definition",
                    "name": "X",
                    "scope": "network",
                    "attrType": { "kind": word, "min": 0, "max": 1 }
                }]),
            ),
            &format!(
                r#"reply dbc/attributes/attrType/kind: expected "int", "float", "string", "enum" or "hex", got {came}"#
            ),
        );
    }
}

#[test]
fn an_attribute_value_kind_outside_its_words_is_refused_at_its_place() {
    // The value carries the integer of a hex value, the last word, so the word
    // alone is refused.
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_entries(
                "attributes",
                json!([{
                    "kind": "default",
                    "name": "X",
                    "value": { "kind": word, "value": 1 }
                }]),
            ),
            &format!(
                r#"reply dbc/attributes/value/kind: expected "int", "float", "string", "enum" or "hex", got {came}"#
            ),
        );
    }
}

#[test]
fn an_attribute_target_kind_outside_its_words_is_refused_at_its_place() {
    // The target carries the node, CAN id and signal of a nodeSig target, the
    // last word, so the word alone is refused.
    for (word, came) in [
        (json!("bogus_word"), r#""bogus_word""#),
        (json!(0), "number"),
    ] {
        assert_refused(
            with_entries(
                "attributes",
                json!([{
                    "kind": "assignment",
                    "name": "X",
                    "target": {
                        "kind": word,
                        "node": "N",
                        "id": 1,
                        "extended": false,
                        "signal": "S"
                    },
                    "value": { "kind": "int", "value": 1 }
                }]),
            ),
            &format!(
                r#"reply dbc/attributes/target/kind: expected "network", "node", "message", "signal", "envVar", "nodeMsg" or "nodeSig", got {came}"#
            ),
        );
    }
}

#[test]
fn env_var_types_are_read_back() {
    let d = decode(snapshot!("env_vars"));
    let types: Vec<i64> = d.environment_vars.iter().map(|e| e.var_type).collect();
    assert_eq!(types, vec![1, 0, 2]);
}
