// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

use super::{AttrTarget, AttrType, AttrValue, Attribute, CommentTarget, Dbc, Presence};
use crate::types::{CanId, Rational};
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

fn decode(json: &str) -> Dbc {
    let v: Value = serde_json::from_str(json).expect("snapshot is valid JSON");
    Dbc::from_value(&v).expect("snapshot decodes to Dbc")
}

/// Every committed corpus snapshot must decode — the empirical check that the
/// typed model matches the core's canonical wire shape (catches a wrong field
/// guess loudly rather than silently).
#[test]
fn all_corpus_snapshots_decode() {
    for (name, json) in SNAPSHOTS {
        let v: Value = serde_json::from_str(json).expect("valid JSON");
        Dbc::from_value(&v).unwrap_or_else(|e| panic!("snapshot {name} failed to decode: {e:?}"));
    }
}

/// `to_value` must be the exact inverse of `from_value` over the whole
/// corpus — in-process, so it reaches branches the all-standard kitchen_sink
/// `.so` round-trips can't: the `extended`-true serialize path (extended_can)
/// and every attribute variant (attributes).
#[test]
fn serialize_round_trips_every_snapshot() {
    for (name, json) in SNAPSHOTS {
        let d = decode(json);
        let reparsed = Dbc::from_value(&d.to_value())
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
    assert_eq!(m.multiplex_values("Mode"), vec![0_u64, 1, 2]);
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

#[test]
fn multiplex_value_at_the_u32_maximum_is_accepted() {
    // The kernel's selector values are u32; the decoder refuses a value past
    // the maximum and accepts the maximum itself.
    let mut v: Value = serde_json::from_str(snapshot!("multiplexing")).expect("valid JSON");
    v["messages"][0]["signals"][1]["multiplex_values"] = json!([u32::MAX]);
    let d = Dbc::from_value(&v).expect("u32::MAX is a valid selector value");
    assert_eq!(
        d.messages[0].signals[1].presence,
        Presence::Multiplexed {
            multiplexor: "Mode".to_string(),
            values: vec![u64::from(u32::MAX)]
        }
    );
    v["messages"][0]["signals"][1]["multiplex_values"] = json!([u64::from(u32::MAX) + 1]);
    assert!(Dbc::from_value(&v).is_err());
}

#[test]
fn comment_target_extended_flag_defaults_to_standard() {
    // The corpus writes no `extended` key on its message and signal comment
    // targets, so each decodes as a standard id; the key set true is read.
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
    let target = v["comments"]
        .as_array_mut()
        .expect("comments")
        .iter_mut()
        .find(|c| c["target"]["kind"] == "message")
        .expect("a message comment");
    target["target"]["extended"] = json!(true);
    let d = Dbc::from_value(&v).expect("decodes");
    assert!(d
        .comments
        .iter()
        .any(|c| matches!(c.target, CommentTarget::Message { extended: true, .. })));
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
fn extended_target_decodes_extended_true() {
    // No corpus fixture has an extended attribute/comment target (all are
    // standard ids), so pin extended_flag's true-path directly — otherwise a
    // misnamed/mishandled flag would silently read false (the extended-id
    // conflation bug-class fixed for message_by_id in the read-side slice).
    let v = json!({
        "attributes": [{
            "kind": "assignment",
            "name": "X",
            "target": { "kind": "message", "id": 77, "extended": true },
            "value": { "kind": "int", "value": 1 }
        }]
    });
    let d = Dbc::from_value(&v).expect("decode minimal extended-target attribute");
    let Some(Attribute::Assignment {
        target: AttrTarget::Message { id, extended },
        ..
    }) = d.attributes.first()
    else {
        panic!("message-targeted assignment");
    };
    assert_eq!((*id, *extended), (77, true));

    // And the serialize side preserves extended-true on the target (the
    // `set_extended` call in attr_target_to_value, which no snapshot hits).
    assert_eq!(
        Dbc::from_value(&d.to_value()).expect("serialize round-trip"),
        d
    );
    assert_eq!(
        d.to_value()["attributes"][0]["target"]["extended"],
        json!(true)
    );
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

// ── decode-validation: reject malformed core output (positive + rejection cases) ──
// These call the private decoders directly; the corpus snapshots above are the
// positive end-to-end witness that the core's own output still decodes.
use super::decode::{decode_env_var, decode_message, decode_presence, decode_signal};

fn valid_signal() -> Value {
    json!({
        "name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
        "signed": false, "factor": 1, "offset": 0, "minimum": 0, "maximum": 100,
        "unit": "", "receivers": [], "valueDescriptions": [], "presence": "always"
    })
}

fn valid_message() -> Value {
    json!({
        "id": 0x100, "extended": false, "name": "M", "dlc": 8,
        "sender": "", "senders": [], "signals": []
    })
}

fn valid_env_var() -> Value {
    json!({ "name": "E", "varType": 0, "initial": 0, "minimum": 0, "maximum": 10 })
}

// message id range (per `extended`) + DLC byte-count
#[test]
fn message_rejects_standard_id_over_11_bits() {
    let mut m = valid_message();
    m["id"] = json!(0x800); // 2048 > MAX_STANDARD_ID (0x7FF)
    assert!(decode_message(&m).is_err());
}

#[test]
fn message_accepts_max_standard_id() {
    let mut m = valid_message();
    m["id"] = json!(0x7FF);
    assert!(decode_message(&m).is_ok());
}

#[test]
fn message_rejects_extended_id_over_29_bits() {
    let mut m = valid_message();
    m["extended"] = json!(true);
    m["id"] = json!(0x2000_0000u64); // 1<<29 > MAX_EXTENDED_ID (0x1FFFFFFF)
    assert!(decode_message(&m).is_err());
}

#[test]
fn message_accepts_max_extended_id() {
    let mut m = valid_message();
    m["extended"] = json!(true);
    m["id"] = json!(0x1FFF_FFFFu64);
    assert!(decode_message(&m).is_ok());
}

#[test]
fn message_rejects_invalid_dlc_byte_count() {
    let mut m = valid_message();
    m["dlc"] = json!(9); // 9 is not a valid CAN/CAN-FD byte count
    assert!(decode_message(&m).is_err());
}

#[test]
fn message_accepts_canfd_dlc_byte_count() {
    let mut m = valid_message();
    m["dlc"] = json!(64); // valid CAN-FD length
    assert!(decode_message(&m).is_ok());
}

#[test]
fn message_rejects_non_bool_extended() {
    let mut m = valid_message();
    m["extended"] = json!("true"); // string, not bool
    assert!(decode_message(&m).is_err());
}

// signal startBit 0-511 / length 1-512 (the type-level ceiling: the
// largest CAN-FD frame; per-frame fit is the kernel's entry-gate check)
#[test]
fn signal_rejects_start_bit_over_511() {
    let mut s = valid_signal();
    s["startBit"] = json!(512);
    assert!(decode_signal(&s).is_err());
}

#[test]
fn signal_accepts_max_start_bit() {
    let mut s = valid_signal();
    s["startBit"] = json!(511);
    assert!(decode_signal(&s).is_ok());
}

#[test]
fn signal_rejects_zero_length() {
    let mut s = valid_signal();
    s["length"] = json!(0);
    assert!(decode_signal(&s).is_err());
}

#[test]
fn signal_rejects_length_over_512() {
    let mut s = valid_signal();
    s["length"] = json!(513);
    assert!(decode_signal(&s).is_err());
}

#[test]
fn signal_accepts_max_length() {
    let mut s = valid_signal();
    s["length"] = json!(512);
    assert!(decode_signal(&s).is_ok());
}

#[test]
fn signal_accepts_min_length() {
    let mut s = valid_signal();
    s["length"] = json!(1); // minimum valid length (lower boundary)
    assert!(decode_signal(&s).is_ok());
}

// multiplexed presence requires non-empty multiplexor + values
#[test]
fn presence_rejects_multiplexed_with_empty_values() {
    let sig = json!({ "presence": "multiplexed", "multiplexor": "Mode", "multiplex_values": [] });
    assert!(decode_presence(&sig).is_err());
}

#[test]
fn presence_rejects_multiplexed_with_missing_values() {
    let sig = json!({ "presence": "multiplexed", "multiplexor": "Mode" });
    assert!(decode_presence(&sig).is_err());
}

#[test]
fn presence_rejects_multiplexed_with_empty_multiplexor() {
    let sig = json!({ "presence": "multiplexed", "multiplexor": "", "multiplex_values": [0] });
    assert!(decode_presence(&sig).is_err());
}

#[test]
fn presence_accepts_multiplexed_with_values() {
    let sig =
        json!({ "presence": "multiplexed", "multiplexor": "Mode", "multiplex_values": [0, 1] });
    assert!(matches!(
        decode_presence(&sig),
        Ok(Presence::Multiplexed { .. })
    ));
}

// multiplex_values entries are bounded to u32 (cross-binding parity with Go)
#[test]
fn presence_rejects_multiplex_value_over_u32() {
    let sig = json!({
        "presence": "multiplexed",
        "multiplexor": "Mode",
        "multiplex_values": [5_000_000_000_u64], // > u32::MAX
    });
    assert!(decode_presence(&sig).is_err());
}

// unknown presence discriminator rejected
#[test]
fn presence_rejects_unknown_discriminator() {
    let sig = json!({ "presence": "sometimes" });
    assert!(decode_presence(&sig).is_err());
}

// environment-variable varType 0-2
#[test]
fn env_var_rejects_var_type_out_of_range() {
    let mut e = valid_env_var();
    e["varType"] = json!(3);
    assert!(decode_env_var(&e).is_err());
}

#[test]
fn env_var_accepts_var_type_boundaries() {
    for vt in 0..=2 {
        let mut e = valid_env_var();
        e["varType"] = json!(vt);
        assert!(decode_env_var(&e).is_ok(), "varType {vt} should decode");
    }
}
