// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed DBC document model — the Rust analogue of Python's `DBCDefinition`,
//! C++/Go's `DbcDefinition`/`DBCDefinition`.
//!
//! A [`Dbc`] is deserialized from the core's canonical JSON (the `dbc` field of
//! a `parseDBCText` / `formatDBC` response). The wire shapes are pinned by the
//! cross-binding corpus snapshots in
//! `python/tests/fixtures/dbc_corpus/parity_snapshots/`:
//!
//! - **rationals** (`factor`/`offset`/`minimum`/`maximum`) are a bare integer
//!   when the denominator is 1, else a `{"numerator","denominator"}` object —
//!   handled by [`crate::response::rational_from_value`].
//! - **presence** is flat: `"presence": "multiplexed"` plus sibling
//!   `"multiplexor"` / `"multiplex_values"` fields (modelled here as the typed
//!   [`Presence`] enum), or `"always"`.
//! - **extended** CAN ids carry a sibling `"extended": true` (absent ⇒ standard).
//!
//! This module is the *read* side (deserialize + queries + lookup). The
//! attribute vocabulary (`BA_DEF_` / `BA_` / `BA_DEF_DEF_`) is carried as
//! faithful pass-through [`serde_json::Value`] for now and will be typed in a
//! follow-on commit (its variant set is only partly exercised by the corpus).

use serde_json::Value;

use crate::error::Error;
use crate::response::ValidationIssue;
use crate::response::{parse_object, protocol, rational_from_value, str_field, u32_field};
use crate::types::{CanId, Rational};

// ── Leaf types ──────────────────────────────────────────────────────────────

/// Bit layout of a signal within the frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ByteOrder {
    /// Intel / little-endian (`@1` in `.dbc`).
    LittleEndian,
    /// Motorola / big-endian (`@0` in `.dbc`).
    BigEndian,
}

/// One `(value, description)` entry from a `VAL_` line or value table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDescription {
    /// The raw signal value.
    pub value: i64,
    /// Its human-readable meaning.
    pub description: String,
}

/// Whether a signal is always present, or multiplexed behind a selector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Presence {
    /// Present in every frame of the message.
    Always,
    /// Present only when `multiplexor`'s value is one of `values`.
    Multiplexed {
        /// Name of the controlling multiplexor signal.
        multiplexor: String,
        /// Selector values for which this signal is present (a list — the core
        /// and JSON path support multi-value selectors).
        values: Vec<u64>,
    },
}

// ── Signal / message ────────────────────────────────────────────────────────

/// A single signal within a message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DbcSignal {
    /// Signal name.
    pub name: String,
    /// Start bit position.
    pub start_bit: u32,
    /// Bit length.
    pub length: u32,
    /// Bit layout.
    pub byte_order: ByteOrder,
    /// Whether the raw value is two's-complement signed.
    pub signed: bool,
    /// Linear scaling factor (`physical = raw * factor + offset`).
    pub factor: Rational,
    /// Linear offset.
    pub offset: Rational,
    /// Declared physical minimum.
    pub minimum: Rational,
    /// Declared physical maximum.
    pub maximum: Rational,
    /// Engineering unit (may be empty).
    pub unit: String,
    /// Receiving nodes (the `SG_` line tail; `Vector__XXX` stripped on parse).
    pub receivers: Vec<String>,
    /// `VAL_` value descriptions attached to this signal.
    pub value_descriptions: Vec<ValueDescription>,
    /// Always-present vs multiplexed.
    pub presence: Presence,
}

/// A CAN message (a `BO_` block).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DbcMessage {
    /// Raw CAN identifier (11- or 29-bit value; see [`DbcMessage::can_id`]).
    pub id: u32,
    /// Whether the identifier is extended (29-bit).
    pub extended: bool,
    /// Message name.
    pub name: String,
    /// Data length (bytes).
    pub dlc: u32,
    /// Primary transmitter node.
    pub sender: String,
    /// Additional transmitters (`BO_TX_BU_`); the primary stays in `sender`.
    pub senders: Vec<String>,
    /// Signals carried by this message.
    pub signals: Vec<DbcSignal>,
}

// ── Top-level metadata ──────────────────────────────────────────────────────

/// A network node (`BU_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    /// Node name.
    pub name: String,
}

/// A named value table (`VAL_TABLE_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueTable {
    /// Table name.
    pub name: String,
    /// `(value, description)` entries.
    pub entries: Vec<ValueDescription>,
}

/// A signal group (`SIG_GROUP_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignalGroup {
    /// Group name.
    pub name: String,
    /// Member signal names.
    pub signals: Vec<String>,
}

/// An environment variable (`EV_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvironmentVar {
    /// Variable name.
    pub name: String,
    /// DBC `varType` discriminant (0=integer, 1=float, 2=string per the core).
    pub var_type: i64,
    /// Initial value.
    pub initial: Rational,
    /// Declared minimum.
    pub minimum: Rational,
    /// Declared maximum.
    pub maximum: Rational,
}

/// The entity a comment (`CM_`) is attached to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommentTarget {
    /// The whole network (`CM_ "...";`).
    Network,
    /// A node (`CM_ BU_ <node> "...";`).
    Node {
        /// Node name.
        node: String,
    },
    /// A message (`CM_ BO_ <id> "...";`).
    Message {
        /// Message CAN id.
        id: u32,
    },
    /// A signal (`CM_ SG_ <id> <signal> "...";`).
    Signal {
        /// Owning message CAN id.
        id: u32,
        /// Signal name.
        signal: String,
    },
    /// An environment variable (`CM_ EV_ <name> "...";`).
    EnvVar {
        /// Variable name.
        env_var: String,
    },
}

/// A comment (`CM_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment {
    /// What the comment is attached to.
    pub target: CommentTarget,
    /// The comment text.
    pub text: String,
}

/// A parsed DBC document.
///
/// `attributes` and `unresolved_value_descs` are carried as raw JSON
/// pass-through for now (see the module docs); every other field is typed.
#[derive(Debug, Clone, PartialEq)]
pub struct Dbc {
    /// `VERSION` string.
    pub version: String,
    /// Messages (`BO_`).
    pub messages: Vec<DbcMessage>,
    /// Nodes (`BU_`).
    pub nodes: Vec<Node>,
    /// Value tables (`VAL_TABLE_`).
    pub value_tables: Vec<ValueTable>,
    /// Environment variables (`EV_`).
    pub environment_vars: Vec<EnvironmentVar>,
    /// Signal groups (`SIG_GROUP_`).
    pub signal_groups: Vec<SignalGroup>,
    /// Comments (`CM_`).
    pub comments: Vec<Comment>,
    /// Attribute vocabulary (`BA_DEF_` / `BA_` / `BA_DEF_DEF_`) — raw JSON
    /// pass-through pending a typed model.
    pub attributes: Vec<Value>,
    /// Unresolved `VAL_` targets flagged by the validator — raw JSON pass-through.
    pub unresolved_value_descs: Vec<Value>,
}

// ── Decode helpers ──────────────────────────────────────────────────────────

fn arr<'a>(obj: &'a Value, key: &str) -> &'a [Value] {
    obj.get(key)
        .and_then(Value::as_array)
        .map_or(&[], Vec::as_slice)
}

fn str_array(obj: &Value, key: &str) -> Vec<String> {
    arr(obj, key)
        .iter()
        .filter_map(|v| v.as_str().map(ToString::to_string))
        .collect()
}

fn i64_field(obj: &Value, key: &str) -> Result<i64, Error> {
    obj.get(key)
        .and_then(Value::as_i64)
        .ok_or_else(|| protocol(format!("missing or non-integer field {key:?}")))
}

fn decode_value_descs(obj: &Value, key: &str) -> Result<Vec<ValueDescription>, Error> {
    arr(obj, key)
        .iter()
        .map(|v| {
            Ok(ValueDescription {
                value: i64_field(v, "value")?,
                description: str_field(v, "description"),
            })
        })
        .collect()
}

fn decode_presence(sig: &Value) -> Result<Presence, Error> {
    match str_field(sig, "presence").as_str() {
        "always" => Ok(Presence::Always),
        "multiplexed" => {
            let values = arr(sig, "multiplex_values")
                .iter()
                .map(|v| {
                    v.as_u64()
                        .ok_or_else(|| protocol("multiplex_values entry is not a u64"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Presence::Multiplexed {
                multiplexor: str_field(sig, "multiplexor"),
                values,
            })
        }
        other => Err(protocol(format!("unknown signal presence {other:?}"))),
    }
}

fn decode_byte_order(sig: &Value) -> Result<ByteOrder, Error> {
    match str_field(sig, "byteOrder").as_str() {
        "little_endian" => Ok(ByteOrder::LittleEndian),
        "big_endian" => Ok(ByteOrder::BigEndian),
        other => Err(protocol(format!("unknown byteOrder {other:?}"))),
    }
}

fn rational_field(obj: &Value, key: &str) -> Result<Rational, Error> {
    obj.get(key)
        .ok_or_else(|| protocol(format!("missing rational field {key:?}")))
        .and_then(rational_from_value)
}

fn decode_signal(sig: &Value) -> Result<DbcSignal, Error> {
    Ok(DbcSignal {
        name: str_field(sig, "name"),
        start_bit: u32_field(sig, "startBit")?,
        length: u32_field(sig, "length")?,
        byte_order: decode_byte_order(sig)?,
        signed: sig.get("signed").and_then(Value::as_bool).unwrap_or(false),
        factor: rational_field(sig, "factor")?,
        offset: rational_field(sig, "offset")?,
        minimum: rational_field(sig, "minimum")?,
        maximum: rational_field(sig, "maximum")?,
        unit: str_field(sig, "unit"),
        receivers: str_array(sig, "receivers"),
        value_descriptions: decode_value_descs(sig, "valueDescriptions")?,
        presence: decode_presence(sig)?,
    })
}

fn decode_message(msg: &Value) -> Result<DbcMessage, Error> {
    let signals = arr(msg, "signals")
        .iter()
        .map(decode_signal)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DbcMessage {
        id: u32_field(msg, "id")?,
        extended: msg
            .get("extended")
            .and_then(Value::as_bool)
            .unwrap_or(false),
        name: str_field(msg, "name"),
        dlc: u32_field(msg, "dlc")?,
        sender: str_field(msg, "sender"),
        senders: str_array(msg, "senders"),
        signals,
    })
}

fn decode_comment_target(t: &Value) -> Result<CommentTarget, Error> {
    match str_field(t, "kind").as_str() {
        "network" => Ok(CommentTarget::Network),
        "node" => Ok(CommentTarget::Node {
            node: str_field(t, "node"),
        }),
        "message" => Ok(CommentTarget::Message {
            id: u32_field(t, "id")?,
        }),
        "signal" => Ok(CommentTarget::Signal {
            id: u32_field(t, "id")?,
            signal: str_field(t, "signal"),
        }),
        "envVar" => Ok(CommentTarget::EnvVar {
            env_var: str_field(t, "envVar"),
        }),
        other => Err(protocol(format!("unknown comment target kind {other:?}"))),
    }
}

fn decode_comment(c: &Value) -> Result<Comment, Error> {
    let target = c
        .get("target")
        .ok_or_else(|| protocol("comment missing 'target'"))
        .and_then(decode_comment_target)?;
    Ok(Comment {
        target,
        text: str_field(c, "text"),
    })
}

fn decode_env_var(e: &Value) -> Result<EnvironmentVar, Error> {
    Ok(EnvironmentVar {
        name: str_field(e, "name"),
        var_type: i64_field(e, "varType")?,
        initial: rational_field(e, "initial")?,
        minimum: rational_field(e, "minimum")?,
        maximum: rational_field(e, "maximum")?,
    })
}

fn decode_value_table(t: &Value) -> Result<ValueTable, Error> {
    Ok(ValueTable {
        name: str_field(t, "name"),
        entries: decode_value_descs(t, "entries")?,
    })
}

fn map_array<T>(
    obj: &Value,
    key: &str,
    f: impl Fn(&Value) -> Result<T, Error>,
) -> Result<Vec<T>, Error> {
    arr(obj, key).iter().map(f).collect()
}

impl Dbc {
    /// Decode a [`Dbc`] from the canonical-JSON `dbc` object.
    pub(crate) fn from_value(obj: &Value) -> Result<Self, Error> {
        Ok(Dbc {
            version: str_field(obj, "version"),
            messages: map_array(obj, "messages", decode_message)?,
            nodes: arr(obj, "nodes")
                .iter()
                .map(|n| Node {
                    name: str_field(n, "name"),
                })
                .collect(),
            value_tables: map_array(obj, "valueTables", decode_value_table)?,
            environment_vars: map_array(obj, "environmentVars", decode_env_var)?,
            signal_groups: arr(obj, "signalGroups")
                .iter()
                .map(|g| SignalGroup {
                    name: str_field(g, "name"),
                    signals: str_array(g, "signals"),
                })
                .collect(),
            comments: map_array(obj, "comments", decode_comment)?,
            attributes: arr(obj, "attributes").to_vec(),
            unresolved_value_descs: arr(obj, "unresolvedValueDescs").to_vec(),
        })
    }
}

/// Decode a `parseDBCText` response into the typed document plus any validation
/// warnings the core reported.
pub(crate) fn decode_parsed_dbc(raw: &str) -> Result<(Dbc, Vec<ValidationIssue>), Error> {
    let obj = parse_object(raw)?;
    let dbc = obj
        .get("dbc")
        .ok_or_else(|| protocol("parse response missing 'dbc'"))
        .and_then(Dbc::from_value)?;
    let warnings = arr(&obj, "warnings")
        .iter()
        .map(|w| ValidationIssue {
            severity: str_field(w, "severity"),
            code: str_field(w, "code"),
            detail: str_field(w, "detail"),
        })
        .collect();
    Ok((dbc, warnings))
}

/// Decode a `formatDBC` response (`{"dbc": …}`) into the typed document.
pub(crate) fn decode_format_dbc(raw: &str) -> Result<Dbc, Error> {
    let obj = parse_object(raw)?;
    obj.get("dbc")
        .ok_or_else(|| protocol("formatDBC response missing 'dbc'"))
        .and_then(Dbc::from_value)
}

// ── Queries & lookups (the `dbc_queries_mux` / `dbc_lookup` rows) ────────────

impl DbcMessage {
    /// The typed CAN identifier (standard or extended).
    ///
    /// # Errors
    /// [`Error::Validation`] if the raw id is out of range for its width — which
    /// should not happen for a core-parsed message, but is surfaced rather than
    /// panicked.
    pub fn can_id(&self) -> Result<CanId, Error> {
        if self.extended {
            CanId::extended(self.id)
        } else {
            u16::try_from(self.id)
                .map_err(|_| Error::Validation(format!("standard id {} out of range", self.id)))
                .and_then(CanId::standard)
        }
    }

    /// Whether any signal in the message is multiplexed.
    #[must_use]
    pub fn is_multiplexed(&self) -> bool {
        self.signals
            .iter()
            .any(|s| matches!(s.presence, Presence::Multiplexed { .. }))
    }

    /// Signals that are present in every frame.
    #[must_use]
    pub fn always_present_signals(&self) -> Vec<&DbcSignal> {
        self.signals
            .iter()
            .filter(|s| matches!(s.presence, Presence::Always))
            .collect()
    }

    /// Signals whose presence is conditional on a multiplexor.
    #[must_use]
    pub fn multiplexed_signals(&self) -> Vec<&DbcSignal> {
        self.signals
            .iter()
            .filter(|s| matches!(s.presence, Presence::Multiplexed { .. }))
            .collect()
    }

    /// Distinct multiplexor names referenced by the message, in first-seen order.
    #[must_use]
    pub fn multiplexor_names(&self) -> Vec<&str> {
        let mut seen: Vec<&str> = Vec::new();
        for s in &self.signals {
            if let Presence::Multiplexed { multiplexor, .. } = &s.presence {
                if !seen.contains(&multiplexor.as_str()) {
                    seen.push(multiplexor);
                }
            }
        }
        seen
    }

    /// The selector values associated with `multiplexor` across the message's
    /// multiplexed signals, in first-seen order (deduplicated).
    #[must_use]
    pub fn multiplex_values(&self, multiplexor: &str) -> Vec<u64> {
        let mut out: Vec<u64> = Vec::new();
        for s in &self.signals {
            if let Presence::Multiplexed {
                multiplexor: m,
                values,
            } = &s.presence
            {
                if m == multiplexor {
                    for &v in values {
                        if !out.contains(&v) {
                            out.push(v);
                        }
                    }
                }
            }
        }
        out
    }

    /// Find a signal by name.
    #[must_use]
    pub fn signal_by_name(&self, name: &str) -> Option<&DbcSignal> {
        self.signals.iter().find(|s| s.name == name)
    }
}

impl Dbc {
    /// Find a message by raw CAN id.
    #[must_use]
    pub fn message_by_id(&self, id: u32) -> Option<&DbcMessage> {
        self.messages.iter().find(|m| m.id == id)
    }

    /// Find a message by name.
    #[must_use]
    pub fn message_by_name(&self, name: &str) -> Option<&DbcMessage> {
        self.messages.iter().find(|m| m.name == name)
    }
}

#[cfg(test)]
mod tests {
    use super::{Dbc, Presence};
    use serde_json::Value;

    macro_rules! snapshot {
        ($name:literal) => {
            include_str!(concat!(
                "../../python/tests/fixtures/dbc_corpus/parity_snapshots/",
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
            Dbc::from_value(&v)
                .unwrap_or_else(|e| panic!("snapshot {name} failed to decode: {e:?}"));
        }
    }

    #[test]
    fn multiplexing_presence_is_typed() {
        let d = decode(snapshot!("multiplexing"));
        let m = d.message_by_id(100).expect("message 100");
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
}
