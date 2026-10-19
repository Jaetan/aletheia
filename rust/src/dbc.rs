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
//! This module holds the full typed document family, including the `BA_*`
//! attribute vocabulary ([`Attribute`] / [`AttrType`] / [`AttrValue`] /
//! [`AttrScope`] / [`AttrTarget`]), and its queries and lookups; its `decode`
//! part reads the document from the canonical JSON and its `encode` part writes
//! it back. Only `unresolved_value_descs` stays raw-JSON pass-through (empty in
//! practice).

use serde_json::{json, Value};

use crate::error::Error;
use crate::response::ValidationIssue;
use crate::types::{CanId, Rational};

mod decode;
mod encode;

pub(crate) use decode::{decode_format_dbc, decode_parsed_dbc};

/// The optional `extended` flag on a CAN-id-bearing target (absent ⇒ standard).
fn extended_flag(t: &Value) -> bool {
    t.get("extended").and_then(Value::as_bool).unwrap_or(false)
}

/// Encode-side mirror of [`extended_flag`]: attach `"extended": true` only
/// when set (absent ⇒ standard ID, per the wire convention in the module doc).
fn set_extended(o: &mut Value, extended: bool) {
    if extended {
        o["extended"] = json!(true);
    }
}

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
        /// Whether the target id is extended (29-bit) — disambiguates a
        /// standard vs extended message sharing the same numeric id.
        extended: bool,
    },
    /// A signal (`CM_ SG_ <id> <signal> "...";`).
    Signal {
        /// Owning message CAN id.
        id: u32,
        /// Whether the owning message id is extended (29-bit).
        extended: bool,
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

// ── Attribute vocabulary (BA_DEF_ / BA_DEF_DEF_ / BA_) ───────────────────────

/// The entity class a `BA_DEF_` attribute definition scopes over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttrScope {
    /// Network-wide (`""`).
    Network,
    /// A node (`BU_`).
    Node,
    /// A message (`BO_`).
    Message,
    /// A signal (`SG_`).
    Signal,
    /// An environment variable (`EV_`).
    EnvVar,
    /// A (node, message) relation (`BU_BO_REL_`).
    NodeMsg,
    /// A (node, signal) relation (`BU_SG_REL_`).
    NodeSig,
}

/// The declared type of an attribute (`BA_DEF_`). `Int` / `Hex` bounds are
/// integers; `Float` bounds are exact rationals (matching the other bindings).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttrType {
    /// `INT min max`.
    Int {
        /// Inclusive minimum.
        min: i64,
        /// Inclusive maximum.
        max: i64,
    },
    /// `FLOAT min max` (rational bounds).
    Float {
        /// Inclusive minimum.
        min: Rational,
        /// Inclusive maximum.
        max: Rational,
    },
    /// `STRING`.
    String,
    /// `ENUM "a","b",…` carrying the ordered label list.
    Enum {
        /// The ordered enumeration labels.
        values: Vec<String>,
    },
    /// `HEX min max`.
    Hex {
        /// Inclusive minimum.
        min: i64,
        /// Inclusive maximum.
        max: i64,
    },
}

/// A concrete attribute value (`BA_` / `BA_DEF_DEF_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttrValue {
    /// Integer value.
    Int(i64),
    /// Float value (exact rational).
    Float(Rational),
    /// String value.
    String(String),
    /// Enum value: the 0-based index into the matching definition's labels.
    Enum(i64),
    /// Hex value.
    Hex(i64),
}

/// The target entity of an attribute assignment (`BA_` / `BA_REL_`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttrTarget {
    /// The whole network.
    Network,
    /// A node.
    Node {
        /// Node name.
        node: String,
    },
    /// A message.
    Message {
        /// Message CAN id.
        id: u32,
        /// Whether the id is extended (29-bit).
        extended: bool,
    },
    /// A signal.
    Signal {
        /// Owning message CAN id.
        id: u32,
        /// Whether the owning message id is extended (29-bit).
        extended: bool,
        /// Signal name.
        signal: String,
    },
    /// An environment variable.
    EnvVar {
        /// Variable name.
        env_var: String,
    },
    /// A (node, message) relation (`BA_REL_` `BU_BO_REL_`).
    NodeMsg {
        /// Node name.
        node: String,
        /// Message CAN id.
        id: u32,
        /// Whether the id is extended (29-bit).
        extended: bool,
    },
    /// A (node, signal) relation (`BA_REL_` `BU_SG_REL_`).
    NodeSig {
        /// Node name.
        node: String,
        /// Owning message CAN id.
        id: u32,
        /// Whether the owning message id is extended (29-bit).
        extended: bool,
        /// Signal name.
        signal: String,
    },
}

/// One `BA_*` attribute entry: a definition, a default, or an assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribute {
    /// `BA_DEF_` / `BA_DEF_REL_` — an attribute type declaration.
    Definition {
        /// Attribute name.
        name: String,
        /// Entity class the attribute scopes over.
        scope: AttrScope,
        /// Declared type.
        attr_type: AttrType,
    },
    /// `BA_DEF_DEF_` — the default value for an attribute.
    Default {
        /// Attribute name.
        name: String,
        /// Default value.
        value: AttrValue,
    },
    /// `BA_` / `BA_REL_` — a concrete value assignment to a target.
    Assignment {
        /// Attribute name.
        name: String,
        /// The entity the value is assigned to.
        target: AttrTarget,
        /// Assigned value.
        value: AttrValue,
    },
}

/// A parsed DBC document.
///
/// Every field is typed except `unresolved_value_descs`, which is carried as
/// raw JSON pass-through (it is empty for every well-formed DBC the core emits).
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
    /// Attribute vocabulary (`BA_DEF_` / `BA_DEF_DEF_` / `BA_`), in wire order.
    pub attributes: Vec<Attribute>,
    /// Unresolved `VAL_` targets flagged by the validator — raw JSON pass-through.
    pub unresolved_value_descs: Vec<Value>,
}

/// The success result of the parse methods
/// ([`Client::parse_dbc_text`](crate::Client::parse_dbc_text) /
/// [`Client::parse_dbc`](crate::Client::parse_dbc)): the canonical typed document
/// plus any non-error validation issues (warnings). Errors short-circuit to the
/// `Result<>::Err` path; this is only produced when the parse + structural
/// validation pass has zero error-severity issues.
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedDbc {
    /// The parsed, canonical typed DBC document.
    pub dbc: Dbc,
    /// Non-error validation issues (warnings), in report order.
    pub warnings: Vec<ValidationIssue>,
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
                .map_err(|_| Error::validation(format!("standard id {} out of range", self.id)))
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
    /// Find a message by CAN id, matching both the numeric value **and** the
    /// extended flag — so a standard and an extended message sharing the same
    /// numeric id are distinguished (mirrors Go `MessageByID` / Python
    /// `message_by_id(..., extended=)`).
    #[must_use]
    pub fn message_by_id(&self, id: CanId) -> Option<&DbcMessage> {
        self.messages
            .iter()
            .find(|m| m.id == id.value() && m.extended == id.is_extended())
    }

    /// Find a message by name.
    #[must_use]
    pub fn message_by_name(&self, name: &str) -> Option<&DbcMessage> {
        self.messages.iter().find(|m| m.name == name)
    }
}

#[cfg(test)]
mod tests;
