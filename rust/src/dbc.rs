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
//! This module is the *read* side (deserialize + queries + lookup): the full
//! typed document family, including the `BA_*` attribute vocabulary
//! ([`Attribute`] / [`AttrType`] / [`AttrValue`] / [`AttrScope`] / [`AttrTarget`]).
//! Only `unresolved_value_descs` stays raw-JSON pass-through (empty in practice).

use serde_json::{json, Value};

use crate::error::Error;
use crate::response::ValidationIssue;
use crate::response::{parse_object, protocol, rational_from_value, str_field, u32_field};
use crate::types::{CanId, Dlc, Rational, MAX_EXTENDED_ID, MAX_STANDARD_ID};

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
            let multiplexor = str_field(sig, "multiplexor");
            if multiplexor.is_empty() {
                return Err(protocol(
                    "multiplexed signal requires a non-empty \"multiplexor\"",
                ));
            }
            let raw = arr(sig, "multiplex_values");
            if raw.is_empty() {
                return Err(protocol(
                    "multiplexed signal requires a non-empty \"multiplex_values\" array",
                ));
            }
            let values = raw
                .iter()
                .map(|v| {
                    let n = v
                        .as_u64()
                        .ok_or_else(|| protocol("multiplex_values entry is not a u64"))?;
                    if n > u64::from(u32::MAX) {
                        return Err(protocol(format!(
                            "multiplex_values entry {n} exceeds u32 range (0-{})",
                            u32::MAX
                        )));
                    }
                    Ok(n)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Presence::Multiplexed {
                multiplexor,
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
    let start_bit = u32_field(sig, "startBit")?;
    if start_bit > 511 {
        return Err(protocol(format!(
            "startBit {start_bit} out of range (0-511)"
        )));
    }
    let length = u32_field(sig, "length")?;
    if !(1..=64).contains(&length) {
        return Err(protocol(format!("bit length {length} out of range (1-64)")));
    }
    Ok(DbcSignal {
        name: str_field(sig, "name"),
        start_bit,
        length,
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
    let extended = match msg.get("extended") {
        None => false,
        Some(v) => v
            .as_bool()
            .ok_or_else(|| protocol("message \"extended\" must be a boolean"))?,
    };
    let id = u32_field(msg, "id")?;
    let max_id = if extended {
        MAX_EXTENDED_ID
    } else {
        u32::from(MAX_STANDARD_ID)
    };
    if id > max_id {
        return Err(protocol(format!(
            "CAN ID {id} exceeds {bits}-bit range (0-{max_id})",
            bits = if extended { 29 } else { 11 }
        )));
    }
    let dlc = u32_field(msg, "dlc")?;
    Dlc::from_bytes(dlc as usize).map_err(|_| {
        protocol(format!(
            "DLC byte count {dlc} is not a valid CAN/CAN-FD length"
        ))
    })?;
    Ok(DbcMessage {
        id,
        extended,
        name: str_field(msg, "name"),
        dlc,
        sender: str_field(msg, "sender"),
        senders: str_array(msg, "senders"),
        signals,
    })
}

/// The optional `extended` flag on a CAN-id-bearing target (absent ⇒ standard).
fn extended_flag(t: &Value) -> bool {
    t.get("extended").and_then(Value::as_bool).unwrap_or(false)
}

fn decode_comment_target(t: &Value) -> Result<CommentTarget, Error> {
    match str_field(t, "kind").as_str() {
        "network" => Ok(CommentTarget::Network),
        "node" => Ok(CommentTarget::Node {
            node: str_field(t, "node"),
        }),
        "message" => Ok(CommentTarget::Message {
            id: u32_field(t, "id")?,
            extended: extended_flag(t),
        }),
        "signal" => Ok(CommentTarget::Signal {
            id: u32_field(t, "id")?,
            extended: extended_flag(t),
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

fn decode_attr_scope(s: &str) -> Result<AttrScope, Error> {
    match s {
        "network" => Ok(AttrScope::Network),
        "node" => Ok(AttrScope::Node),
        "message" => Ok(AttrScope::Message),
        "signal" => Ok(AttrScope::Signal),
        "envVar" => Ok(AttrScope::EnvVar),
        "nodeMsg" => Ok(AttrScope::NodeMsg),
        "nodeSig" => Ok(AttrScope::NodeSig),
        other => Err(protocol(format!("unknown attribute scope {other:?}"))),
    }
}

fn decode_attr_type(t: &Value) -> Result<AttrType, Error> {
    match str_field(t, "kind").as_str() {
        "int" => Ok(AttrType::Int {
            min: i64_field(t, "min")?,
            max: i64_field(t, "max")?,
        }),
        "float" => Ok(AttrType::Float {
            min: rational_field(t, "min")?,
            max: rational_field(t, "max")?,
        }),
        "string" => Ok(AttrType::String),
        "enum" => Ok(AttrType::Enum {
            values: str_array(t, "values"),
        }),
        "hex" => Ok(AttrType::Hex {
            min: i64_field(t, "min")?,
            max: i64_field(t, "max")?,
        }),
        other => Err(protocol(format!("unknown attribute type kind {other:?}"))),
    }
}

fn decode_attr_value(v: &Value) -> Result<AttrValue, Error> {
    match str_field(v, "kind").as_str() {
        "int" => Ok(AttrValue::Int(i64_field(v, "value")?)),
        "float" => Ok(AttrValue::Float(rational_field(v, "value")?)),
        "string" => Ok(AttrValue::String(str_field(v, "value"))),
        "enum" => Ok(AttrValue::Enum(i64_field(v, "value")?)),
        "hex" => Ok(AttrValue::Hex(i64_field(v, "value")?)),
        other => Err(protocol(format!("unknown attribute value kind {other:?}"))),
    }
}

fn decode_attr_target(t: &Value) -> Result<AttrTarget, Error> {
    match str_field(t, "kind").as_str() {
        "network" => Ok(AttrTarget::Network),
        "node" => Ok(AttrTarget::Node {
            node: str_field(t, "node"),
        }),
        "message" => Ok(AttrTarget::Message {
            id: u32_field(t, "id")?,
            extended: extended_flag(t),
        }),
        "signal" => Ok(AttrTarget::Signal {
            id: u32_field(t, "id")?,
            extended: extended_flag(t),
            signal: str_field(t, "signal"),
        }),
        "envVar" => Ok(AttrTarget::EnvVar {
            env_var: str_field(t, "envVar"),
        }),
        "nodeMsg" => Ok(AttrTarget::NodeMsg {
            node: str_field(t, "node"),
            id: u32_field(t, "id")?,
            extended: extended_flag(t),
        }),
        "nodeSig" => Ok(AttrTarget::NodeSig {
            node: str_field(t, "node"),
            id: u32_field(t, "id")?,
            extended: extended_flag(t),
            signal: str_field(t, "signal"),
        }),
        other => Err(protocol(format!("unknown attribute target kind {other:?}"))),
    }
}

fn decode_attribute(a: &Value) -> Result<Attribute, Error> {
    match str_field(a, "kind").as_str() {
        "definition" => Ok(Attribute::Definition {
            name: str_field(a, "name"),
            scope: decode_attr_scope(&str_field(a, "scope"))?,
            attr_type: a
                .get("attrType")
                .ok_or_else(|| protocol("attribute definition missing 'attrType'"))
                .and_then(decode_attr_type)?,
        }),
        "default" => Ok(Attribute::Default {
            name: str_field(a, "name"),
            value: a
                .get("value")
                .ok_or_else(|| protocol("attribute default missing 'value'"))
                .and_then(decode_attr_value)?,
        }),
        "assignment" => Ok(Attribute::Assignment {
            name: str_field(a, "name"),
            target: a
                .get("target")
                .ok_or_else(|| protocol("attribute assignment missing 'target'"))
                .and_then(decode_attr_target)?,
            value: a
                .get("value")
                .ok_or_else(|| protocol("attribute assignment missing 'value'"))
                .and_then(decode_attr_value)?,
        }),
        other => Err(protocol(format!("unknown attribute kind {other:?}"))),
    }
}

fn decode_env_var(e: &Value) -> Result<EnvironmentVar, Error> {
    let var_type = i64_field(e, "varType")?;
    if !(0..=2).contains(&var_type) {
        return Err(protocol(format!(
            "environment variable varType {var_type} out of range (0-2)"
        )));
    }
    Ok(EnvironmentVar {
        name: str_field(e, "name"),
        var_type,
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
            attributes: map_array(obj, "attributes", decode_attribute)?,
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
        .map(crate::response::decode_issue)
        .collect::<Result<Vec<_>, Error>>()?;
    Ok((dbc, warnings))
}

/// Decode a `formatDBC` response (`{"dbc": …}`) into the typed document.
pub(crate) fn decode_format_dbc(raw: &str) -> Result<Dbc, Error> {
    let obj = parse_object(raw)?;
    obj.get("dbc")
        .ok_or_else(|| protocol("formatDBC response missing 'dbc'"))
        .and_then(Dbc::from_value)
}

// ── Serialize (Dbc → canonical JSON, the inverse of the decoders above) ──────
//
// Mirrors the wire shapes pinned by the corpus snapshots: `Rational::to_value`
// emits a bare integer when the denominator is 1; presence is flat; the
// `extended` flag and the empty `unresolved_value_descs` follow the core's
// emit-only-when-meaningful convention (`extended` omitted when false).

fn byte_order_str(b: ByteOrder) -> &'static str {
    match b {
        ByteOrder::LittleEndian => "little_endian",
        ByteOrder::BigEndian => "big_endian",
    }
}

fn value_descs_to_value(vds: &[ValueDescription]) -> Value {
    Value::Array(
        vds.iter()
            .map(|vd| json!({ "value": vd.value, "description": vd.description }))
            .collect(),
    )
}

fn signal_to_value(s: &DbcSignal) -> Value {
    let mut o = json!({
        "name": s.name,
        "startBit": s.start_bit,
        "length": s.length,
        "byteOrder": byte_order_str(s.byte_order),
        "signed": s.signed,
        "factor": s.factor.to_value(),
        "offset": s.offset.to_value(),
        "minimum": s.minimum.to_value(),
        "maximum": s.maximum.to_value(),
        "unit": s.unit,
        "receivers": s.receivers,
        "valueDescriptions": value_descs_to_value(&s.value_descriptions),
    });
    match &s.presence {
        Presence::Always => o["presence"] = json!("always"),
        Presence::Multiplexed {
            multiplexor,
            values,
        } => {
            o["presence"] = json!("multiplexed");
            o["multiplexor"] = json!(multiplexor);
            o["multiplex_values"] = json!(values);
        }
    }
    o
}

fn message_to_value(m: &DbcMessage) -> Value {
    let mut o = json!({
        "id": m.id,
        "name": m.name,
        "dlc": m.dlc,
        "sender": m.sender,
        "senders": m.senders,
        "signals": m.signals.iter().map(signal_to_value).collect::<Vec<_>>(),
    });
    if m.extended {
        o["extended"] = json!(true);
    }
    o
}

fn comment_target_to_value(t: &CommentTarget) -> Value {
    match t {
        CommentTarget::Network => json!({ "kind": "network" }),
        CommentTarget::Node { node } => json!({ "kind": "node", "node": node }),
        CommentTarget::Message { id, extended } => {
            let mut o = json!({ "kind": "message", "id": id });
            if *extended {
                o["extended"] = json!(true);
            }
            o
        }
        CommentTarget::Signal {
            id,
            extended,
            signal,
        } => {
            let mut o = json!({ "kind": "signal", "id": id, "signal": signal });
            if *extended {
                o["extended"] = json!(true);
            }
            o
        }
        CommentTarget::EnvVar { env_var } => json!({ "kind": "envVar", "envVar": env_var }),
    }
}

fn comment_to_value(c: &Comment) -> Value {
    json!({ "target": comment_target_to_value(&c.target), "text": c.text })
}

fn env_var_to_value(e: &EnvironmentVar) -> Value {
    json!({
        "name": e.name,
        "varType": e.var_type,
        "initial": e.initial.to_value(),
        "minimum": e.minimum.to_value(),
        "maximum": e.maximum.to_value(),
    })
}

fn value_table_to_value(t: &ValueTable) -> Value {
    json!({ "name": t.name, "entries": value_descs_to_value(&t.entries) })
}

fn attr_type_to_value(t: &AttrType) -> Value {
    match t {
        AttrType::Int { min, max } => json!({ "kind": "int", "min": min, "max": max }),
        AttrType::Float { min, max } => {
            json!({ "kind": "float", "min": min.to_value(), "max": max.to_value() })
        }
        AttrType::String => json!({ "kind": "string" }),
        AttrType::Enum { values } => json!({ "kind": "enum", "values": values }),
        AttrType::Hex { min, max } => json!({ "kind": "hex", "min": min, "max": max }),
    }
}

fn attr_value_to_value(v: &AttrValue) -> Value {
    match v {
        AttrValue::Int(n) => json!({ "kind": "int", "value": n }),
        AttrValue::Float(r) => json!({ "kind": "float", "value": r.to_value() }),
        AttrValue::String(s) => json!({ "kind": "string", "value": s }),
        AttrValue::Enum(i) => json!({ "kind": "enum", "value": i }),
        AttrValue::Hex(n) => json!({ "kind": "hex", "value": n }),
    }
}

fn attr_scope_str(s: AttrScope) -> &'static str {
    match s {
        AttrScope::Network => "network",
        AttrScope::Node => "node",
        AttrScope::Message => "message",
        AttrScope::Signal => "signal",
        AttrScope::EnvVar => "envVar",
        AttrScope::NodeMsg => "nodeMsg",
        AttrScope::NodeSig => "nodeSig",
    }
}

fn attr_target_to_value(t: &AttrTarget) -> Value {
    match t {
        AttrTarget::Network => json!({ "kind": "network" }),
        AttrTarget::Node { node } => json!({ "kind": "node", "node": node }),
        AttrTarget::Message { id, extended } => {
            let mut o = json!({ "kind": "message", "id": id });
            if *extended {
                o["extended"] = json!(true);
            }
            o
        }
        AttrTarget::Signal {
            id,
            extended,
            signal,
        } => {
            let mut o = json!({ "kind": "signal", "id": id, "signal": signal });
            if *extended {
                o["extended"] = json!(true);
            }
            o
        }
        AttrTarget::EnvVar { env_var } => json!({ "kind": "envVar", "envVar": env_var }),
        AttrTarget::NodeMsg { node, id, extended } => {
            let mut o = json!({ "kind": "nodeMsg", "node": node, "id": id });
            if *extended {
                o["extended"] = json!(true);
            }
            o
        }
        AttrTarget::NodeSig {
            node,
            id,
            extended,
            signal,
        } => {
            let mut o = json!({ "kind": "nodeSig", "node": node, "id": id, "signal": signal });
            if *extended {
                o["extended"] = json!(true);
            }
            o
        }
    }
}

fn attribute_to_value(a: &Attribute) -> Value {
    match a {
        Attribute::Definition {
            name,
            scope,
            attr_type,
        } => json!({
            "kind": "definition",
            "name": name,
            "scope": attr_scope_str(*scope),
            "attrType": attr_type_to_value(attr_type),
        }),
        Attribute::Default { name, value } => json!({
            "kind": "default",
            "name": name,
            "value": attr_value_to_value(value),
        }),
        Attribute::Assignment {
            name,
            target,
            value,
        } => json!({
            "kind": "assignment",
            "name": name,
            "target": attr_target_to_value(target),
            "value": attr_value_to_value(value),
        }),
    }
}

impl Dbc {
    /// Serialize to the core's canonical DBC JSON (the inverse of
    /// [`Dbc::from_value`]) for the `parseDBC` / `validateDBC` / `formatDBCText`
    /// commands.
    pub(crate) fn to_value(&self) -> Value {
        json!({
            "version": self.version,
            "messages": self.messages.iter().map(message_to_value).collect::<Vec<_>>(),
            "nodes": self.nodes.iter().map(|n| json!({ "name": n.name })).collect::<Vec<_>>(),
            "valueTables": self.value_tables.iter().map(value_table_to_value).collect::<Vec<_>>(),
            "environmentVars":
                self.environment_vars.iter().map(env_var_to_value).collect::<Vec<_>>(),
            "signalGroups": self.signal_groups.iter()
                .map(|g| json!({ "name": g.name, "signals": g.signals }))
                .collect::<Vec<_>>(),
            "comments": self.comments.iter().map(comment_to_value).collect::<Vec<_>>(),
            "attributes": self.attributes.iter().map(attribute_to_value).collect::<Vec<_>>(),
            "unresolvedValueDescs": self.unresolved_value_descs,
        })
    }
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
mod tests {
    use super::{AttrTarget, AttrType, AttrValue, Attribute, Dbc, Presence};
    use crate::types::{CanId, Rational};
    use serde_json::{json, Value};

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

    /// `to_value` must be the exact inverse of `from_value` over the whole
    /// corpus — in-process, so it reaches branches the all-standard kitchen_sink
    /// `.so` round-trips can't: the `extended`-true serialize path (extended_can)
    /// and every attribute variant (attributes).
    #[test]
    fn serialize_round_trips_every_snapshot() {
        for (name, json) in SNAPSHOTS {
            let d = decode(json);
            let reparsed = Dbc::from_value(&d.to_value()).unwrap_or_else(|e| {
                panic!("serialize round-trip {name} failed to re-decode: {e:?}")
            });
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
        // `if *extended` branch in attr_target_to_value, which no snapshot hits).
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
    use super::{decode_env_var, decode_message, decode_presence, decode_signal};

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

    // signal startBit 0-511 / length 1-64
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
    fn signal_rejects_length_over_64() {
        let mut s = valid_signal();
        s["length"] = json!(65);
        assert!(decode_signal(&s).is_err());
    }

    #[test]
    fn signal_accepts_max_length() {
        let mut s = valid_signal();
        s["length"] = json!(64);
        assert!(decode_signal(&s).is_ok());
    }

    // multiplexed presence requires non-empty multiplexor + values
    #[test]
    fn presence_rejects_multiplexed_with_empty_values() {
        let sig =
            json!({ "presence": "multiplexed", "multiplexor": "Mode", "multiplex_values": [] });
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
}
