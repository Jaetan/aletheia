// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Decoding of the core's canonical DBC JSON into the typed `Dbc` document,
//! and of the `parseDBCText` and `formatDBC` responses that carry it.

use serde_json::Value;

use super::{
    extended_flag, AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder, Comment,
    CommentTarget, Dbc, DbcMessage, DbcSignal, EnvironmentVar, Node, ParsedDbc, Presence,
    SignalGroup, ValueDescription, ValueTable,
};
use crate::error::Error;
use crate::response::{parse_object, protocol, rational_from_value, str_field, u32_field};
use crate::types::{Dlc, Rational, MAX_EXTENDED_ID, MAX_STANDARD_ID};

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

pub(super) fn decode_presence(sig: &Value) -> Result<Presence, Error> {
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

pub(super) fn decode_signal(sig: &Value) -> Result<DbcSignal, Error> {
    let start_bit = u32_field(sig, "startBit")?;
    if start_bit > 511 {
        return Err(protocol(format!(
            "startBit {start_bit} out of range (0-511)"
        )));
    }
    let length = u32_field(sig, "length")?;
    if !(1..=512).contains(&length) {
        return Err(protocol(format!(
            "bit length {length} out of range (1-512)"
        )));
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

pub(super) fn decode_message(msg: &Value) -> Result<DbcMessage, Error> {
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

pub(super) fn decode_env_var(e: &Value) -> Result<EnvironmentVar, Error> {
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
pub(crate) fn decode_parsed_dbc(raw: &str) -> Result<ParsedDbc, Error> {
    let obj = parse_object(raw)?;
    let dbc = obj
        .get("dbc")
        .ok_or_else(|| protocol("parse response missing 'dbc'"))
        .and_then(Dbc::from_value)?;
    let warnings = arr(&obj, "warnings")
        .iter()
        .map(crate::response::decode_issue)
        .collect::<Result<Vec<_>, Error>>()?;
    Ok(ParsedDbc { dbc, warnings })
}

/// Decode a `formatDBC` response (`{"dbc": …}`) into the typed document.
pub(crate) fn decode_format_dbc(raw: &str) -> Result<Dbc, Error> {
    let obj = parse_object(raw)?;
    obj.get("dbc")
        .ok_or_else(|| protocol("formatDBC response missing 'dbc'"))
        .and_then(Dbc::from_value)
}
