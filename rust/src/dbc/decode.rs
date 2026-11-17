// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Decoding of the core's canonical DBC JSON into the typed `Dbc` document,
//! and of the `parseDBCText` and `formatDBC` responses that carry it.
//!
//! The DBC a reply carries sits at `dbc`, and every refusal names its place
//! from there: a signal's field is at `dbc/messages/signals/<key>`. Every key
//! the kernel writes is required, and each number or string is read by kind
//! only, its range the kernel's, decided when it read the DBC and proven of
//! every reply. A signal's byte order and presence, a comment target's kind,
//! an attribute's kind, a definition's scope and type kind and an attribute's
//! value kind and target kind are read by `field_word`, which refuses a word
//! outside the place's words, every other tag as a string; one function
//! dispatches each tag, its match naming every word the kernel writes at the
//! place but the last, which the final arm reads.

use super::{
    AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder, Comment, CommentTarget, Dbc,
    DbcMessage, DbcSignal, EnvironmentVar, Node, ParsedDbc, Presence, RawValueDescription,
    SignalGroup, ValueDescription, ValueTable,
};
use crate::error::Error;
use crate::reply_shape::{
    came, field_array, field_bool, field_i64, field_natural, field_naturals, field_object,
    field_object_of, field_objects, field_rational, field_sign_magnitude, field_string,
    field_strings, field_word, refusal, ReplyPath, ReplyStatus, NUMBER, ROOT,
};
use crate::response::{decode_reply, read_issues};
use crate::types::{CanId, Dlc};
use crate::wire_json::Object;

/// Decode a `parseDBCText` / `parseDBC` response into the typed document plus
/// the warnings the core reported.
pub(crate) fn decode_parsed_dbc(raw: &str) -> Result<ParsedDbc, Error> {
    let reply = decode_reply(raw, ReplyStatus::Success)?;
    let dbc = field_object(&reply, ROOT, "dbc")?;
    field_array(&reply, ROOT, "warnings")?;
    let dbc = read_dbc(&dbc)?;
    let warnings = read_issues(&reply, "warnings")?;
    Ok(ParsedDbc { dbc, warnings })
}

/// Decode a `formatDBC` response (`{"dbc": …}`) into the typed document.
pub(crate) fn decode_format_dbc(raw: &str) -> Result<Dbc, Error> {
    let reply = decode_reply(raw, ReplyStatus::Success)?;
    read_dbc(&field_object(&reply, ROOT, "dbc")?)
}

/// The DBC object of a reply, at `dbc`.
fn read_dbc(dbc: &Object<'_>) -> Result<Dbc, Error> {
    let path = ROOT.at("dbc");
    let version = field_string(dbc, path, "version")?.into_owned();
    let messages = field_objects(dbc, path, "messages", read_message)?;
    let signal_groups = field_objects(dbc, path, "signalGroups", read_signal_group)?;
    let environment_vars = field_objects(dbc, path, "environmentVars", read_environment_var)?;
    let value_tables = field_objects(dbc, path, "valueTables", read_value_table)?;
    let nodes = field_objects(dbc, path, "nodes", read_node)?;
    let comments = field_objects(dbc, path, "comments", read_comment)?;
    let attributes = field_objects(dbc, path, "attributes", read_attribute)?;
    let unresolved_value_descs = field_objects(
        dbc,
        path,
        "unresolvedValueDescs",
        read_raw_value_description,
    )?;
    Ok(Dbc {
        version,
        messages,
        nodes,
        value_tables,
        environment_vars,
        signal_groups,
        comments,
        attributes,
        unresolved_value_descs,
    })
}

/// The identifier of the object at `path`: its `extended` flag, then `id` at
/// the width the flag names, whose range the kernel proves. A number past the
/// width's integer type, which the kernel never writes, is refused as the
/// number the place does not hold.
fn read_can_id(obj: &Object<'_>, path: ReplyPath<'_>) -> Result<CanId, Error> {
    if field_bool(obj, path, "extended")? {
        field_natural(obj, path, "id").map(CanId::Extended)
    } else {
        field_natural(obj, path, "id").map(CanId::Standard)
    }
}

/// A message's byte count, one a length code stands for; a count no code
/// stands for, which the kernel never writes, is refused as the number the
/// place does not hold.
fn read_dlc(message: &Object<'_>, path: ReplyPath<'_>) -> Result<u32, Error> {
    let count: u32 = field_natural(message, path, "dlc")?;
    if Dlc::from_bytes(count as usize).is_err() {
        return Err(refusal(path.at("dlc"), NUMBER, came(message, "dlc")));
    }
    Ok(count)
}

/// One message at `path`, its signals included.
fn read_message(message: &Object<'_>, path: ReplyPath<'_>) -> Result<DbcMessage, Error> {
    let signals = field_objects(message, path, "signals", read_signal)?;
    let name = field_string(message, path, "name")?.into_owned();
    let id = read_can_id(message, path)?;
    let dlc = read_dlc(message, path)?;
    let sender = field_string(message, path, "sender")?.into_owned();
    let senders = field_strings(message, path, "senders")?;
    Ok(DbcMessage {
        id: id.value(),
        extended: id.is_extended(),
        name,
        dlc,
        sender,
        senders,
        signals,
    })
}

/// A signal's byte order, `big_endian` its last arm.
fn byte_order(word: &str) -> ByteOrder {
    match word {
        "little_endian" => ByteOrder::LittleEndian,
        _ => ByteOrder::BigEndian,
    }
}

/// One signal at `path`.
fn read_signal(signal: &Object<'_>, path: ReplyPath<'_>) -> Result<DbcSignal, Error> {
    Ok(DbcSignal {
        name: field_string(signal, path, "name")?.into_owned(),
        start_bit: field_natural(signal, path, "startBit")?,
        length: field_natural(signal, path, "length")?,
        byte_order: byte_order(field_word(
            signal,
            path,
            "byteOrder",
            &["little_endian", "big_endian"],
        )?),
        signed: field_bool(signal, path, "signed")?,
        factor: field_rational(signal, path, "factor")?,
        offset: field_rational(signal, path, "offset")?,
        minimum: field_rational(signal, path, "minimum")?,
        maximum: field_rational(signal, path, "maximum")?,
        unit: field_string(signal, path, "unit")?.into_owned(),
        receivers: field_strings(signal, path, "receivers")?,
        value_descriptions: field_objects(
            signal,
            path,
            "valueDescriptions",
            read_value_description,
        )?,
        presence: presence(
            field_word(signal, path, "presence", &["always", "multiplexed"])?,
            signal,
            path,
        )?,
    })
}

/// The presence the kernel states for every signal, `multiplexed` its last
/// arm, whose multiplexor is a string and whose selector values are whole
/// numbers.
fn presence(word: &str, signal: &Object<'_>, path: ReplyPath<'_>) -> Result<Presence, Error> {
    match word {
        "always" => Ok(Presence::Always),
        _ => Ok(Presence::Multiplexed {
            multiplexor: field_string(signal, path, "multiplexor")?.into_owned(),
            values: field_naturals(signal, path, "multiplex_values")?,
        }),
    }
}

/// One signal group: its name and its members' names.
fn read_signal_group(group: &Object<'_>, path: ReplyPath<'_>) -> Result<SignalGroup, Error> {
    Ok(SignalGroup {
        name: field_string(group, path, "name")?.into_owned(),
        signals: field_strings(group, path, "signals")?,
    })
}

/// One environment variable, its `varType` the tag the kernel proves it to
/// be.
fn read_environment_var(var: &Object<'_>, path: ReplyPath<'_>) -> Result<EnvironmentVar, Error> {
    Ok(EnvironmentVar {
        name: field_string(var, path, "name")?.into_owned(),
        var_type: field_natural(var, path, "varType")?,
        initial: field_rational(var, path, "initial")?,
        minimum: field_rational(var, path, "minimum")?,
        maximum: field_rational(var, path, "maximum")?,
    })
}

/// One value description: a signed key and its text.
fn read_value_description(
    entry: &Object<'_>,
    path: ReplyPath<'_>,
) -> Result<ValueDescription, Error> {
    Ok(ValueDescription {
        value: field_sign_magnitude(entry, path, "value")?,
        description: field_string(entry, path, "description")?.into_owned(),
    })
}

/// One value table: its name and its entries.
fn read_value_table(table: &Object<'_>, path: ReplyPath<'_>) -> Result<ValueTable, Error> {
    Ok(ValueTable {
        name: field_string(table, path, "name")?.into_owned(),
        entries: field_objects(table, path, "entries", read_value_description)?,
    })
}

/// One value description the text parser could not attach to a signal, at
/// `path`: its CAN id read as a message's, its signal name and its entries.
fn read_raw_value_description(
    desc: &Object<'_>,
    path: ReplyPath<'_>,
) -> Result<RawValueDescription, Error> {
    Ok(RawValueDescription {
        id: read_can_id(desc, path)?,
        signal_name: field_string(desc, path, "signalName")?.into_owned(),
        entries: field_objects(desc, path, "entries", read_value_description)?,
    })
}

/// One node.
fn read_node(node: &Object<'_>, path: ReplyPath<'_>) -> Result<Node, Error> {
    Ok(Node {
        name: field_string(node, path, "name")?.into_owned(),
    })
}

/// What a comment is attached to, `envVar` its last arm.
fn comment_target(
    word: &str,
    target: &Object<'_>,
    path: ReplyPath<'_>,
) -> Result<CommentTarget, Error> {
    match word {
        "network" => Ok(CommentTarget::Network),
        "node" => Ok(CommentTarget::Node {
            node: field_string(target, path, "node")?.into_owned(),
        }),
        "message" => {
            let id = read_can_id(target, path)?;
            Ok(CommentTarget::Message {
                id: id.value(),
                extended: id.is_extended(),
            })
        }
        "signal" => {
            let id = read_can_id(target, path)?;
            Ok(CommentTarget::Signal {
                id: id.value(),
                extended: id.is_extended(),
                signal: field_string(target, path, "signal")?.into_owned(),
            })
        }
        _ => Ok(CommentTarget::EnvVar {
            env_var: field_string(target, path, "envVar")?.into_owned(),
        }),
    }
}

/// One comment: its target and its text.
fn read_comment(comment: &Object<'_>, path: ReplyPath<'_>) -> Result<Comment, Error> {
    let target = field_object_of(comment, path, "target", |target, place| {
        let kind = field_word(
            target,
            place,
            "kind",
            &["network", "node", "message", "signal", "envVar"],
        )?;
        comment_target(kind, target, place)
    })?;
    let text = field_string(comment, path, "text")?.into_owned();
    Ok(Comment { target, text })
}

/// An attribute definition's scope, `nodeSig` its last arm.
fn attr_scope(word: &str) -> AttrScope {
    match word {
        "network" => AttrScope::Network,
        "node" => AttrScope::Node,
        "message" => AttrScope::Message,
        "signal" => AttrScope::Signal,
        "envVar" => AttrScope::EnvVar,
        "nodeMsg" => AttrScope::NodeMsg,
        _ => AttrScope::NodeSig,
    }
}

/// An attribute definition's type, `hex` its last arm; an INT or HEX type is
/// bounded by its integer `min` and `max`, a FLOAT type by its rational ones.
fn attr_type(word: &str, attr_type: &Object<'_>, path: ReplyPath<'_>) -> Result<AttrType, Error> {
    match word {
        "int" => Ok(AttrType::Int {
            min: field_i64(attr_type, path, "min")?,
            max: field_i64(attr_type, path, "max")?,
        }),
        "float" => Ok(AttrType::Float {
            min: field_rational(attr_type, path, "min")?,
            max: field_rational(attr_type, path, "max")?,
        }),
        "string" => Ok(AttrType::String),
        "enum" => Ok(AttrType::Enum {
            values: field_strings(attr_type, path, "values")?,
        }),
        _ => Ok(AttrType::Hex {
            min: field_i64(attr_type, path, "min")?,
            max: field_i64(attr_type, path, "max")?,
        }),
    }
}

/// An attribute's value, `hex` its last arm.
fn attr_value(word: &str, value: &Object<'_>, path: ReplyPath<'_>) -> Result<AttrValue, Error> {
    match word {
        "int" => Ok(AttrValue::Int(field_i64(value, path, "value")?)),
        "float" => Ok(AttrValue::Float(field_rational(value, path, "value")?)),
        "string" => Ok(AttrValue::String(
            field_string(value, path, "value")?.into_owned(),
        )),
        "enum" => Ok(AttrValue::Enum(field_i64(value, path, "value")?)),
        _ => Ok(AttrValue::Hex(field_i64(value, path, "value")?)),
    }
}

/// What an attribute is assigned to, `nodeSig` its last arm; a target other
/// than the network, a node or an environment variable carries a CAN id, read
/// before the names beside it.
fn attr_target(word: &str, target: &Object<'_>, path: ReplyPath<'_>) -> Result<AttrTarget, Error> {
    match word {
        "network" => Ok(AttrTarget::Network),
        "node" => Ok(AttrTarget::Node {
            node: field_string(target, path, "node")?.into_owned(),
        }),
        "envVar" => Ok(AttrTarget::EnvVar {
            env_var: field_string(target, path, "envVar")?.into_owned(),
        }),
        "message" => {
            let id = read_can_id(target, path)?;
            Ok(AttrTarget::Message {
                id: id.value(),
                extended: id.is_extended(),
            })
        }
        "signal" => {
            let id = read_can_id(target, path)?;
            Ok(AttrTarget::Signal {
                id: id.value(),
                extended: id.is_extended(),
                signal: field_string(target, path, "signal")?.into_owned(),
            })
        }
        "nodeMsg" => {
            let id = read_can_id(target, path)?;
            Ok(AttrTarget::NodeMsg {
                node: field_string(target, path, "node")?.into_owned(),
                id: id.value(),
                extended: id.is_extended(),
            })
        }
        _ => {
            let id = read_can_id(target, path)?;
            Ok(AttrTarget::NodeSig {
                node: field_string(target, path, "node")?.into_owned(),
                id: id.value(),
                extended: id.is_extended(),
                signal: field_string(target, path, "signal")?.into_owned(),
            })
        }
    }
}

/// One attribute entry at `path`: its kind and its name, then what the kind
/// carries.
fn read_attribute(attribute_entry: &Object<'_>, path: ReplyPath<'_>) -> Result<Attribute, Error> {
    let kind = field_word(
        attribute_entry,
        path,
        "kind",
        &["definition", "default", "assignment"],
    )?;
    let name = field_string(attribute_entry, path, "name")?.into_owned();
    attribute(kind, name, attribute_entry, path)
}

/// An attribute entry by its kind, `assignment` its last arm: a definition's
/// scope and type, a default's value, an assignment's target and value.
fn attribute(
    word: &str,
    name: String,
    entry: &Object<'_>,
    path: ReplyPath<'_>,
) -> Result<Attribute, Error> {
    match word {
        "definition" => Ok(Attribute::Definition {
            name,
            scope: attr_scope(field_word(
                entry,
                path,
                "scope",
                &[
                    "network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig",
                ],
            )?),
            attr_type: field_object_of(entry, path, "attrType", read_attr_type)?,
        }),
        "default" => Ok(Attribute::Default {
            name,
            value: field_object_of(entry, path, "value", read_attr_value)?,
        }),
        _ => Ok(Attribute::Assignment {
            name,
            target: field_object_of(entry, path, "target", read_attr_target)?,
            value: field_object_of(entry, path, "value", read_attr_value)?,
        }),
    }
}

/// An attribute definition's type object at `path`, read by its kind.
fn read_attr_type(type_entry: &Object<'_>, path: ReplyPath<'_>) -> Result<AttrType, Error> {
    let kind = field_word(
        type_entry,
        path,
        "kind",
        &["int", "float", "string", "enum", "hex"],
    )?;
    attr_type(kind, type_entry, path)
}

/// An attribute's value object at `path`, read by its kind.
fn read_attr_value(value: &Object<'_>, path: ReplyPath<'_>) -> Result<AttrValue, Error> {
    let kind = field_word(
        value,
        path,
        "kind",
        &["int", "float", "string", "enum", "hex"],
    )?;
    attr_value(kind, value, path)
}

/// An attribute assignment's target object at `path`, read by its kind.
fn read_attr_target(target: &Object<'_>, path: ReplyPath<'_>) -> Result<AttrTarget, Error> {
    let kind = field_word(
        target,
        path,
        "kind",
        &[
            "network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig",
        ],
    )?;
    attr_target(kind, target, path)
}
