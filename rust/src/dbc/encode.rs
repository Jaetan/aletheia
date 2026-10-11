// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Serialization of the typed `Dbc` document to the core's canonical DBC JSON.

use serde_json::{json, Value};

use super::{
    set_extended, AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder, Comment,
    CommentTarget, Dbc, DbcMessage, DbcSignal, EnvironmentVar, Presence, ValueDescription,
    ValueTable,
};

// ── Serialize (Dbc → canonical JSON, the inverse of the decoders in decode.rs)
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
    set_extended(&mut o, m.extended);
    o
}

fn comment_target_to_value(t: &CommentTarget) -> Value {
    match t {
        CommentTarget::Network => json!({ "kind": "network" }),
        CommentTarget::Node { node } => json!({ "kind": "node", "node": node }),
        CommentTarget::Message { id, extended } => {
            let mut o = json!({ "kind": "message", "id": id });
            set_extended(&mut o, *extended);
            o
        }
        CommentTarget::Signal {
            id,
            extended,
            signal,
        } => {
            let mut o = json!({ "kind": "signal", "id": id, "signal": signal });
            set_extended(&mut o, *extended);
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
            set_extended(&mut o, *extended);
            o
        }
        AttrTarget::Signal {
            id,
            extended,
            signal,
        } => {
            let mut o = json!({ "kind": "signal", "id": id, "signal": signal });
            set_extended(&mut o, *extended);
            o
        }
        AttrTarget::EnvVar { env_var } => json!({ "kind": "envVar", "envVar": env_var }),
        AttrTarget::NodeMsg { node, id, extended } => {
            let mut o = json!({ "kind": "nodeMsg", "node": node, "id": id });
            set_extended(&mut o, *extended);
            o
        }
        AttrTarget::NodeSig {
            node,
            id,
            extended,
            signal,
        } => {
            let mut o = json!({ "kind": "nodeSig", "node": node, "id": id, "signal": signal });
            set_extended(&mut o, *extended);
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
