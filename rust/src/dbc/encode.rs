// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Serialization of the typed `Dbc` document to the core's canonical DBC JSON,
//! the inverse of the decoders in decode.rs.
//!
//! Each type writes through a crate-private `Serialize` impl on [`Wire`], an
//! object's keys in byte order, the order Go writes them in for the same
//! document. A rational is a bare number when its
//! denominator is 1 (see [`Wire`]'s impl for [`Rational`](crate::Rational)),
//! presence is flat, and every CAN identifier carries its `extended` flag,
//! true or false, as the kernel's formatter writes one. Nothing is decided
//! here: the kernel decides every number and every name when it reads the
//! document.

use serde::ser::{Serialize, Serializer};

use super::{
    AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder, Comment, CommentTarget, Dbc,
    DbcMessage, DbcSignal, EnvironmentVar, Node, Presence, RawValueDescription, SignalGroup,
    ValueDescription, ValueTable,
};
use crate::wire_json::{json_object, Number, Wire};

fn byte_order_str(b: ByteOrder) -> &'static str {
    match b {
        ByteOrder::LittleEndian => "little_endian",
        ByteOrder::BigEndian => "big_endian",
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

impl Serialize for Wire<'_, ValueDescription> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        json_object!(serializer, {
            "description" => &self.0.description,
            "value" => &Number(self.0.value),
        })
    }
}

impl Serialize for Wire<'_, DbcSignal> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let s = self.0;
        match &s.presence {
            Presence::Always => json_object!(serializer, {
                "byteOrder" => byte_order_str(s.byte_order),
                "factor" => &Wire(&s.factor),
                "length" => &Number::natural(s.length),
                "maximum" => &Wire(&s.maximum),
                "minimum" => &Wire(&s.minimum),
                "name" => &s.name,
                "offset" => &Wire(&s.offset),
                "presence" => "always",
                "receivers" => &s.receivers,
                "signed" => &s.signed,
                "startBit" => &Number::natural(s.start_bit),
                "unit" => &s.unit,
                "valueDescriptions" => &Wire(s.value_descriptions.as_slice()),
            }),
            Presence::Multiplexed {
                multiplexor,
                values,
            } => {
                let values: Vec<Number> = values.iter().map(|&v| Number::natural(v)).collect();
                json_object!(serializer, {
                    "byteOrder" => byte_order_str(s.byte_order),
                    "factor" => &Wire(&s.factor),
                    "length" => &Number::natural(s.length),
                    "maximum" => &Wire(&s.maximum),
                    "minimum" => &Wire(&s.minimum),
                    "multiplex_values" => &values,
                    "multiplexor" => multiplexor,
                    "name" => &s.name,
                    "offset" => &Wire(&s.offset),
                    "presence" => "multiplexed",
                    "receivers" => &s.receivers,
                    "signed" => &s.signed,
                    "startBit" => &Number::natural(s.start_bit),
                    "unit" => &s.unit,
                    "valueDescriptions" => &Wire(s.value_descriptions.as_slice()),
                })
            }
        }
    }
}

impl Serialize for Wire<'_, DbcMessage> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let m = self.0;
        json_object!(serializer, {
            "dlc" => &Number::natural(m.dlc),
            "extended" => &m.extended,
            "id" => &Number::natural(m.id),
            "name" => &m.name,
            "sender" => &m.sender,
            "senders" => &m.senders,
            "signals" => &Wire(m.signals.as_slice()),
        })
    }
}

impl Serialize for Wire<'_, CommentTarget> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            CommentTarget::Network => json_object!(serializer, { "kind" => "network" }),
            CommentTarget::Node { node } => json_object!(serializer, {
                "kind" => "node",
                "node" => node,
            }),
            CommentTarget::Message { id, extended } => json_object!(serializer, {
                "extended" => extended,
                "id" => &Number::natural(*id),
                "kind" => "message",
            }),
            CommentTarget::Signal {
                id,
                extended,
                signal,
            } => json_object!(serializer, {
                "extended" => extended,
                "id" => &Number::natural(*id),
                "kind" => "signal",
                "signal" => signal,
            }),
            CommentTarget::EnvVar { env_var } => json_object!(serializer, {
                "envVar" => env_var,
                "kind" => "envVar",
            }),
        }
    }
}

impl Serialize for Wire<'_, Comment> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        json_object!(serializer, {
            "target" => &Wire(&self.0.target),
            "text" => &self.0.text,
        })
    }
}

impl Serialize for Wire<'_, EnvironmentVar> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let e = self.0;
        json_object!(serializer, {
            "initial" => &Wire(&e.initial),
            "maximum" => &Wire(&e.maximum),
            "minimum" => &Wire(&e.minimum),
            "name" => &e.name,
            "varType" => &Number::signed(e.var_type),
        })
    }
}

impl Serialize for Wire<'_, ValueTable> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        json_object!(serializer, {
            "entries" => &Wire(self.0.entries.as_slice()),
            "name" => &self.0.name,
        })
    }
}

impl Serialize for Wire<'_, Node> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        json_object!(serializer, { "name" => &self.0.name })
    }
}

impl Serialize for Wire<'_, SignalGroup> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        json_object!(serializer, {
            "name" => &self.0.name,
            "signals" => &self.0.signals,
        })
    }
}

/// A value description the text parser could not attach to a signal: its
/// entries, its identifier pair and its signal name.
impl Serialize for Wire<'_, RawValueDescription> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let d = self.0;
        json_object!(serializer, {
            "entries" => &Wire(d.entries.as_slice()),
            "extended" => &d.id.is_extended(),
            "id" => &Number::natural(d.id.value()),
            "signalName" => &d.signal_name,
        })
    }
}

impl Serialize for Wire<'_, AttrType> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            AttrType::Int { min, max } => json_object!(serializer, {
                "kind" => "int",
                "max" => &Number::signed(*max),
                "min" => &Number::signed(*min),
            }),
            AttrType::Float { min, max } => json_object!(serializer, {
                "kind" => "float",
                "max" => &Wire(max),
                "min" => &Wire(min),
            }),
            AttrType::String => json_object!(serializer, { "kind" => "string" }),
            AttrType::Enum { values } => json_object!(serializer, {
                "kind" => "enum",
                "values" => values,
            }),
            AttrType::Hex { min, max } => json_object!(serializer, {
                "kind" => "hex",
                "max" => &Number::signed(*max),
                "min" => &Number::signed(*min),
            }),
        }
    }
}

impl Serialize for Wire<'_, AttrValue> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            AttrValue::Int(n) => json_object!(serializer, {
                "kind" => "int",
                "value" => &Number::signed(*n),
            }),
            AttrValue::Float(r) => json_object!(serializer, {
                "kind" => "float",
                "value" => &Wire(r),
            }),
            AttrValue::String(s) => json_object!(serializer, {
                "kind" => "string",
                "value" => s,
            }),
            AttrValue::Enum(i) => json_object!(serializer, {
                "kind" => "enum",
                "value" => &Number::signed(*i),
            }),
            AttrValue::Hex(n) => json_object!(serializer, {
                "kind" => "hex",
                "value" => &Number::signed(*n),
            }),
        }
    }
}

impl Serialize for Wire<'_, AttrTarget> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            AttrTarget::Network => json_object!(serializer, { "kind" => "network" }),
            AttrTarget::Node { node } => json_object!(serializer, {
                "kind" => "node",
                "node" => node,
            }),
            AttrTarget::Message { id, extended } => json_object!(serializer, {
                "extended" => extended,
                "id" => &Number::natural(*id),
                "kind" => "message",
            }),
            AttrTarget::Signal {
                id,
                extended,
                signal,
            } => json_object!(serializer, {
                "extended" => extended,
                "id" => &Number::natural(*id),
                "kind" => "signal",
                "signal" => signal,
            }),
            AttrTarget::EnvVar { env_var } => json_object!(serializer, {
                "envVar" => env_var,
                "kind" => "envVar",
            }),
            AttrTarget::NodeMsg { node, id, extended } => json_object!(serializer, {
                "extended" => extended,
                "id" => &Number::natural(*id),
                "kind" => "nodeMsg",
                "node" => node,
            }),
            AttrTarget::NodeSig {
                node,
                id,
                extended,
                signal,
            } => json_object!(serializer, {
                "extended" => extended,
                "id" => &Number::natural(*id),
                "kind" => "nodeSig",
                "node" => node,
                "signal" => signal,
            }),
        }
    }
}

impl Serialize for Wire<'_, Attribute> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            Attribute::Definition {
                name,
                scope,
                attr_type,
            } => json_object!(serializer, {
                "attrType" => &Wire(attr_type),
                "kind" => "definition",
                "name" => name,
                "scope" => attr_scope_str(*scope),
            }),
            Attribute::Default { name, value } => json_object!(serializer, {
                "kind" => "default",
                "name" => name,
                "value" => &Wire(value),
            }),
            Attribute::Assignment {
                name,
                target,
                value,
            } => json_object!(serializer, {
                "kind" => "assignment",
                "name" => name,
                "target" => &Wire(target),
                "value" => &Wire(value),
            }),
        }
    }
}

/// The document as the `dbc` field of a `parseDBC`, `validateDBC` or
/// `formatDBCText` command carries it.
impl Serialize for Wire<'_, Dbc> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let d = self.0;
        json_object!(serializer, {
            "attributes" => &Wire(d.attributes.as_slice()),
            "comments" => &Wire(d.comments.as_slice()),
            "environmentVars" => &Wire(d.environment_vars.as_slice()),
            "messages" => &Wire(d.messages.as_slice()),
            "nodes" => &Wire(d.nodes.as_slice()),
            "signalGroups" => &Wire(d.signal_groups.as_slice()),
            "unresolvedValueDescs" => &Wire(d.unresolved_value_descs.as_slice()),
            "valueTables" => &Wire(d.value_tables.as_slice()),
            "version" => &d.version,
        })
    }
}
