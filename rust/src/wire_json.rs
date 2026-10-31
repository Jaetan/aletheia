// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The kernel's JSON a level at a time, every number exact to its 128 bits.
//!
//! A reply is walked as objects and arrays of [`RawValue`]: [`parse`] reads the
//! text as one value, [`parse_object`] as one object, [`kind`] names what a
//! place holds, and [`object`], [`array`](fn@array), [`string`], [`boolean`],
//! [`whole`], [`natural`] and [`rational`] read a place of their kind,
//! answering `None` for anything else so that the reader refuses it at its
//! place. A number is read from its own digits.
//!
//! A request is written by `Serialize` impls on [`Wire`], each writing an
//! object's keys in byte order, as every binding writes them, and each number
//! as its exact decimal digits ([`Number`]). Neither direction passes through
//! `serde_json::Value`, whose numbers stop at 64 bits.

use std::borrow::Cow;
use std::fmt;

use serde::de::{self, Deserialize, Deserializer, MapAccess, Visitor};
use serde::ser::{Error as _, Serialize, SerializeMap, Serializer};
use serde_json::value::RawValue;

use crate::error::Error;
use crate::types::{Rational, SignMagnitude};

// ── Reading ─────────────────────────────────────────────────────────────────

/// The whitespace JSON allows around a value.
const JSON_SPACE: [char; 4] = [' ', '\t', '\r', '\n'];

/// A JSON kind: what a reply refusal says a place expects and what came there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    Null,
    Boolean,
    Number,
    String,
    Array,
    Object,
}

impl Kind {
    /// The kind's name in a reply refusal.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Kind::Null => "null",
            Kind::Boolean => "boolean",
            Kind::Number => "number",
            Kind::String => "string",
            Kind::Array => "array",
            Kind::Object => "object",
        }
    }
}

/// The one JSON value `raw` holds, or serde_json's reason for text that is
/// not exactly one JSON value (nothing, a malformed value, or text after it).
pub(crate) fn parse(raw: &str) -> Result<&RawValue, serde_json::Error> {
    serde_json::from_str(raw)
}

/// The kind of `value`, read from its first byte: a value serde_json has
/// already checked is told by it alone.
pub(crate) fn kind(value: &RawValue) -> Kind {
    match value
        .get()
        .trim_start_matches(JSON_SPACE)
        .as_bytes()
        .first()
    {
        Some(b'{') => Kind::Object,
        Some(b'[') => Kind::Array,
        Some(b'"') => Kind::String,
        Some(b't' | b'f') => Kind::Boolean,
        Some(b'n') => Kind::Null,
        _ => Kind::Number,
    }
}

/// One object of a reply: its members in the order the text holds them, each
/// key unescaped and each value its raw text. A key holding no escape borrows
/// the reply's text, so an object costs one allocation, its list of members,
/// unless a key is escaped.
pub(crate) struct Object<'a> {
    members: Vec<(Cow<'a, str>, &'a RawValue)>,
}

impl<'a> Object<'a> {
    /// The value at `key`, the last one when the text repeats the key, as
    /// serde_json's own map keeps it.
    pub(crate) fn get(&self, key: &str) -> Option<&'a RawValue> {
        self.members
            .iter()
            .rev()
            .find(|(k, _)| k.as_ref() == key)
            .map(|&(_, value)| value)
    }
}

impl<'de> Deserialize<'de> for Object<'de> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct ObjectVisitor;

        impl<'de> Visitor<'de> for ObjectVisitor {
            type Value = Object<'de>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("an object")
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Object<'de>, M::Error> {
                let mut members = Vec::with_capacity(map.size_hint().unwrap_or(0));
                while let Some((Text(key), value)) = map.next_entry::<Text<'de>, &'de RawValue>()? {
                    members.push((key, value));
                }
                Ok(Object { members })
            }
        }

        deserializer.deserialize_map(ObjectVisitor)
    }
}

/// A string of a reply, borrowed from the text when it holds no escape and
/// unescaped into a buffer of its own when it does.
struct Text<'a>(Cow<'a, str>);

impl<'de> Deserialize<'de> for Text<'de> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct TextVisitor;

        impl<'de> Visitor<'de> for TextVisitor {
            type Value = Text<'de>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a string")
            }

            fn visit_borrowed_str<E: de::Error>(self, v: &'de str) -> Result<Text<'de>, E> {
                Ok(Text(Cow::Borrowed(v)))
            }

            fn visit_str<E: de::Error>(self, v: &str) -> Result<Text<'de>, E> {
                Ok(Text(Cow::Owned(v.to_owned())))
            }

            fn visit_string<E: de::Error>(self, v: String) -> Result<Text<'de>, E> {
                Ok(Text(Cow::Owned(v)))
            }
        }

        deserializer.deserialize_str(TextVisitor)
    }
}

/// The object `raw` holds when it is exactly one JSON object, whitespace around
/// it aside, read in one pass; `None` for any other text. serde_json refuses
/// text after the object and checks each member's value as it reads it into a
/// [`RawValue`], so this pass takes the texts [`parse`] then [`object`] take,
/// to the same members.
pub(crate) fn parse_object(raw: &str) -> Option<Object<'_>> {
    serde_json::from_str(raw).ok()
}

/// The object `value` holds, or `None` for a value of another kind.
pub(crate) fn object(value: &RawValue) -> Option<Object<'_>> {
    if kind(value) != Kind::Object {
        return None;
    }
    parse_object(value.get())
}

/// The elements of the array `value` holds, or `None` for a value of another
/// kind.
pub(crate) fn array(value: &RawValue) -> Option<Vec<&RawValue>> {
    if kind(value) != Kind::Array {
        return None;
    }
    serde_json::from_str(value.get()).ok()
}

/// The string `value` holds, unescaped, or `None` for a value of another kind.
pub(crate) fn string(value: &RawValue) -> Option<Cow<'_, str>> {
    if kind(value) != Kind::String {
        return None;
    }
    // serde_json checked the token as JSON when it read the level holding it,
    // so a token with no backslash holds no escape and no control character:
    // the text between its quotes is its content, borrowed as it stands.
    let token = value.get().trim_matches(JSON_SPACE);
    match token.strip_prefix('"').and_then(|t| t.strip_suffix('"')) {
        Some(content) if !content.contains('\\') => Some(Cow::Borrowed(content)),
        _ => serde_json::from_str::<Text<'_>>(token)
            .ok()
            .map(|text| text.0),
    }
}

/// The boolean `value` holds, or `None` for a value of another kind.
pub(crate) fn boolean(value: &RawValue) -> Option<bool> {
    match value.get().trim_matches(JSON_SPACE) {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// The whole number `value` writes as an optional minus sign then decimal
/// digits, read from that text as a sign and a magnitude, a zero unsigned.
/// `None` for a value of another kind, for a number written otherwise (with a
/// fraction or an exponent, `1.0` or `1e3`) and for a magnitude past
/// 2^128-1: a whole-number place refuses each as the number it does not hold,
/// expecting `number` where `number` came, as Go's reply readers do.
pub(crate) fn whole(value: &RawValue) -> Option<SignMagnitude> {
    let text = value.get().trim_matches(JSON_SPACE);
    let (negative, digits) = match text.strip_prefix('-') {
        Some(digits) => (true, digits),
        None => (false, text),
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let magnitude: u128 = digits.parse().ok()?;
    Some(SignMagnitude {
        negative: negative && magnitude != 0,
        magnitude,
    })
}

/// The whole number at a place the kernel proves natural, or `None` where
/// [`whole`] answers `None` and for a negative number.
pub(crate) fn natural(value: &RawValue) -> Option<u128> {
    whole(value).filter(|n| !n.negative).map(|n| n.magnitude)
}

/// The rational `value` writes: a whole number, or the `{numerator,
/// denominator}` object the kernel writes a fraction as, stored as the kernel
/// wrote it ([`Rational::from_kernel`]). The object's sign is the quotient's,
/// so a negative denominator, which the kernel never writes, flips it as the
/// other bindings' readers do, and a zero denominator, which it never writes
/// either, is read as written. `None` for anything else, which a rational
/// place refuses as `a rational` expected.
pub(crate) fn rational(value: &RawValue) -> Option<Rational> {
    if let Some(n) = whole(value) {
        return Some(Rational::from_kernel(n.negative, n.magnitude, 1));
    }
    let fraction = object(value)?;
    let numerator = whole(fraction.get("numerator")?)?;
    let denominator = whole(fraction.get("denominator")?)?;
    Some(Rational::from_kernel(
        numerator.negative != denominator.negative,
        numerator.magnitude,
        denominator.magnitude,
    ))
}

// ── Writing ─────────────────────────────────────────────────────────────────

/// Write an object through `$serializer` holding each `$key => $value` entry
/// in the order given, which every caller gives in byte order: the order Go's
/// encoder writes a map's keys in. Each `$value` is a reference to a
/// `Serialize` value.
macro_rules! json_object {
    ($serializer:expr, { $($key:literal => $value:expr),+ $(,)? }) => {{
        let mut map = ::serde::Serializer::serialize_map($serializer, Some([$($key),+].len()))?;
        $(::serde::ser::SerializeMap::serialize_entry(&mut map, $key, $value)?;)+
        ::serde::ser::SerializeMap::end(map)
    }};
}
pub(crate) use json_object;

/// A value as the kernel's JSON writes it. Each type a request carries has its
/// `Serialize` impl on this crate-private view, so the public types carry no
/// serde impl of their own.
pub(crate) struct Wire<'a, T: ?Sized>(pub(crate) &'a T);

/// Every element of a slice as the kernel's JSON writes it, in order.
impl<T> Serialize for Wire<'_, [T]>
where
    for<'b> Wire<'b, T>: Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.0.iter().map(Wire))
    }
}

/// A rational as every binding writes one: its signed numerator's digits when
/// the denominator is 1, else `{"denominator": d, "numerator": n}`.
impl Serialize for Wire<'_, Rational> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let numerator = Number(SignMagnitude {
            negative: self.0.is_negative(),
            magnitude: self.0.numerator(),
        });
        if self.0.denominator() == 1 {
            return numerator.serialize(serializer);
        }
        json_object!(serializer, {
            "denominator" => &Number::natural(self.0.denominator()),
            "numerator" => &numerator,
        })
    }
}

/// A whole number written as its decimal digits, after a `-` when it is
/// negative and not zero: the one way every number the writer builds reaches
/// the kernel's JSON, exact to its 128 bits.
#[derive(Clone, Copy)]
pub(crate) struct Number(pub(crate) SignMagnitude);

impl Number {
    /// The number `magnitude`, written unsigned.
    pub(crate) fn natural(magnitude: impl Into<u128>) -> Self {
        Number(SignMagnitude {
            negative: false,
            magnitude: magnitude.into(),
        })
    }

    /// The signed number `n`.
    pub(crate) fn signed(n: i64) -> Self {
        Number(SignMagnitude {
            negative: n < 0,
            magnitude: u128::from(n.unsigned_abs()),
        })
    }
}

impl Serialize for Number {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // serde_json writes a u128 and an i128 as their exact decimal digits,
        // so every number from -2^127 to 2^128-1 is written natively, a zero
        // unsigned whatever its sign. A negative past -2^127, which no i128
        // holds, is written as a RawValue of its digits.
        let SignMagnitude {
            negative,
            magnitude,
        } = self.0;
        if !negative {
            return serializer.serialize_u128(magnitude);
        }
        match 0_i128.checked_sub_unsigned(magnitude) {
            Some(n) => serializer.serialize_i128(n),
            None => RawValue::from_string(self.0.to_string())
                .map_err(S::Error::custom)?
                .serialize(serializer),
        }
    }
}

/// The JSON text of `value`.
pub(crate) fn to_text<T: Serialize + ?Sized>(value: &T) -> Result<String, Error> {
    serde_json::to_string(value)
        .map_err(|e| Error::Protocol(format!("a request could not be written: {e}")))
}

/// The text of the command `command` carrying `value` under `key`:
/// `{"command": command, key: value, "type": "command"}`, its keys in byte
/// order for each key a command carries (`dbc`, `properties`, `text`).
pub(crate) fn command<T: Serialize + ?Sized>(
    command: &str,
    key: &'static str,
    value: &T,
) -> Result<String, Error> {
    /// The command's object, `key` between `command` and `type` in byte order.
    struct Command<'a, T: ?Sized> {
        command: &'a str,
        key: &'static str,
        value: &'a T,
    }

    impl<T: Serialize + ?Sized> Serialize for Command<'_, T> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            let mut map = serializer.serialize_map(Some(3))?;
            map.serialize_entry("command", self.command)?;
            map.serialize_entry(self.key, self.value)?;
            map.serialize_entry("type", "command")?;
            map.end()
        }
    }

    to_text(&Command {
        command,
        key,
        value,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 2^128-1, the largest magnitude a reply's number carries.
    const MAX: &str = "340282366920938463463374607431768211455";

    /// The one value `text` holds.
    fn value(text: &str) -> &RawValue {
        parse(text).expect("one JSON value")
    }

    #[test]
    fn a_whole_number_is_read_exactly_to_its_128_bits_in_either_sign() {
        let read = |text: &str| whole(value(text)).map(|n| (n.negative, n.magnitude));
        assert_eq!(read(MAX), Some((false, u128::MAX)));
        assert_eq!(read(&format!("-{MAX}")), Some((true, u128::MAX)));
        // 2^64 + 1, which neither a u64 nor an f64 holds exactly.
        assert_eq!(read("18446744073709551617"), Some((false, (1 << 64) + 1)));
        // A zero is unsigned whatever its sign.
        assert_eq!(read("-0"), Some((false, 0)));
        // A natural place takes the magnitude and refuses a negative.
        assert_eq!(natural(value(MAX)), Some(u128::MAX));
        assert_eq!(natural(value("-1")), None);
    }

    #[test]
    fn a_fraction_an_exponent_or_a_number_past_2_128_minus_1_is_no_whole_number() {
        for text in [
            "1.0",
            "-2.5",
            "1e3",
            "1E3",
            "-1e-3",
            "340282366920938463463374607431768211456",
            "-340282366920938463463374607431768211456",
            r#""7""#,
            "true",
            "null",
            "[1]",
            "{}",
        ] {
            assert_eq!(whole(value(text)), None, "{text}");
        }
    }

    #[test]
    fn a_rational_is_a_whole_number_or_its_fraction_object_stored_as_written() {
        let read = |text: &str| {
            rational(value(text)).map(|r| (r.is_negative(), r.numerator(), r.denominator()))
        };
        assert_eq!(read(&format!("-{MAX}")), Some((true, u128::MAX, 1)));
        assert_eq!(
            read(&format!(r#"{{"numerator":-{MAX},"denominator":{MAX}}}"#)),
            Some((true, u128::MAX, u128::MAX))
        );
        // The kernel writes neither: a negative denominator flips the sign as
        // the other bindings' readers flip it, and a zero one is read as
        // written.
        assert_eq!(
            read(r#"{"numerator":-4,"denominator":-2}"#),
            Some((false, 4, 2))
        );
        assert_eq!(
            read(r#"{"numerator":4,"denominator":-2}"#),
            Some((true, 4, 2))
        );
        assert_eq!(
            read(r#"{"numerator":1,"denominator":0}"#),
            Some((false, 1, 0))
        );
        for text in [
            "1.5",
            r#"{"numerator":1}"#,
            r#"{"denominator":2}"#,
            r#"{"numerator":1.5,"denominator":2}"#,
            r#"{"numerator":1,"denominator":"2"}"#,
            r#""1""#,
        ] {
            assert_eq!(read(text), None, "{text}");
        }
    }

    #[test]
    fn an_escaped_key_is_read_unescaped() {
        let obj = object(value(r#"{"a\u0062":1,"q\"\\":2,"plain":3}"#)).expect("an object");
        assert_eq!(obj.get("ab").map(RawValue::get), Some("1"));
        assert_eq!(obj.get("q\"\\").map(RawValue::get), Some("2"));
        assert_eq!(obj.get("plain").map(RawValue::get), Some("3"));
        assert!(obj.get(r"a\u0062").is_none());
        // A repeated key reads as its last value, as serde_json's map keeps it.
        let obj = object(value(r#"{"k":1,"k":2}"#)).expect("an object");
        assert_eq!(obj.get("k").map(RawValue::get), Some("2"));
        // A string value's escapes are read the same way.
        assert_eq!(string(value(r#""a\u0062\n""#)).as_deref(), Some("ab\n"));
    }

    #[test]
    fn a_number_is_written_exactly_to_its_128_bits() {
        let number = |negative: bool, magnitude: u128| {
            to_text(&Number(SignMagnitude {
                negative,
                magnitude,
            }))
            .expect("a number is written")
        };
        assert_eq!(number(false, u128::MAX), MAX);
        assert_eq!(number(true, u128::MAX), format!("-{MAX}"));
        assert_eq!(number(true, 0), "0");
        // -2^127, the least number an i128 holds, and the one past it.
        let two_to_127 = 1_u128 << 127;
        assert_eq!(
            number(true, two_to_127),
            "-170141183460469231731687303715884105728"
        );
        assert_eq!(
            number(true, two_to_127 + 1),
            "-170141183460469231731687303715884105729"
        );
        assert_eq!(
            number(false, two_to_127),
            "170141183460469231731687303715884105728"
        );
        // A rational is its numerator's digits over 1, and the object of its
        // two parts otherwise, the keys in byte order.
        let r = Rational::from_parts(true, u128::MAX, 2).expect("a fraction");
        assert_eq!(
            to_text(&Wire(&r)).expect("a rational is written"),
            format!(r#"{{"denominator":2,"numerator":-{MAX}}}"#)
        );
        assert_eq!(
            to_text(&Wire(&Rational::from(u128::MAX))).expect("a rational is written"),
            MAX
        );
    }
}
