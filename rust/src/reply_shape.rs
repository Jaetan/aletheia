// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The refusal every reply reader returns for a place holding what the kernel
//! never writes there, and the readers of each kind that build it.
//!
//! A refusal reads `reply <path>: expected <what>, got <what came>`, the same
//! text in the four bindings. The path is the reply proof's: the keys from the
//! reply's root joined by `/`, an array's entries keeping the array's path, the
//! whole reply's path empty (`reply: expected object, got array`). What is
//! expected and what came are JSON kinds, `string`, `boolean`, `number`,
//! `array`, `object` or `null`, and a key the reply lacks came as `nothing`. A
//! rational place expects `a rational`: a number, or the `{numerator,
//! denominator}` object the kernel writes a fraction as. A place holding one of
//! a set of words expects them quoted, and a string outside them came quoted;
//! an issue's code expects `an issue code` and an error reply's `an error
//! code`, a string outside the table came quoted.
//! A whole-number place expects a `number` written as digits, all the kernel
//! writes there; a number the place's Rust type cannot hold, which the kernel
//! never writes there either, is refused as the number the place does not
//! hold, `expected number, got number`.
//!
//! A reader narrows each place itself and builds its refusal here: [`came`]
//! names what a key held, [`came_as`] what a value is, [`came_word`] what a
//! word place held.

use std::borrow::Cow;
use std::fmt::{self, Write as _};

use serde_json::value::RawValue;

use crate::error::Error;
use crate::types::{Rational, SignMagnitude};
use crate::wire_json::{self, Object};

/// A place in a reply: its keys from the root, each borrowed from the reader
/// naming it, so a place costs nothing until a refusal prints it.
#[derive(Clone, Copy)]
pub(crate) struct ReplyPath<'a> {
    parent: Option<&'a ReplyPath<'a>>,
    key: &'a str,
}

/// The whole reply's place, whose path is empty.
pub(crate) static ROOT: ReplyPath<'static> = ReplyPath {
    parent: None,
    key: "",
};

impl<'a> ReplyPath<'a> {
    /// The place of `key` in the object at this place.
    pub(crate) fn at(&'a self, key: &'a str) -> ReplyPath<'a> {
        ReplyPath {
            parent: Some(self),
            key,
        }
    }
}

/// The keys from the root joined by `/`, empty for the root.
impl fmt::Display for ReplyPath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(parent) = self.parent {
            parent.fmt(f)?;
            if parent.parent.is_some() {
                f.write_char('/')?;
            }
        }
        f.write_str(self.key)
    }
}

// What a place holds: a JSON kind, a rational, or its words quoted.
pub(crate) const STRING: &str = "string";
pub(crate) const BOOLEAN: &str = "boolean";
pub(crate) const NUMBER: &str = "number";
pub(crate) const ARRAY: &str = "array";
pub(crate) const OBJECT: &str = "object";
pub(crate) const A_RATIONAL: &str = "a rational";

/// What a reply's text holds before it is read as an object.
const JSON_TEXT: &str = "JSON text";

/// What came at a key the reply lacks.
const NOTHING: &str = "nothing";

/// The refusal of a reply place: `reply <path>: expected <expected>, got
/// <arrival>`, `reply: ...` at the whole reply.
pub(crate) fn refusal(path: ReplyPath<'_>, expected: &str, arrival: &str) -> Error {
    Error::Protocol(if path.parent.is_none() {
        format!("reply: expected {expected}, got {arrival}")
    } else {
        format!("reply {path}: expected {expected}, got {arrival}")
    })
}

/// What came at a place: the JSON kind of its value.
pub(crate) fn came_as(value: &RawValue) -> &'static str {
    wire_json::kind(value).as_str()
}

/// What `key` held in `obj`: its value's JSON kind, or nothing.
pub(crate) fn came(obj: &Object<'_>, key: &str) -> &'static str {
    obj.get(key).map_or(NOTHING, came_as)
}

/// What a word place held: its string quoted, another value's kind, or
/// nothing.
pub(crate) fn came_word(obj: &Object<'_>, key: &str) -> Cow<'static, str> {
    match obj.get(key).and_then(wire_json::string) {
        Some(word) => Cow::Owned(quote_json(&word)),
        None => Cow::Borrowed(came(obj, key)),
    }
}

/// A word place's words quoted: `"a"`, `"a" or "b"`, `"a", "b" or "c"`.
pub(crate) fn words(expected: &[&str]) -> String {
    let mut out = String::new();
    for (index, word) in expected.iter().enumerate() {
        if index > 0 {
            out.push_str(if index + 1 == expected.len() {
                " or "
            } else {
                ", "
            });
        }
        out.push_str(&quote_json(word));
    }
    out
}

/// `text` as a JSON string with every character outside printable ASCII
/// escaped, as Python's `json.dumps` writes it: the two-character escapes,
/// every other character below a space and every one from DEL on as `\u` and
/// four lowercase hex digits, a pair of them past U+FFFF. A string outside a
/// place's words then reads alike in the four bindings.
pub(crate) fn quote_json(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            ' '..='~' => out.push(c),
            _ => {
                for unit in c.encode_utf16(&mut [0; 2]) {
                    // Writing to a String cannot fail.
                    let _ = write!(out, "\\u{unit:04x}");
                }
            }
        }
    }
    out.push('"');
    out
}

/// The object a reply's text holds: text that is not one JSON value is refused
/// with serde_json's reason, and a value that is not an object by its kind.
pub(crate) fn read_reply(raw: &str) -> Result<Object<'_>, Error> {
    // A text holding one object is read in one pass. Any other text fails that
    // pass and is read again as one value, then as its object, which names its
    // fault: every refusal reads as that second reading alone writes it.
    if let Some(reply) = wire_json::parse_object(raw) {
        return Ok(reply);
    }
    let value = wire_json::parse(raw).map_err(|e| refusal(ROOT, JSON_TEXT, &e.to_string()))?;
    read_object(value, ROOT)
}

/// The object at `path`.
pub(crate) fn read_object<'a>(
    value: &'a RawValue,
    path: ReplyPath<'_>,
) -> Result<Object<'a>, Error> {
    wire_json::object(value).ok_or_else(|| refusal(path, OBJECT, came_as(value)))
}

/// The array at `path`.
pub(crate) fn read_array<'a>(
    value: &'a RawValue,
    path: ReplyPath<'_>,
) -> Result<Vec<&'a RawValue>, Error> {
    wire_json::array(value).ok_or_else(|| refusal(path, ARRAY, came_as(value)))
}

/// The string at `path`.
pub(crate) fn read_string<'a>(
    value: &'a RawValue,
    path: ReplyPath<'_>,
) -> Result<Cow<'a, str>, Error> {
    wire_json::string(value).ok_or_else(|| refusal(path, STRING, came_as(value)))
}

/// The boolean at `path`.
pub(crate) fn read_bool(value: &RawValue, path: ReplyPath<'_>) -> Result<bool, Error> {
    wire_json::boolean(value).ok_or_else(|| refusal(path, BOOLEAN, came_as(value)))
}

/// The whole number at `path`, signed.
pub(crate) fn read_sign_magnitude(
    value: &RawValue,
    path: ReplyPath<'_>,
) -> Result<SignMagnitude, Error> {
    wire_json::whole(value).ok_or_else(|| refusal(path, NUMBER, came_as(value)))
}

/// The whole number at a place the kernel proves natural, in the place's own
/// type, which holds the proven range.
pub(crate) fn read_natural<T: TryFrom<u128>>(
    value: &RawValue,
    path: ReplyPath<'_>,
) -> Result<T, Error> {
    wire_json::natural(value)
        .and_then(|n| T::try_from(n).ok())
        .ok_or_else(|| refusal(path, NUMBER, came_as(value)))
}

/// The whole number at a place whose proven range an `i64` holds, an
/// attribute's integer value or bound.
pub(crate) fn read_i64(value: &RawValue, path: ReplyPath<'_>) -> Result<i64, Error> {
    wire_json::whole(value)
        .and_then(|n| i64::try_from(n).ok())
        .ok_or_else(|| refusal(path, NUMBER, came_as(value)))
}

/// The rational at `path`, a number or its `{numerator, denominator}` object,
/// as [`wire_json::rational`] reads it; anything else is refused as a rational
/// expected.
pub(crate) fn read_rational(value: &RawValue, path: ReplyPath<'_>) -> Result<Rational, Error> {
    wire_json::rational(value).ok_or_else(|| refusal(path, A_RATIONAL, came_as(value)))
}

/// `key` of the object at `path`, read with `read`, which names its own
/// expectation for a value of the wrong kind; an absent key is refused as
/// nothing came, `expected` being what `read` expects.
fn field<'a, T>(
    obj: &Object<'a>,
    path: ReplyPath<'_>,
    key: &str,
    expected: &str,
    read: impl FnOnce(&'a RawValue, ReplyPath<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let place = path.at(key);
    match obj.get(key) {
        Some(value) => read(value, place),
        None => Err(refusal(place, expected, NOTHING)),
    }
}

// The fields of each kind, each refusing an absent key as nothing came.

pub(crate) fn field_object<'a>(
    obj: &Object<'a>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<Object<'a>, Error> {
    field(obj, path, key, OBJECT, read_object)
}

pub(crate) fn field_array<'a>(
    obj: &Object<'a>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<Vec<&'a RawValue>, Error> {
    field(obj, path, key, ARRAY, read_array)
}

pub(crate) fn field_string<'a>(
    obj: &Object<'a>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<Cow<'a, str>, Error> {
    field(obj, path, key, STRING, read_string)
}

pub(crate) fn field_bool(obj: &Object<'_>, path: ReplyPath<'_>, key: &str) -> Result<bool, Error> {
    field(obj, path, key, BOOLEAN, read_bool)
}

pub(crate) fn field_sign_magnitude(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<SignMagnitude, Error> {
    field(obj, path, key, NUMBER, read_sign_magnitude)
}

pub(crate) fn field_natural<T: TryFrom<u128>>(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<T, Error> {
    field(obj, path, key, NUMBER, read_natural)
}

pub(crate) fn field_i64(obj: &Object<'_>, path: ReplyPath<'_>, key: &str) -> Result<i64, Error> {
    field(obj, path, key, NUMBER, read_i64)
}

pub(crate) fn field_rational(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<Rational, Error> {
    field(obj, path, key, A_RATIONAL, read_rational)
}

/// The object at `key`, read with `read` at the key's place.
pub(crate) fn field_object_of<'a, T>(
    obj: &Object<'a>,
    path: ReplyPath<'_>,
    key: &str,
    read: impl FnOnce(&Object<'a>, ReplyPath<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let inner = field_object(obj, path, key)?;
    read(&inner, path.at(key))
}

/// The array at `key`, each entry an object read with `read` at the array's
/// place.
pub(crate) fn field_objects<'a, T>(
    obj: &Object<'a>,
    path: ReplyPath<'_>,
    key: &str,
    mut read: impl FnMut(&Object<'a>, ReplyPath<'_>) -> Result<T, Error>,
) -> Result<Vec<T>, Error> {
    let entries = field_array(obj, path, key)?;
    let place = path.at(key);
    entries
        .into_iter()
        .map(|entry| read(&read_object(entry, place)?, place))
        .collect()
}

/// The array at `key`, each entry a string.
pub(crate) fn field_strings(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<Vec<String>, Error> {
    let entries = field_array(obj, path, key)?;
    let place = path.at(key);
    entries
        .into_iter()
        .map(|entry| read_string(entry, place).map(Cow::into_owned))
        .collect()
}

/// The array at `key`, each entry a whole number the kernel proves natural.
pub(crate) fn field_naturals<T: TryFrom<u128>>(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
) -> Result<Vec<T>, Error> {
    let entries = field_array(obj, path, key)?;
    let place = path.at(key);
    entries
        .into_iter()
        .map(|entry| read_natural(entry, place))
        .collect()
}

/// The word at `key`, one of `expected`, any other refused with the words
/// quoted.
pub(crate) fn field_word(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
    expected: &[&'static str],
) -> Result<&'static str, Error> {
    if let Some(word) = obj.get(key).and_then(wire_json::string) {
        if let Some(&found) = expected.iter().find(|&&w| w == word) {
            return Ok(found);
        }
    }
    Err(refusal(
        path.at(key),
        &words(expected),
        &came_word(obj, key),
    ))
}

/// The word at `key` that `member` reads as a member of a table, any other
/// refused as `expected`, a string outside the table quoted as [`field_word`]
/// quotes it.
pub(crate) fn field_member<T>(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
    expected: &str,
    member: impl FnOnce(&str) -> Option<T>,
) -> Result<T, Error> {
    obj.get(key)
        .and_then(wire_json::string)
        .and_then(|word| member(&word))
        .ok_or_else(|| refusal(path.at(key), expected, &came_word(obj, key)))
}

/// The status at a reply's root. The readers await no status but these, whose
/// words [`ReplyStatus::word`] gives and [`field_status`] alone reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplyStatus {
    /// The answer to a command that succeeded.
    Success,
    /// The answer to a validation.
    Validation,
    /// The answer to the end of a stream.
    Complete,
    /// The acknowledgement of a frame or an event.
    Ack,
    /// The error any command may answer.
    Error,
}

impl ReplyStatus {
    /// The word the kernel writes for this status.
    pub(crate) fn word(self) -> &'static str {
        match self {
            ReplyStatus::Success => "success",
            ReplyStatus::Validation => "validation",
            ReplyStatus::Complete => "complete",
            ReplyStatus::Ack => "ack",
            ReplyStatus::Error => "error",
        }
    }
}

/// The status at `key`, one of `expected`, any other refused with the words
/// quoted as [`field_word`] refuses: the one reader of a status's word.
pub(crate) fn field_status(
    obj: &Object<'_>,
    path: ReplyPath<'_>,
    key: &str,
    expected: &[ReplyStatus],
) -> Result<ReplyStatus, Error> {
    if let Some(word) = obj.get(key).and_then(wire_json::string) {
        if let Some(&found) = expected.iter().find(|status| status.word() == word) {
            return Ok(found);
        }
    }
    let spellings: Vec<&str> = expected.iter().map(|status| status.word()).collect();
    Err(refusal(
        path.at(key),
        &words(&spellings),
        &came_word(obj, key),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The object a reply's `text` holds.
    fn reply(text: &str) -> Object<'_> {
        read_reply(text).expect("an object")
    }

    /// The text of the reply refusal `result` holds.
    #[track_caller]
    fn refused<T>(result: Result<T, Error>) -> String {
        match result {
            Err(Error::Protocol(text)) => text,
            Err(other) => panic!("expected a reply refusal, got {other:?}"),
            Ok(_) => panic!("expected a reply refusal, got a value"),
        }
    }

    /// A reader of the value at a key, its value dropped.
    type Reader = fn(&Object<'_>, ReplyPath<'_>, &str) -> Result<(), Error>;

    #[test]
    fn a_place_of_each_kind_refuses_every_other_kind_and_an_absent_key_in_the_one_form() {
        let held =
            reply(r#"{"null":null,"boolean":true,"number":7,"string":"s","array":[],"object":{}}"#);
        let kinds = ["null", "boolean", "number", "string", "array", "object"];
        // Each reader: what its place expects, the kind it takes, and itself.
        let readers: [(&str, &str, Reader); 8] = [
            (OBJECT, "object", |o, p, k| field_object(o, p, k).map(drop)),
            (ARRAY, "array", |o, p, k| field_array(o, p, k).map(drop)),
            (STRING, "string", |o, p, k| field_string(o, p, k).map(drop)),
            (BOOLEAN, "boolean", |o, p, k| field_bool(o, p, k).map(drop)),
            (NUMBER, "number", |o, p, k| {
                field_sign_magnitude(o, p, k).map(drop)
            }),
            (NUMBER, "number", |o, p, k| {
                field_natural::<u128>(o, p, k).map(drop)
            }),
            (NUMBER, "number", |o, p, k| field_i64(o, p, k).map(drop)),
            (A_RATIONAL, "number", |o, p, k| {
                field_rational(o, p, k).map(drop)
            }),
        ];
        for (expected, takes, read) in readers {
            for key in kinds {
                let result = read(&held, ROOT, key);
                if key == takes {
                    assert!(result.is_ok(), "{expected} at {key}: {result:?}");
                } else {
                    assert_eq!(
                        refused(result),
                        format!("reply {key}: expected {expected}, got {key}")
                    );
                }
            }
            assert_eq!(
                refused(read(&held, ROOT, "absent")),
                format!("reply absent: expected {expected}, got nothing")
            );
        }
    }

    #[test]
    fn a_path_joins_its_keys_and_an_array_entry_keeps_the_array_path() {
        let held = reply(r#"{"outer":{"inner":{"leaf":1}},"list":[{"leaf":"x"},{"leaf":2}]}"#);
        let leaf = |obj: &Object<'_>, place: ReplyPath<'_>| {
            field_string(obj, place, "leaf").map(Cow::into_owned)
        };
        let nested = field_object_of(&held, ROOT, "outer", |outer, place| {
            field_object_of(outer, place, "inner", leaf)
        });
        assert_eq!(
            refused(nested),
            "reply outer/inner/leaf: expected string, got number"
        );
        assert_eq!(
            refused(field_objects(&held, ROOT, "list", leaf)),
            "reply list/leaf: expected string, got number"
        );
        // The whole reply's place has an empty path.
        assert_eq!(
            refused(read_reply("[]")),
            "reply: expected object, got array"
        );
        assert_eq!(
            refused(read_reply("{} 7")),
            "reply: expected JSON text, got trailing characters at line 1 column 4"
        );
    }

    #[test]
    fn a_word_place_quotes_its_words_and_the_string_that_came() {
        let held = reply(r#"{"one":"x","word":"d","number":7}"#);
        assert_eq!(
            field_word(&held, ROOT, "one", &["x"]).expect("its word"),
            "x"
        );
        for (words, expected) in [
            (&["a"][..], r#""a""#),
            (&["a", "b"][..], r#""a" or "b""#),
            (&["a", "b", "c"][..], r#""a", "b" or "c""#),
        ] {
            assert_eq!(
                refused(field_word(&held, ROOT, "word", words)),
                format!(r#"reply word: expected {expected}, got "d""#)
            );
        }
        assert_eq!(
            refused(field_word(&held, ROOT, "number", &["a"])),
            r#"reply number: expected "a", got number"#
        );
        assert_eq!(
            refused(field_word(&held, ROOT, "absent", &["a"])),
            r#"reply absent: expected "a", got nothing"#
        );
        // A status place reads and refuses alike, the word that came quoted
        // as every binding quotes it.
        let status = reply(r#"{"status":"weird\u007f"}"#);
        assert_eq!(
            refused(field_status(
                &status,
                ROOT,
                "status",
                &[ReplyStatus::Complete, ReplyStatus::Error]
            )),
            r#"reply status: expected "complete" or "error", got "weird\u007f""#
        );
    }

    #[test]
    fn a_string_is_quoted_as_python_json_dumps_quotes_it() {
        // json.dumps(text, ensure_ascii=True) writes exactly this: the
        // two-character escapes, every other control character and DEL as
        // \u and four lowercase hex digits, and a character past U+FFFF as
        // its surrogate pair.
        let text = "a\"b\\c\nd\re\tf\u{8}g\u{c}h\u{1}i\u{1f}j\u{7f}k\u{e9}l\u{20ac}m\u{1f600}n ~";
        assert_eq!(
            quote_json(text),
            r#""a\"b\\c\nd\re\tf\bg\fh\u0001i\u001fj\u007fk\u00e9l\u20acm\ud83d\ude00n ~""#
        );
    }
}
