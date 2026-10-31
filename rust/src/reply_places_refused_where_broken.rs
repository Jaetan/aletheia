// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Every reply reader accepts a broken place of a real reply or refuses it in
//! the one form. Each case's reply is the real kernel's answer to a command;
//! every place of it is broken in turn, its key deleted, its value replaced by
//! another JSON kind, or an array's entry so replaced, and each broken copy is
//! returned by a [`MockBackend`] to the [`Client`] method whose reader takes
//! that reply, which accepts it or refuses it as
//! `reply <path>: expected <what>, got <what came>` naming the broken place.
//! The cases and the breaks are those of the Go binding's
//! `reply_places_refused_where_broken_test.go` and the C++ binding's
//! `integration_tests_reply_places.cpp`.
//!
//! The replies come from the crate's own [`FfiBackend`], which holds the
//! binary entries' answers no public call returns, so the test lives in the
//! crate. It fails rather than skips without the library.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};

use serde_json::value::RawValue;

use crate::backend::{Backend, FfiBackend};
use crate::log::LogLevel;
use crate::ltl::{Formula, Predicate};
use crate::wire_json::{self, Kind, Wire};
use crate::{CanId, Client, Dbc, Dlc, Error, MockBackend, Rational, Timestamp};

/// The reader of a kernel reply, named by the command whose reply it reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Reader {
    ParseDbc,
    FormatDbc,
    FormatDbcText,
    ValidateDbc,
    Frame,
    EndStream,
    Extraction,
    Envelope,
}

/// The scenarios a real reply comes from, beside the corpus and the envelopes.
const KITCHEN_SINK: &str = "kitchen_sink";
const UNKNOWN_TARGET: &str = "value_tables with an unknown VAL_ target";
const TWIN: &str = "kitchen_sink with a twin message";
const FIVE_PROPERTIES: &str = "kitchen_sink with five properties";
const MIXED: &str = "a value, an over-range error and an absent signal";

/// The corpus DBCs every load case reads.
const CORPUS: [&str; 7] = [
    KITCHEN_SINK,
    "attributes",
    "comments_groups",
    "env_vars",
    "value_tables",
    "multiplexing",
    "extended_can",
];

/// One refused load: its fixture, the code its envelope carries, and the
/// kitchen_sink text the kernel refuses.
struct Envelope {
    fixture: &'static str,
    code: &'static str,
    text: fn(&str) -> String,
}

/// Four kitchen_sink variants, each refused with its code.
fn envelopes() -> [Envelope; 4] {
    [
        Envelope {
            fixture: "trailing input",
            code: "text_trailing_input",
            text: |base| format!("{base}\nBO_ 1 X: 8\n"),
        },
        Envelope {
            fixture: "invalid character",
            code: "dbc_invalid_character",
            text: |base| format!("{base}\nCM_ \"a\"\"b\";\n"),
        },
        Envelope {
            fixture: "identifier past its bound",
            code: "input_bound_exceeded",
            text: |base| base.replacen("BU_: ", &format!("BU_: {} ", "N".repeat(129)), 1),
        },
        Envelope {
            fixture: "validation failed",
            code: "handler_validation_failed",
            text: |base| {
                format!(
                    "{base}\nBO_ 256 Twin: 8 Engine\n SG_ D : 0|8@1+ (1,0) [0|255] \"\" Gateway\n"
                )
            },
        },
    ]
}

/// A reader and the real reply it is fed broken copies of.
type Case = (Reader, String);

/// Every case: each load and its formatted DBC, the text formatter and the
/// validator on kitchen_sink and its twin, a frame's batch, the end of that
/// stream, an extraction, and four refused loads.
fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for reader in [Reader::ParseDbc, Reader::FormatDbc] {
        for fixture in CORPUS.iter().chain([&UNKNOWN_TARGET]) {
            out.push((reader, (*fixture).to_owned()));
        }
    }
    for (reader, fixture) in [
        (Reader::FormatDbcText, KITCHEN_SINK),
        (Reader::FormatDbcText, TWIN),
        (Reader::ValidateDbc, KITCHEN_SINK),
        (Reader::ValidateDbc, TWIN),
        (Reader::Frame, FIVE_PROPERTIES),
        (Reader::EndStream, FIVE_PROPERTIES),
        (Reader::Extraction, MIXED),
    ] {
        out.push((reader, fixture.to_owned()));
    }
    for envelope in envelopes() {
        out.push((Reader::Envelope, envelope.fixture.to_owned()));
    }
    out
}

/// Message 256 of the mixed DBC holds a selector, a halved value, a signal
/// its selector leaves out and one whose value's numerator passes the wire's
/// 128-bit bound.
const MIXED_TEXT: &str = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 Mixed: 8 ECU\n \
    SG_ Mode M : 0|4@1+ (1,0) [0|15] \"\" Vector__XXX\n \
    SG_ Half m0 : 8|8@1+ (0.5,0) [0|127.5] \"\" Vector__XXX\n \
    SG_ Other m1 : 8|8@1+ (1,0) [0|255] \"\" Vector__XXX\n \
    SG_ Big : 16|17@1+ (0.12345678901234567890123456789012345678,0) [0|10000] \"\" Vector__XXX\n";

/// Mode 0, Half 3/2, Big all ones over its low 16 bits.
const MIXED_FRAME: [u8; 8] = [0x00, 0x03, 0xFF, 0xFF, 0, 0, 0, 0];

/// Speed 250 rpm and Temp 60 degC, then Speed 0: Temp holds, Speed under 100
/// fails.
const FIRST_FRAME: [u8; 8] = [0xE8, 0x03, 100, 0, 0, 0, 0, 0];
const SECOND_FRAME: [u8; 8] = [0x00, 0x00, 100, 0, 0, 0, 0, 0];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits in the repository")
        .to_path_buf()
}

/// A corpus DBC's text.
fn corpus_text(name: &str) -> String {
    let path = repo_root()
        .join("python/tests/fixtures/dbc_corpus")
        .join(format!("{name}.dbc"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// A reply as a tree whose leaves keep their text, so every number reads
/// back with its digits.
#[derive(Debug, Clone)]
enum Json {
    Object(BTreeMap<String, Json>),
    Array(Vec<Json>),
    Leaf(String),
}

impl Json {
    /// The tree of one JSON value's text.
    fn of(raw: &RawValue) -> Json {
        match wire_json::kind(raw) {
            Kind::Object => Json::Object(
                serde_json::from_str::<BTreeMap<String, &RawValue>>(raw.get())
                    .expect("an object")
                    .into_iter()
                    .map(|(key, value)| (key, Json::of(value)))
                    .collect(),
            ),
            Kind::Array => Json::Array(
                serde_json::from_str::<Vec<&RawValue>>(raw.get())
                    .expect("an array")
                    .into_iter()
                    .map(Json::of)
                    .collect(),
            ),
            _ => Json::Leaf(raw.get().trim().to_owned()),
        }
    }

    /// The tree of a reply, which the kernel writes as one JSON object.
    fn reply(raw: &str) -> Json {
        let value = wire_json::parse(raw)
            .unwrap_or_else(|e| panic!("a reply that is not JSON text: {e}: {raw}"));
        let tree = Json::of(value);
        assert!(
            matches!(tree, Json::Object(_)),
            "a reply that is not one JSON object: {raw}"
        );
        tree
    }

    /// The tree as JSON text, an object's keys in byte order.
    fn text(&self) -> String {
        match self {
            Json::Object(members) => {
                let inner: Vec<String> = members
                    .iter()
                    .map(|(key, value)| {
                        format!(
                            "{}:{}",
                            serde_json::to_string(key).expect("a key"),
                            value.text()
                        )
                    })
                    .collect();
                format!("{{{}}}", inner.join(","))
            }
            Json::Array(entries) => {
                let inner: Vec<String> = entries.iter().map(Json::text).collect();
                format!("[{}]", inner.join(","))
            }
            Json::Leaf(text) => text.clone(),
        }
    }

    /// The value at `key` of an object.
    fn at(&self, key: &str) -> &Json {
        match self {
            Json::Object(members) => members
                .get(key)
                .unwrap_or_else(|| panic!("no {key} in {}", self.text())),
            _ => panic!("{key} of a value that is not an object: {}", self.text()),
        }
    }
}

/// Holds that a reply's key holds the word given.
fn require_word(reply: &Json, key: &str, want: &str) {
    let found = reply.at(key).text();
    assert_eq!(
        found,
        serde_json::to_string(want).expect("a word"),
        "reply {key}: {}",
        reply.text()
    );
}

/// A session of the real kernel.
fn session() -> FfiBackend {
    FfiBackend::new(None, None, LogLevel::Warn)
        .expect("load libaletheia-ffi.so for test (is ALETHEIA_LIB set?)")
}

/// The kernel's reply to the JSON command `name` carrying the JSON text
/// `value` under `key`.
fn command(backend: &FfiBackend, name: &str, key: &'static str, value: &str) -> Json {
    let raw = RawValue::from_string(value.to_owned()).expect("JSON text");
    let line = wire_json::command(name, key, &*raw).expect("a command");
    Json::reply(&backend.process(&line).expect("a reply"))
}

/// The kernel's parseDBCText reply for a DBC text.
fn load(backend: &FfiBackend, text: &str) -> Json {
    let line = wire_json::command("parseDBCText", "text", text).expect("a command");
    Json::reply(&backend.process(&line).expect("a reply"))
}

/// The DBC with a copy of its first message appended under another name,
/// sharing its id.
fn with_twin(dbc: &Json) -> Json {
    let mut out = dbc.clone();
    let Json::Object(members) = &mut out else {
        panic!("a DBC that is not an object")
    };
    let Some(Json::Array(messages)) = members.get_mut("messages") else {
        panic!("a DBC without messages")
    };
    let mut twin = messages.first().expect("a first message").clone();
    let Json::Object(fields) = &mut twin else {
        panic!("a message that is not an object")
    };
    fields.insert("name".to_owned(), Json::Leaf("\"Twin\"".to_owned()));
    messages.push(twin);
    out
}

fn standard_256() -> CanId {
    CanId::standard(256).expect("an 11-bit id")
}

fn eight_bytes() -> Dlc {
    Dlc::new(8).expect("DLC 8")
}

/// Loads every corpus DBC and the variant with an unknown VAL_ target, then
/// formats each back.
fn load_replies(replies: &mut BTreeMap<Case, Json>) {
    let mut texts: Vec<(String, String)> = CORPUS
        .iter()
        .map(|name| ((*name).to_owned(), corpus_text(name)))
        .collect();
    texts.push((
        UNKNOWN_TARGET.to_owned(),
        corpus_text("value_tables") + "\nVAL_ 999 Ghost 0 \"Zero\" ;\n",
    ));
    for (name, text) in texts {
        let backend = session();
        replies.insert((Reader::ParseDbc, name.clone()), load(&backend, &text));
        let formatted = backend.format_dbc_binary().expect("a formatDBC reply");
        replies.insert((Reader::FormatDbc, name), Json::reply(&formatted));
    }
}

/// Formats and validates kitchen_sink's DBC and its twin-message variant.
fn dbc_command_replies(replies: &mut BTreeMap<Case, Json>) {
    let kitchen = replies[&(Reader::ParseDbc, KITCHEN_SINK.to_owned())]
        .at("dbc")
        .clone();
    let twin = with_twin(&kitchen);
    for (name, body) in [(KITCHEN_SINK, kitchen), (TWIN, twin)] {
        let backend = session();
        let text = body.text();
        replies.insert(
            (Reader::FormatDbcText, name.to_owned()),
            command(&backend, "formatDBCText", "dbc", &text),
        );
        replies.insert(
            (Reader::ValidateDbc, name.to_owned()),
            command(&backend, "validateDBC", "dbc", &text),
        );
    }
}

/// Streams kitchen_sink under five properties: a batch on the first frame,
/// then the end.
fn stream_replies(replies: &mut BTreeMap<Case, Json>) {
    let above = |signal: &str, value: i128| {
        Formula::Eventually(Box::new(Formula::Atomic(Predicate::GreaterThan {
            signal: signal.to_owned(),
            value: Rational::integer(value),
        })))
    };
    let below = |signal: &str, value: i128| {
        Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
            signal: signal.to_owned(),
            value: Rational::integer(value),
        })))
    };
    let formulas = [
        above("Temp", 0),
        below("Speed", 100),
        above("Pressure", 10),
        below("Pressure", 100),
        above("Speed", 5000),
    ];
    let backend = session();
    require_word(
        &load(&backend, &corpus_text(KITCHEN_SINK)),
        "status",
        "success",
    );
    let line =
        wire_json::command("setProperties", "properties", &Wire(&formulas[..])).expect("a command");
    require_word(
        &Json::reply(&backend.process(&line).expect("a reply")),
        "status",
        "success",
    );
    backend.start_stream_binary().expect("a startStream reply");
    let send = |ts, frame: &[u8]| {
        let raw = backend
            .send_frame_binary(
                Timestamp(ts),
                standard_256(),
                eight_bytes(),
                frame,
                None,
                None,
            )
            .expect("a frame reply");
        Json::reply(&raw)
    };
    let first = send(1000, &FIRST_FRAME);
    require_word(&first, "type", "property_batch");
    send(2000, &SECOND_FRAME);
    let end = Json::reply(&backend.end_stream_binary().expect("an endStream reply"));
    replies.insert((Reader::Frame, FIVE_PROPERTIES.to_owned()), first);
    replies.insert((Reader::EndStream, FIVE_PROPERTIES.to_owned()), end);
}

/// Extracts message 256 of the mixed DBC through the JSON-answering entry.
fn extraction_reply(replies: &mut BTreeMap<Case, Json>) {
    let backend = session();
    require_word(&load(&backend, MIXED_TEXT), "status", "success");
    let raw = backend
        .extract_signals_binary(standard_256(), eight_bytes(), &MIXED_FRAME)
        .expect("an extraction reply");
    replies.insert((Reader::Extraction, MIXED.to_owned()), Json::reply(&raw));
}

/// Refuses the four kitchen_sink variants, each with the code its fixture
/// names.
fn envelope_replies(replies: &mut BTreeMap<Case, Json>) {
    let base = corpus_text(KITCHEN_SINK);
    for envelope in envelopes() {
        let reply = load(&session(), &(envelope.text)(&base));
        require_word(&reply, "code", envelope.code);
        replies.insert((Reader::Envelope, envelope.fixture.to_owned()), reply);
    }
}

/// Every case's reply, answered by the real kernel.
fn kernel_replies() -> BTreeMap<Case, Json> {
    let mut replies = BTreeMap::new();
    load_replies(&mut replies);
    dbc_command_replies(&mut replies);
    stream_replies(&mut replies);
    extraction_reply(&mut replies);
    envelope_replies(&mut replies);
    let all = cases();
    for case in &all {
        assert!(replies.contains_key(case), "no reply for {case:?}");
    }
    assert_eq!(replies.len(), all.len(), "one reply per case");
    replies
}

/// How a place is broken: its key deleted, its value or an array's entry
/// replaced by another kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Breakage {
    Deleted,
    Retyped,
    EntryRetyped,
}

/// One step from a value to one inside it: an object's key or an array's
/// position.
#[derive(Debug, Clone)]
enum Step {
    Key(String),
    Index(usize),
}

/// One broken copy: the place, as a refusal names it, the value's steps from
/// the root, how it is broken and what replaces it.
struct Break {
    path: String,
    steps: Vec<Step>,
    breakage: Breakage,
    replacement: Option<Json>,
}

/// Whether a value is the kernel's `{numerator, denominator}` object, a leaf
/// of the reply proof.
fn is_wire_rational(value: &Json) -> bool {
    matches!(value, Json::Object(members)
        if members.len() == 2 && members.contains_key("numerator")
            && members.contains_key("denominator"))
}

/// A value's replacements: "x" for a number, 0 for the rest, both for a
/// rational.
fn stand_ins(value: &Json) -> Vec<Json> {
    let zero = Json::Leaf("0".to_owned());
    let x = Json::Leaf("\"x\"".to_owned());
    if is_wire_rational(value) {
        return vec![zero, x];
    }
    match value {
        Json::Leaf(text) if text.starts_with(|c: char| c == '-' || c.is_ascii_digit()) => vec![x],
        _ => vec![zero],
    }
}

/// Adds a break of every place below `value` to `out`: each key deleted and
/// retyped, each entry retyped, keys in their sorted order.
fn add_breaks(value: &Json, path: &str, steps: &[Step], out: &mut Vec<Break>) {
    match value {
        Json::Object(members) if !is_wire_rational(value) => {
            for (key, inner) in members {
                let here = if path.is_empty() {
                    key.clone()
                } else {
                    format!("{path}/{key}")
                };
                let mut at = steps.to_vec();
                at.push(Step::Key(key.clone()));
                out.push(Break {
                    path: here.clone(),
                    steps: at.clone(),
                    breakage: Breakage::Deleted,
                    replacement: None,
                });
                for stand_in in stand_ins(inner) {
                    out.push(Break {
                        path: here.clone(),
                        steps: at.clone(),
                        breakage: Breakage::Retyped,
                        replacement: Some(stand_in),
                    });
                }
                add_breaks(inner, &here, &at, out);
            }
        }
        Json::Array(entries) => {
            for (index, entry) in entries.iter().enumerate() {
                let mut at = steps.to_vec();
                at.push(Step::Index(index));
                for stand_in in stand_ins(entry) {
                    out.push(Break {
                        path: path.to_owned(),
                        steps: at.clone(),
                        breakage: Breakage::EntryRetyped,
                        replacement: Some(stand_in),
                    });
                }
                add_breaks(entry, path, &at, out);
            }
        }
        _ => {}
    }
}

/// Every break of a reply.
fn breaks_of(reply: &Json) -> Vec<Break> {
    let mut out = Vec::new();
    add_breaks(reply, "", &[], &mut out);
    out
}

/// `value` with the place `steps` lead to broken as `change` says.
fn broken(value: &mut Json, steps: &[Step], change: &Break) {
    let (step, rest) = steps.split_first().expect("a step");
    match (value, step) {
        (Json::Object(members), Step::Key(key)) => {
            if !rest.is_empty() {
                broken(members.get_mut(key).expect("the key"), rest, change);
            } else if let Some(replacement) = &change.replacement {
                members.insert(key.clone(), replacement.clone());
            } else {
                members.remove(key);
            }
        }
        (Json::Array(entries), Step::Index(index)) => {
            let entry = entries.get_mut(*index).expect("the entry");
            if rest.is_empty() {
                *entry = change.replacement.clone().expect("an entry is retyped");
            } else {
                broken(entry, rest, change);
            }
        }
        _ => panic!("a step below a value that holds no such place"),
    }
}

/// The reply with the place `change` names broken as it says.
fn broken_copy(reply: &Json, change: &Break) -> Json {
    let mut out = reply.clone();
    broken(&mut out, &change.steps, change);
    out
}

/// What came at the broken place: nothing for a deleted key, else its kind.
fn arrival(change: &Break) -> &'static str {
    match &change.replacement {
        None => "nothing",
        Some(Json::Leaf(text)) if text.starts_with('"') => "string",
        Some(_) => "number",
    }
}

/// A value's steps spelled as dbc.messages[0].signals[1].factor.
fn spelled(steps: &[Step]) -> String {
    let mut out = String::new();
    for step in steps {
        match step {
            Step::Key(key) if out.is_empty() => out.push_str(key),
            Step::Key(key) => {
                out.push('.');
                out.push_str(key);
            }
            Step::Index(index) => out.push_str(&format!("[{index}]")),
        }
    }
    out
}

/// What the client method whose reader takes the case's reply answers when
/// a [`MockBackend`] returns `raw` to it: the reader the client applies to
/// the command's answer, an error envelope read by the one the refused
/// load's answer takes.
fn read_broken(reader: Reader, raw: String) -> Result<(), Error> {
    let mock = MockBackend::new();
    mock.respond_json(raw);
    let client = Client::with_backend(Box::new(mock));
    let empty = Dbc {
        version: String::new(),
        messages: Vec::new(),
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    };
    let payload = [0u8; 8];
    match reader {
        Reader::ParseDbc | Reader::Envelope => client.parse_dbc_text("").map(drop),
        Reader::FormatDbc => client.format_dbc().map(drop),
        Reader::FormatDbcText => client.format_dbc_text(&empty).map(drop),
        Reader::ValidateDbc => client.validate_dbc(&empty).map(drop),
        Reader::Frame => client
            .send_frame(
                Timestamp(0),
                standard_256(),
                eight_bytes(),
                &payload,
                None,
                None,
            )
            .map(drop),
        Reader::EndStream => client.end_stream().map(drop),
        Reader::Extraction => client
            .extract_signals(standard_256(), eight_bytes(), &payload)
            .map(drop),
    }
}

/// How the case's reader took a broken copy: empty for an acceptance or the
/// one form naming the broken place. An error envelope's reader accepts by
/// answering the error the envelope carries.
fn verdict(reader: Reader, change: &Break, raw: String) -> String {
    let answer = match panic::catch_unwind(AssertUnwindSafe(|| read_broken(reader, raw))) {
        Ok(answer) => answer,
        Err(_) => return "panicked".to_owned(),
    };
    match answer {
        Ok(()) => String::new(),
        Err(Error::Protocol(text)) => {
            let head = format!("reply {}: expected ", change.path);
            let tail = format!(", got {}", arrival(change));
            if text.starts_with(&head) && text.ends_with(&tail) {
                String::new()
            } else {
                format!("refused as {text:?}")
            }
        }
        Err(_) if reader == Reader::Envelope => String::new(),
        Err(other) => format!("answered {other:?}"),
    }
}

/// The broken copies of the case's reply its reader took out of the one
/// form, one line for each path, breakage and verdict.
fn out_of_form(reader: Reader, reply: &Json) -> Vec<String> {
    let mut order: Vec<(String, Breakage, String)> = Vec::new();
    let mut seen: BTreeMap<(String, Breakage, String), (String, usize)> = BTreeMap::new();
    for change in breaks_of(reply) {
        let said = verdict(reader, &change, broken_copy(reply, &change).text());
        if said.is_empty() {
            continue;
        }
        let failure = (change.path.clone(), change.breakage, said);
        let entry = seen.entry(failure.clone()).or_insert_with(|| {
            order.push(failure);
            (spelled(&change.steps), 0)
        });
        entry.1 += 1;
    }
    order
        .iter()
        .map(|failure| {
            let (first, copies) = &seen[failure];
            format!(
                "{} {:?} (at {first}, x{copies}): {}",
                failure.0, failure.1, failure.2
            )
        })
        .collect()
}

/// A reader accepts each broken place of a real reply or refuses it as
/// `reply <path>: expected ..., got ...` naming the place.
#[test]
fn a_broken_reply_place_is_accepted_or_refused_in_the_one_form() {
    let replies = kernel_replies();
    let mut failures = Vec::new();
    for case in cases() {
        let lines = out_of_form(case.0, &replies[&case]);
        if !lines.is_empty() {
            failures.push(format!(
                "{:?} on {}: {} broken places out of the one form\n{}",
                case.0,
                case.1,
                lines.len(),
                lines.join("\n")
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The reply proof's table names and the paths each holds, read from its
/// replyRange, replyText and replyNonEmpty clauses: a table, then its path as
/// keys before [].
fn proof_paths() -> BTreeMap<String, BTreeSet<String>> {
    let path = repo_root().join("src/Aletheia/Protocol/ReplyRange.agda");
    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut tables: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for line in source.lines() {
        let Some((table, rest)) = ["replyRange", "replyText", "replyNonEmpty"]
            .iter()
            .find_map(|table| Some((*table, line.strip_prefix(table)?.strip_prefix(" (")?)))
        else {
            continue;
        };
        let mut keys = Vec::new();
        let mut rest = rest;
        while let Some(quoted) = rest.strip_prefix('"') {
            let (key, after) = quoted
                .split_once('"')
                .unwrap_or_else(|| panic!("a clause the test cannot read: {line}"));
            keys.push(key);
            rest = after
                .strip_prefix(" \u{2237} ")
                .unwrap_or_else(|| panic!("a clause the test cannot read: {line}"));
        }
        assert!(
            !keys.is_empty() && rest.starts_with("[])"),
            "a clause the test cannot read: {line}"
        );
        tables
            .entry(table.to_owned())
            .or_default()
            .insert(keys.join("/"));
    }
    tables
}

/// Each path of the reply proof's three tables is broken in some case's
/// reply.
#[test]
fn every_place_the_reply_proof_names_is_broken_by_some_case() {
    let tables = proof_paths();
    assert_eq!(
        tables.keys().map(String::as_str).collect::<Vec<_>>(),
        ["replyNonEmpty", "replyRange", "replyText"]
    );
    let replies = kernel_replies();
    let broken_paths: BTreeSet<String> = cases()
        .iter()
        .flat_map(|case| breaks_of(&replies[case]))
        .map(|change| change.path)
        .collect();
    let unbroken: Vec<String> = tables
        .iter()
        .flat_map(|(table, paths)| {
            paths
                .iter()
                .filter(|path| !broken_paths.contains(*path))
                .map(move |path| format!("{table}: {path}"))
        })
        .collect();
    assert!(
        unbroken.is_empty(),
        "paths no case breaks:\n{}",
        unbroken.join("\n")
    );
}
