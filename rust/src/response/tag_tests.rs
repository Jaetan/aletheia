// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A validation issue's severity and code, an error reply's code, a property
//! result's type and status and a stream warning's kind hold a member of their
//! set or are refused at their place in the one form.

use super::tests::assert_refused;
use super::*;
use crate::dbc::decode_parsed_dbc;

/// The DBC object of the corpus's smallest snapshot.
const MINIMAL: &str =
    include_str!("../../../python/tests/fixtures/dbc_corpus/parity_snapshots/minimal.json");

/// A reader of a reply holding one validation issue, the object's JSON text.
type IssueReader = fn(&str) -> Result<(), Error>;

/// Each reply holding validation issues, the key it holds them at and the
/// reader taking it: a validation, a parsed DBC's warnings, a refused load's
/// envelope and a DBC text's diagnostics.
fn issue_readers() -> [(&'static str, IssueReader); 4] {
    [
        ("issues", |issue| {
            decode_validation(&format!(
                r#"{{"status":"validation","has_errors":false,"issues":[{issue}]}}"#
            ))
            .map(drop)
        }),
        ("warnings", |issue| {
            decode_parsed_dbc(&format!(
                r#"{{"status":"success","dbc":{MINIMAL},"warnings":[{issue}]}}"#
            ))
            .map(drop)
        }),
        ("issues", |issue| {
            Err(error_envelope(&format!(
                r#"{{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":[{issue}]}}"#
            )))
        }),
        ("issues", |issue| {
            decode_format_text(&format!(
                r#"{{"status":"success","text":"VERSION \"\"\n","issues":[{issue}]}}"#
            ))
            .map(drop)
        }),
    ]
}

#[test]
fn a_severity_outside_error_and_warning_is_refused_at_its_place() {
    let arrivals = [
        (
            r#"{"severity":"fatal","code":"factor_zero","detail":"d"}"#,
            r#""fatal""#,
        ),
        (r#"{"code":"factor_zero","detail":"d"}"#, "nothing"),
        (
            r#"{"severity":0,"code":"factor_zero","detail":"d"}"#,
            "number",
        ),
    ];
    for (key, read) in issue_readers() {
        for (issue, came) in arrivals {
            assert_refused(
                read(issue),
                &format!(r#"reply {key}/severity: expected "error" or "warning", got {came}"#),
            );
        }
    }
}

#[test]
fn an_issue_code_outside_the_issue_codes_is_refused_at_its_place() {
    let arrivals = [
        (
            r#"{"severity":"warning","code":"some_future_code","detail":"d"}"#,
            r#""some_future_code""#,
        ),
        (r#"{"severity":"warning","detail":"d"}"#, "nothing"),
        (r#"{"severity":"warning","code":0,"detail":"d"}"#, "number"),
    ];
    for (key, read) in issue_readers() {
        for (issue, came) in arrivals {
            assert_refused(
                read(issue),
                &format!("reply {key}/code: expected an issue code, got {came}"),
            );
        }
    }
}

#[test]
fn the_error_codes_are_those_of_the_wire_codes_record_in_its_order() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/WIRE_CODES.yaml");
    let text = std::fs::read_to_string(&path).expect("read docs/WIRE_CODES.yaml");
    let docs = yaml_rust2::YamlLoader::load_from_str(&text).expect("parse WIRE_CODES.yaml");
    let recorded: Vec<&str> = docs[0]["error_codes"]
        .as_vec()
        .expect("an error_codes sequence")
        .iter()
        .map(|entry| entry["name"].as_str().expect("a code's name"))
        .collect();
    let words: Vec<&str> = error_codes::ERROR_CODES
        .into_iter()
        .map(ErrorCode::as_str)
        .collect();
    assert_eq!(words, recorded);
    for (place, code) in error_codes::ERROR_CODES.iter().enumerate() {
        assert_eq!(*code as usize, place, "{code:?} is declared elsewhere");
        assert_eq!(
            snake_case(&format!("{code:?}")),
            code.as_str(),
            "{code:?} is named for another word"
        );
    }
}

/// `camel` in snake case: each capital lowered, an underscore before all but
/// the first.
fn snake_case(camel: &str) -> String {
    let mut snake = String::new();
    for c in camel.chars() {
        if c.is_ascii_uppercase() && !snake.is_empty() {
            snake.push('_');
        }
        snake.push(c.to_ascii_lowercase());
    }
    snake
}

#[test]
fn an_error_code_outside_the_error_codes_is_refused_at_its_place() {
    let arrivals = [
        (r#"{"status":"error","code":"c","message":"m"}"#, r#""c""#),
        (r#"{"status":"error","message":"m"}"#, "nothing"),
        (r#"{"status":"error","code":0,"message":"m"}"#, "number"),
    ];
    for (reply, came) in arrivals {
        let text = format!("reply code: expected an error code, got {came}");
        // The binary entries' envelope reader and a command's reply reader.
        assert_refused::<()>(Err(error_envelope(reply)), &text);
        assert_refused(decode_validation(reply), &text);
    }
}

/// A reader of a reply holding one entry, the entry's JSON text.
type EntryReader = fn(&str) -> Result<(), Error>;

/// The two replies holding property results: a frame's batch and the end of a
/// stream.
const RESULT_READERS: [EntryReader; 2] = [
    |result| {
        decode_frame(&format!(
            r#"{{"type":"property_batch","results":[{result}]}}"#
        ))
        .map(drop)
    },
    |result| {
        decode_stream(&format!(
            r#"{{"status":"complete","results":[{result}],"warnings":[]}}"#
        ))
        .map(drop)
    },
];

/// The end of a stream holding one warning.
fn stream_warning(warning: &str) -> Result<StreamResult, Error> {
    decode_stream(&format!(
        r#"{{"status":"complete","results":[],"warnings":[{warning}]}}"#
    ))
}

/// Each `(entry, came)` of `rows` read by each of `readers` is refused at
/// `place` expecting `expected`, every row compared at once so a failure shows
/// each row's answer.
#[track_caller]
fn assert_rows_refused(
    readers: &[EntryReader],
    place: &str,
    expected: &str,
    rows: &[(&str, &str)],
) {
    let mut answers = Vec::new();
    let mut refusals = Vec::new();
    for read in readers {
        for (entry, came) in rows {
            answers.push(match read(entry) {
                Err(Error::Protocol(text)) => text,
                other => format!("{other:?}"),
            });
            refusals.push(format!("reply {place}: expected {expected}, got {came}"));
        }
    }
    assert_eq!(answers, refusals);
}

#[test]
fn a_result_type_other_than_property_is_refused_at_its_place() {
    assert_rows_refused(
        &RESULT_READERS,
        "results/type",
        r#""property""#,
        &[
            (
                r#"{"type":"verdict","status":"holds","property_index":0}"#,
                r#""verdict""#,
            ),
            (r#"{"status":"holds","property_index":0}"#, "nothing"),
            (
                r#"{"type":0,"status":"holds","property_index":0}"#,
                "number",
            ),
        ],
    );
}

#[test]
fn a_result_status_outside_fails_holds_and_unresolved_is_refused_at_its_place() {
    assert_rows_refused(
        &RESULT_READERS,
        "results/status",
        r#""fails", "holds" or "unresolved""#,
        &[
            (
                r#"{"type":"property","status":"bogus","property_index":0,"reason":"r"}"#,
                r#""bogus""#,
            ),
            (
                r#"{"type":"property","property_index":0,"reason":"r"}"#,
                "nothing",
            ),
            (
                r#"{"type":"property","status":0,"property_index":0,"reason":"r"}"#,
                "number",
            ),
        ],
    );
}

#[test]
fn a_stream_warning_kind_other_than_uncached_atom_is_refused_at_its_place() {
    assert_eq!(
        stream_warning(r#"{"kind":"uncached_atom","property_index":3,"detail":"d"}"#)
            .expect("a warning")
            .warnings,
        [StreamWarning {
            kind: WarningKind::UncachedAtom,
            property_index: 3,
            detail: "d".to_owned(),
        }]
    );
    assert_rows_refused(
        &[|warning| stream_warning(warning).map(drop)],
        "warnings/kind",
        r#""uncached_atom""#,
        &[
            (
                r#"{"kind":"stale_atom","property_index":0,"detail":"d"}"#,
                r#""stale_atom""#,
            ),
            (r#"{"property_index":0,"detail":"d"}"#, "nothing"),
            (r#"{"kind":0,"property_index":0,"detail":"d"}"#, "number"),
        ],
    );
}
