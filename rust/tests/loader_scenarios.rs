// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#![cfg(feature = "yaml")]

//! The YAML half of the cross-binding loader contract,
//! `docs/LOADER_SCENARIOS.yaml`, which the peer bindings read too: each `yaml`
//! row's check document loads to the rational the row names and each
//! `yaml_within_ms` row's to the milliseconds it names, or is refused as the
//! kernel refused the number, with the location and the key the loader read it
//! under and the printed form `<location>: invalid '<key>': <message>`. Decimal
//! parsing is RTS-gated, so each test brings up a backend first.

use std::path::Path;

use aletheia::{check, load_checks_from_yaml, Check, Client, Error, Rational};
use yaml_rust2::{Yaml, YamlLoader};

fn contract() -> Yaml {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/LOADER_SCENARIOS.yaml");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    YamlLoader::load_from_str(&text)
        .expect("the loader contract is YAML")
        .into_iter()
        .next()
        .expect("the loader contract holds a document")
}

/// A text field of a contract row.
fn text<'a>(node: &'a Yaml, key: &str, scenario: &str) -> &'a str {
    node[key]
        .as_str()
        .unwrap_or_else(|| panic!("{scenario}: '{key}' is not a string"))
}

/// An unsigned number of the contract. A magnitude past `i64::MAX` reads as a
/// [`Yaml::Real`] holding its text.
fn unsigned(node: &Yaml, scenario: &str) -> u64 {
    let number = match node {
        Yaml::Integer(i) => u64::try_from(*i).ok(),
        Yaml::Real(s) => s.parse().ok(),
        _ => None,
    };
    number.unwrap_or_else(|| panic!("{scenario}: {node:?} is not an unsigned number"))
}

/// The rational a row expects the loader to read; `None` for a refusal row. A
/// row giving a rational and another answer is a mistake in the contract.
fn expected_rational(expect: &Yaml, scenario: &str) -> Option<Rational> {
    let pair = expect["rational"].as_vec()?;
    assert!(
        expect["milliseconds"].is_badvalue() && expect["kind"].is_badvalue(),
        "{scenario}: the contract gives a rational and another answer"
    );
    let part = |i: usize| {
        pair.get(i)
            .and_then(Yaml::as_i64)
            .unwrap_or_else(|| panic!("{scenario}: rational part {i} is not an integer"))
    };
    Some(Rational::new(part(0), part(1)).unwrap_or_else(|e| panic!("{scenario}: {e}")))
}

/// The milliseconds a row expects the loader to read; `None` for a refusal row.
/// A row giving milliseconds and another answer is a mistake in the contract.
fn expected_milliseconds(expect: &Yaml, scenario: &str) -> Option<u64> {
    let ms = &expect["milliseconds"];
    (!ms.is_badvalue()).then(|| {
        assert!(
            expect["rational"].is_badvalue() && expect["kind"].is_badvalue(),
            "{scenario}: the contract gives milliseconds and another answer"
        );
        unsigned(ms, scenario)
    })
}

/// How a refusal differs from the row's `expect`, one line per difference. A
/// refusal row that also gives a reading is a mistake in the contract.
fn refusal_differences(err: &Error, expect: &Yaml, scenario: &str) -> Vec<String> {
    assert!(
        expect["rational"].is_badvalue() && expect["milliseconds"].is_badvalue(),
        "{scenario}: the contract gives a refusal and a reading"
    );
    let kind = text(expect, "kind", scenario);
    let code = text(expect, "code", scenario);
    let location = text(expect, "location", scenario);
    let key = text(expect, "key", scenario);
    let printed = text(expect, "printed", scenario);
    let message = printed
        .strip_prefix(&format!("{location}: invalid '{key}': "))
        .unwrap_or_else(|| panic!("{scenario}: 'printed' does not open with its location and key"));
    let (got_kind, got_code, got_message) = match err {
        Error::Validation { message, code, .. } => ("validation", code.as_deref(), message),
        Error::InputBoundExceeded { code, message, .. } => {
            ("input_bound_exceeded", Some(code.as_str()), message)
        }
        other => return vec![format!("expected a {kind} refusal, got {other:?}")],
    };
    let (got_location, got_key) = (err.location(), err.key());
    let mut differences = Vec::new();
    if got_kind != kind {
        differences.push(format!("kind {got_kind}, expected {kind}"));
    }
    if got_code != Some(code) {
        differences.push(format!("code {got_code:?}, expected {code:?}"));
    }
    if got_message != message {
        differences.push(format!("message {got_message:?}, expected {message:?}"));
    }
    if got_location != Some(location) {
        differences.push(format!("location {got_location:?}, expected {location:?}"));
    }
    if got_key != Some(key) {
        differences.push(format!("key {got_key:?}, expected {key:?}"));
    }
    let shown = err.to_string();
    if shown != printed {
        differences.push(format!("printed {shown:?}, expected {printed:?}"));
    }
    if let Error::InputBoundExceeded {
        bound_kind,
        observed,
        limit,
        field,
        ..
    } = err
    {
        let bound = &expect["bound"];
        let got = (bound_kind.as_str(), *observed, *limit, field.as_deref());
        let want = (
            text(bound, "kind", scenario),
            unsigned(&bound["observed"], scenario),
            unsigned(&bound["limit"], scenario),
            Some(text(bound, "field", scenario)),
        );
        if got != want {
            differences.push(format!("bound {got:?}, expected {want:?}"));
        }
    }
    differences
}

/// How a load differs from the row's `expect`, one line per difference: the
/// value read against the expected one, or the refusal against the row's.
fn differences<T: PartialEq + std::fmt::Debug>(
    loaded: Result<T, Error>,
    expected: Option<T>,
    expect: &Yaml,
    scenario: &str,
) -> Vec<String> {
    match (loaded, expected) {
        (Ok(got), Some(want)) if got == want => Vec::new(),
        (Ok(got), Some(want)) => vec![format!("read {got:?}, expected {want:?}")],
        (Err(err), Some(want)) => vec![format!("refused with {err:?}, expected {want:?}")],
        (Ok(got), None) => vec![format!("read {got:?}, expected a refusal")],
        (Err(err), None) => refusal_differences(&err, expect, scenario),
    }
}

/// Loads the check document `document` builds around each value of the
/// contract's `section` and asserts it loads as the row's `expect` says, every
/// difference named by its scenario: `expected` gives the checks a reading row
/// loads to, `None` for a refusal row.
fn assert_rows_load_as_the_contract_says(
    section: &str,
    document: impl Fn(&str) -> String,
    expected: impl Fn(&Yaml, &str) -> Option<Vec<Check>>,
) {
    let _rts =
        Client::new().expect("init GHC RTS (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)");
    let contract = contract();
    let rows = contract[section]
        .as_vec()
        .unwrap_or_else(|| panic!("the contract holds no {section} list"));
    assert!(!rows.is_empty(), "the contract's {section} list is empty");
    let unnamed = format!("a {section} row");
    let mut failures = Vec::new();
    for row in rows {
        let scenario = text(row, "name", &unnamed);
        let value = text(row, "value", scenario);
        let expect = &row["expect"];
        let found = differences(
            load_checks_from_yaml(&document(value)),
            expected(expect, scenario),
            expect,
            scenario,
        );
        failures.extend(found.into_iter().map(|d| format!("{scenario}: {d}")));
    }
    assert!(
        failures.is_empty(),
        "docs/LOADER_SCENARIOS.yaml, {section} rows:\n{}",
        failures.join("\n")
    );
}

#[test]
fn every_yaml_row_loads_as_the_contract_says() {
    assert_rows_load_as_the_contract_says(
        "yaml",
        |value| {
            format!(
                "checks:\n  - name: \"C\"\n    signal: Speed\n    condition: never_exceeds\n    value: {value}\n"
            )
        },
        |expect, scenario| {
            expected_rational(expect, scenario)
                .map(|r| vec![check::signal("Speed").never_exceeds(r).named("C")])
        },
    );
}

#[test]
fn every_yaml_within_ms_row_loads_as_the_contract_says() {
    assert_rows_load_as_the_contract_says(
        "yaml_within_ms",
        |value| {
            format!(
                "checks:\n  - name: \"C\"\n    signal: Speed\n    condition: settles_between\n    min: 0\n    max: 100\n    within_ms: {value}\n"
            )
        },
        |expect, scenario| {
            expected_milliseconds(expect, scenario).map(|ms| {
                let settles = check::signal("Speed")
                    .settles_between(0, 100)
                    .within(ms)
                    .unwrap_or_else(|e| panic!("{scenario}: {e}"));
                vec![settles.named("C")]
            })
        },
    );
}
