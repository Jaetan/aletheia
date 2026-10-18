// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The Excel half of the cross-binding loader contract,
//! `docs/LOADER_SCENARIOS.yaml`, which the peer bindings read too: each
//! `excel` row's workbook, one data row on its `Checks` or `DBC` sheet, loads
//! to the rational the row names, or is refused as the kernel refused the
//! number, with the location and the column header the loader read it under
//! and the printed form `<location>: invalid '<key>': <message>`. Decimal
//! parsing is RTS-gated, so the test brings up a backend first.

use std::path::{Path, PathBuf};

use aletheia::{check, Client, Error, Rational};
use aletheia_excel::{load_checks_from_excel, load_dbc_from_excel};
use rust_xlsxwriter::Workbook;
use yaml_rust2::{Yaml, YamlLoader};

const CHECKS_HEADERS: [&str; 8] = [
    "Check Name",
    "Signal",
    "Condition",
    "Value",
    "Min",
    "Max",
    "Time (ms)",
    "Severity",
];

const DBC_HEADERS: [&str; 16] = [
    "Message ID",
    "Message Name",
    "Extended",
    "DLC",
    "Signal",
    "Start Bit",
    "Length",
    "Byte Order",
    "Signed",
    "Factor",
    "Offset",
    "Min",
    "Max",
    "Unit",
    "Multiplexor",
    "Multiplex Value",
];

/// A cell of a scenario's data row: text, the DBC sheet's boolean `Signed`
/// cell, or nothing.
enum Cell<'a> {
    Text(&'a str),
    False,
    Empty,
}

/// The contract's `Checks` row, `value` in its `Value` cell.
fn checks_row(value: &str) -> [Cell<'_>; 8] {
    use Cell::{Empty, Text};
    [
        Text("C"),
        Text("Speed"),
        Text("never_exceeds"),
        Text(value),
        Empty,
        Empty,
        Empty,
        Empty,
    ]
}

/// The contract's `DBC` row, `value` in its `Factor` cell.
fn dbc_row(value: &str) -> [Cell<'_>; 16] {
    use Cell::{Empty, False, Text};
    [
        Text("256"),
        Text("M"),
        Empty,
        Text("8"),
        Text("Sig"),
        Text("0"),
        Text("8"),
        Text("little_endian"),
        False,
        Text(value),
        Text("0"),
        Text("0"),
        Text("1"),
        Empty,
        Empty,
        Empty,
    ]
}

/// A workbook path that removes its file on drop.
struct TempXlsx(PathBuf);

impl Drop for TempXlsx {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Write a workbook of one sheet: its header row, then `row`.
fn write_workbook(path: &Path, sheet: &str, headers: &[&str], row: &[Cell]) {
    let mut workbook = Workbook::new();
    let worksheet = workbook.add_worksheet();
    worksheet.set_name(sheet).expect("name the sheet");
    for (column, header) in (0u16..).zip(headers) {
        worksheet
            .write_string(0, column, *header)
            .expect("write a header");
    }
    for (column, cell) in (0u16..).zip(row) {
        match cell {
            Cell::Text(text) => {
                worksheet
                    .write_string(1, column, *text)
                    .expect("write a text cell");
            }
            Cell::False => {
                worksheet
                    .write_boolean(1, column, false)
                    .expect("write a boolean cell");
            }
            Cell::Empty => {}
        }
    }
    workbook.save(path).expect("save the workbook");
}

fn contract() -> Yaml {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/LOADER_SCENARIOS.yaml");
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

#[test]
fn every_excel_row_loads_as_the_contract_says() {
    let _rts =
        Client::new().expect("init GHC RTS (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)");
    let contract = contract();
    let rows = contract["excel"]
        .as_vec()
        .expect("the contract holds an excel list");
    assert!(!rows.is_empty(), "the contract's excel list is empty");
    let mut failures = Vec::new();
    for row in rows {
        let scenario = text(row, "name", "an excel row");
        let value = text(row, "value", scenario);
        let expect = &row["expect"];
        let expected = expected_rational(expect, scenario);
        let path = std::env::temp_dir().join(format!(
            "aletheia_loader_scenario_{}_{scenario}.xlsx",
            std::process::id()
        ));
        let _cleanup = TempXlsx(path.clone());
        let found = match text(row, "sheet", scenario) {
            "Checks" => {
                write_workbook(&path, "Checks", &CHECKS_HEADERS, &checks_row(value));
                let expected =
                    expected.map(|r| vec![check::signal("Speed").never_exceeds(r).named("C")]);
                differences(load_checks_from_excel(&path), expected, expect, scenario)
            }
            "DBC" => {
                write_workbook(&path, "DBC", &DBC_HEADERS, &dbc_row(value));
                let factors = load_dbc_from_excel(&path).map(|dbc| {
                    dbc.messages
                        .iter()
                        .flat_map(|message| message.signals.iter().map(|signal| signal.factor))
                        .collect::<Vec<_>>()
                });
                differences(factors, expected.map(|r| vec![r]), expect, scenario)
            }
            other => panic!("{scenario}: the contract names no sheet {other:?}"),
        };
        failures.extend(found.into_iter().map(|d| format!("{scenario}: {d}")));
    }
    assert!(
        failures.is_empty(),
        "docs/LOADER_SCENARIOS.yaml, excel rows:\n{}",
        failures.join("\n")
    );
}
