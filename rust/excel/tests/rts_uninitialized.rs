// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The Excel loaders read every number but a DBC's message ID through the
//! kernel's decimal parser, which needs the GHC runtime up and never starts it.
//! Its own test binary, the runtime being process-global and one-shot: nothing
//! here starts it, so a load reading a number returns the parser's refusal as
//! it is, unlocated, and starts nothing, while a loader's own refusal of a path
//! answers on the path.

use aletheia::Error;
use aletheia_excel::{load_checks_from_excel, load_dbc_from_excel};
use rust_xlsxwriter::Workbook;

/// The refusal a number read answers while the runtime is down.
const RUNTIME_DOWN: &str = "GHC runtime not initialized: call aletheia::start_runtime or build a \
                            Client before rendering or parsing a number";

fn demo() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/demo/demo_workbook.xlsx")
}

/// A load reading a number with the RTS down: the typed runtime error, its
/// text, unlocated.
fn assert_the_runtime_refusal<T: std::fmt::Debug>(loaded: Result<T, Error>) {
    let err = loaded.expect_err("a load reading a number with the RTS down must be refused");
    assert!(
        matches!(err, Error::RtsNotInitialized),
        "expected Error::RtsNotInitialized; got: {err:?}"
    );
    assert_eq!(err.to_string(), RUNTIME_DOWN);
    assert_eq!((err.location(), err.key()), (None, None));
}

/// A workbook holding a When-Then sheet alone, its one row's numbers written as text.
fn when_then_workbook(path: &std::path::Path) {
    const HEADERS: [&str; 11] = [
        "Check Name",
        "When Signal",
        "When Condition",
        "When Value",
        "Then Signal",
        "Then Condition",
        "Then Value",
        "Then Min",
        "Then Max",
        "Within (ms)",
        "Severity",
    ];
    const ROW: [&str; 11] = [
        "",
        "BrakePedal",
        "exceeds",
        "50",
        "BrakeLight",
        "equals",
        "1",
        "",
        "",
        "100",
        "",
    ];
    let mut workbook = Workbook::new();
    let worksheet = workbook.add_worksheet();
    worksheet.set_name("When-Then").expect("name the sheet");
    for (column, (header, cell)) in (0u16..).zip(HEADERS.iter().zip(ROW)) {
        worksheet
            .write_string(0, column, *header)
            .expect("write a header");
        if !cell.is_empty() {
            worksheet
                .write_string(1, column, cell)
                .expect("write a text cell");
        }
    }
    workbook.save(path).expect("save the workbook");
}

#[test]
fn every_excel_loader_returns_the_runtime_refusal_unlocated_when_the_rts_is_uninitialised() {
    assert_the_runtime_refusal(load_checks_from_excel(demo()));
    let path = std::env::temp_dir().join(format!("aletheia_rts_down_{}.xlsx", std::process::id()));
    when_then_workbook(&path);
    let loaded = load_checks_from_excel(&path);
    let _ = std::fs::remove_file(&path);
    assert_the_runtime_refusal(loaded);
    assert_the_runtime_refusal(load_dbc_from_excel(demo()));
    assert_eq!(aletheia::allocated_bytes(), None);
}

#[test]
fn an_excel_loader_s_own_refusal_answers_on_its_path_when_the_rts_is_uninitialised() {
    let err = load_checks_from_excel("does-not-exist.xlsx")
        .expect_err("a workbook that does not exist must be refused");
    assert!(
        matches!(err, Error::Validation { code: None, .. }),
        "expected Error::Validation with no code; got: {err:?}"
    );
    assert_eq!(
        err.to_string(),
        "cannot stat does-not-exist.xlsx: No such file or directory (os error 2)"
    );
}
