// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Aletheia Excel check + DBC loader.
//!
//! A separate crate so the `.xlsx` dependency chain (calamine reader +
//! rust_xlsxwriter writer + zip for the ZIP-bomb guard) stays optional for core
//! users — mirroring Go's `go/excel/` module and Python's `aletheia.excel_loader`.
//!
//! # Column-handling contract (shared across all bindings)
//! Cells are looked up by **header name** (position-independent — a technician
//! may reorder or delete columns they don't use), and an **absent column is
//! treated exactly like an empty cell**:
//! - required fields error when empty (naming the row, the column, what was
//!   found, and what was expected);
//! - optional fields fall back to a default (`Extended` → standard, `Unit` → "",
//!   the `Multiplexor`/`Multiplex Value` pair → always-present).
//!
//! Coercion is **strict** and follows the float principle: a number cell
//! stores a lossy IEEE-754 double, so every numeric field must be **text-formatted**
//! and is parsed EXACTLY by the kernel [`Rational::from_decimal`] (the cross-binding
//! single source of truth), and a number-typed cell is rejected. A whole-number
//! field (`DLC`, `Start Bit`, `Length`, `Multiplex Value`) is that rational
//! with a fraction refused, and a time window (`Time (µs)`, `Within (µs)`) is
//! whole microseconds the kernel reads from the cell's text through
//! [`TimeBound::parse`]. `Message ID` also takes a hex string (`0x100`);
//! `Signed` is a native boolean. Because the kernel reads every number and
//! builds every check, loading a workbook requires the GHC runtime up. A check
//! the kernel refuses where it is built keeps the builder's error, located at
//! its row with no column (see [`Error::located_at`]). The compiled formulas
//! and the typed [`Dbc`] delegate every value to the verified core via the main
//! `aletheia` crate.

use std::collections::HashMap;
use std::path::Path;

use calamine::{open_workbook, Data, Range, Reader, Xlsx};
use rust_xlsxwriter::{Format, Workbook};

use aletheia::check::{self, Check};
use aletheia::{
    ByteOrder, CanId, Dbc, DbcMessage, DbcSignal, Dlc, Error, Presence, Rational, SignMagnitude,
    TimeBound,
};

/// The shared 64 MiB input-length cap (Python `MAX_DBC_TEXT_BYTES`, Go
/// `MaxDBCTextBytes`). An `.xlsx` is a ZIP archive that the reader all-loads, so
/// the cap is applied at this trust boundary — to the raw file size *and* to the
/// sum of uncompressed entry sizes (ZIP-bomb guard) — before any parsing.
const MAX_INPUT_BYTES: u64 = 64 * 1024 * 1024;

// ── Sheet names + headers ─────────────────────────────────────────────────────

const DBC_SHEET: &str = "DBC";
const CHECKS_SHEET: &str = "Checks";
const WHEN_THEN_SHEET: &str = "When-Then";

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

const CHECKS_HEADERS: [&str; 8] = [
    "Check Name",
    "Signal",
    "Condition",
    "Value",
    "Min",
    "Max",
    "Time (µs)",
    "Severity",
];

const WHEN_THEN_HEADERS: [&str; 11] = [
    "Check Name",
    "When Signal",
    "When Condition",
    "When Value",
    "Then Signal",
    "Then Condition",
    "Then Value",
    "Then Min",
    "Then Max",
    "Within (µs)",
    "Severity",
];

fn invalid(msg: impl Into<String>) -> Error {
    Error::validation(msg)
}

/// The all-text-contract rejection for a numeric field supplied as a *number*
/// cell. Names the row (`ctx`), the column (`key`) and the offending value
/// (`got`) so a single stray number cell hiding in a column of text — which looks
/// identical in the spreadsheet — is locatable from the error alone. Identical in
/// shape across all four bindings (Python `get_excel_number`, Go `xlsxRational`,
/// C++ `get_decimal`).
fn number_cell_error(ctx: &str, key: &str, got: impl std::fmt::Display) -> Error {
    invalid(format!(
        "{ctx}: '{key}' is a number cell (got {got}); format it as TEXT so the exact \
         value is preserved (a number cell stores a lossy float)"
    ))
}

// ── Row model: header name → cell, present cells only ─────────────────────────

/// A data row keyed by header name, holding only the **present** cells (an empty
/// or whitespace-only cell is dropped, so it reads identically to an absent
/// column — the core of the "absent column ≡ empty cell" contract).
type Row = HashMap<String, Data>;

/// Whether a cell carries a value. An empty cell, or a string that is empty
/// after trimming, counts as absent.
fn cell_present(d: &Data) -> bool {
    match d {
        Data::Empty => false,
        Data::String(s) => !s.trim().is_empty(),
        _ => true,
    }
}

/// Stringify a header cell (numbers/bools become their textual form; an empty
/// header yields `""`, whose column is then ignored).
fn header_name(d: &Data) -> String {
    match d {
        Data::String(s) => s.trim().to_string(),
        Data::Int(n) => n.to_string(),
        Data::Float(f) => f.to_string(),
        Data::Bool(b) => b.to_string(),
        _ => String::new(),
    }
}

/// Split a worksheet range into `(row_number, row_map)` pairs. The first row is
/// the header; every column is read (no positional cap). Cells under an empty
/// header, and empty cells, are dropped. `row_number` is 1-based and skips the
/// header (so the first data row is row 2), for human-facing error context.
fn rows_to_maps(range: &Range<Data>) -> Vec<(usize, Row)> {
    let mut iter = range.rows();
    let Some(header_row) = iter.next() else {
        return Vec::new();
    };
    let headers: Vec<String> = header_row.iter().map(header_name).collect();
    let mut out = Vec::new();
    for (i, row) in iter.enumerate() {
        let mut map = Row::new();
        for (h, cell) in headers.iter().zip(row.iter()) {
            if h.is_empty() || !cell_present(cell) {
                continue;
            }
            map.insert(h.clone(), cell.clone());
        }
        out.push((i + 2, map));
    }
    out
}

// ── Strict typed cell accessors (match Python `_loader_utils`) ────────────────

/// A required text field. The cell must be a string — a numeric or boolean cell
/// is rejected (strict, matching `openpyxl`).
fn get_str(row: &Row, key: &str, ctx: &str) -> Result<String, Error> {
    match row.get(key) {
        Some(Data::String(s)) if !s.trim().is_empty() => Ok(s.clone()),
        Some(other) => Err(invalid(format!(
            "{ctx}: '{key}' must be text, got {}",
            describe(other)
        ))),
        None => Err(invalid(format!(
            "{ctx}: missing required '{key}' (expected text)"
        ))),
    }
}

/// The trimmed text of a required numeric field. A spreadsheet number cell
/// stores an IEEE-754 double, lossy for decimals, so a numeric value MUST be
/// **text-formatted**, its original string being what the kernel reads; a
/// number-typed cell is rejected, naming the row (`ctx`) and the column
/// (`key`).
fn numeric_text<'a>(row: &'a Row, key: &str, ctx: &str) -> Result<&'a str, Error> {
    match row.get(key) {
        Some(Data::String(s)) => Ok(s.trim()),
        // The all-text contract rejects EVERY number cell, integer or decimal: a
        // spreadsheet stores numbers as lossy IEEE-754 doubles (calamine surfaces
        // even an integer cell as `Data::Float`). Rejecting both `Int` and `Float`
        // makes the contract hold regardless of how the reader types the cell,
        // rather than relying on calamine's "all xlsx numbers are Float" detail.
        Some(Data::Int(n)) => Err(number_cell_error(ctx, key, n)),
        Some(Data::Float(f)) => Err(number_cell_error(ctx, key, f)),
        Some(other) => Err(invalid(format!(
            "{ctx}: '{key}' must be a text-formatted number, got {}",
            describe(other)
        ))),
        None => Err(invalid(format!(
            "{ctx}: missing required '{key}' (expected a text-formatted number)"
        ))),
    }
}

/// A required numeric field as an exact [`Rational`], its [`numeric_text`]
/// parsed by the kernel [`Rational::from_decimal`] (the cross-binding single
/// source of truth); a refusal of it keeps the kernel's error and gains the row
/// (`ctx`) as its location and the column header (`key`) as its key. Needs the
/// GHC runtime up (the kernel reads the number).
fn get_rational(row: &Row, key: &str, ctx: &str) -> Result<Rational, Error> {
    Rational::from_decimal(numeric_text(row, key, ctx)?).map_err(|e| e.located(ctx, key))
}

/// A required whole-number field: the same cell, read the same way as
/// [`get_rational`], with a fraction refused.
fn get_whole(row: &Row, key: &str, ctx: &str) -> Result<SignMagnitude, Error> {
    let r = get_rational(row, key, ctx)?;
    if r.denominator() != 1 {
        let text = numeric_text(row, key, ctx)?;
        return Err(invalid(format!(
            "{ctx}: '{key}' must be a whole number, got {text:?}"
        )));
    }
    Ok(SignMagnitude {
        negative: r.is_negative(),
        magnitude: r.numerator(),
    })
}

/// A required whole number a 16-bit field holds, refusing one it cannot; the
/// kernel decides the field's range when it reads the definition.
fn get_u16(row: &Row, key: &str, ctx: &str) -> Result<u16, Error> {
    let w = get_whole(row, key, ctx)?;
    match u16::try_from(w.magnitude) {
        Ok(v) if !w.negative => Ok(v),
        _ => Err(invalid(format!(
            "{ctx}: '{key}' {w} out of range [0, {}]",
            u16::MAX
        ))),
    }
}

/// A required time window, whole microseconds the kernel reads from the
/// [`numeric_text`] of its cell through [`TimeBound::parse`]; a refusal of it
/// is located as [`get_rational`] locates one. Needs the GHC runtime up.
fn get_time_bound(row: &Row, key: &str, ctx: &str) -> Result<TimeBound, Error> {
    TimeBound::parse(numeric_text(row, key, ctx)?).map_err(|e| e.located(ctx, key))
}

/// A required boolean field. Accepts a native boolean, an integral `1`/`0`, or
/// the strings `TRUE`/`FALSE` (case-insensitive). A `1`/`0` written as a number
/// cell arrives as a lossy double and is rejected (the all-text contract); use a
/// native boolean or a text `TRUE`/`FALSE`/`1`/`0`.
fn get_bool(row: &Row, key: &str, ctx: &str) -> Result<bool, Error> {
    match row.get(key) {
        Some(Data::Bool(b)) => Ok(*b),
        Some(Data::Int(1)) => Ok(true),
        Some(Data::Int(0)) => Ok(false),
        Some(Data::String(s)) => match s.trim().to_ascii_uppercase().as_str() {
            "TRUE" | "1" => Ok(true),
            "FALSE" | "0" => Ok(false),
            _ => Err(invalid(format!(
                "{ctx}: '{key}' must be TRUE or FALSE, got {s:?}"
            ))),
        },
        Some(other) => Err(invalid(format!(
            "{ctx}: '{key}' must be TRUE or FALSE, got {}",
            describe(other)
        ))),
        None => Err(invalid(format!(
            "{ctx}: missing required '{key}' (expected TRUE or FALSE)"
        ))),
    }
}

/// A short human description of a cell's kind, for strict-rejection messages.
fn describe(d: &Data) -> String {
    match d {
        Data::String(s) => format!("text {s:?}"),
        Data::Int(n) => format!("the number {n}"),
        Data::Float(f) => format!("the number {f}"),
        Data::Bool(b) => format!("the boolean {b}"),
        Data::Empty => "an empty cell".to_string(),
        other => format!("{other:?}"),
    }
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Load signal checks from an Excel workbook.
///
/// Reads the `Checks` and `When-Then` sheets (either or both may be present) and
/// compiles each row through the [`check`] DSL into a [`Check`].
///
/// # Errors
/// [`Error::Validation`] if the path is a symlink / non-regular file, the file or
/// its uncompressed contents exceed the 64 MiB bound, the workbook has neither
/// sheet, or a row is malformed (unknown condition, missing/ill-typed cell, a
/// number the kernel's decimal grammar refuses, carrying the kernel's `code`);
/// [`Error::InputBoundExceeded`] if a number crosses the rational component
/// magnitude bound. Both number refusals are [`Rational::from_decimal`]'s, or
/// [`TimeBound::parse`]'s for a time window, with the kernel's message, code
/// and fields, located (see [`Error::located`]) at `Row <n>` under the column
/// header. A check the kernel refuses where it is built keeps the builder's
/// error, located at `Row <n>` with no key (see [`Error::located_at`]);
/// [`Error::RtsNotInitialized`] if the runtime has not started
/// ([`aletheia::start_runtime`] or a client starts it).
pub fn load_checks_from_excel(path: impl AsRef<Path>) -> Result<Vec<Check>, Error> {
    load_checks_within(path.as_ref(), MAX_INPUT_BYTES)
}

fn load_checks_within(path: &Path, limit: u64) -> Result<Vec<Check>, Error> {
    harden_path(path, limit)?;
    let mut wb: Xlsx<_> =
        open_workbook(path).map_err(|e| invalid(format!("cannot open {}: {e}", path.display())))?;
    let names = wb.sheet_names();
    let has_checks = names.iter().any(|n| n == CHECKS_SHEET);
    let has_when_then = names.iter().any(|n| n == WHEN_THEN_SHEET);
    if !has_checks && !has_when_then {
        return Err(invalid(format!(
            "workbook has no '{CHECKS_SHEET}' or '{WHEN_THEN_SHEET}' sheet"
        )));
    }
    let mut results = Vec::new();
    if has_checks {
        let range = sheet_range(&mut wb, CHECKS_SHEET)?;
        for (n, row) in rows_to_maps(&range) {
            if row.is_empty() {
                continue;
            }
            results.push(parse_simple_row(&row, n).map_err(|e| locate_row(e, n))?);
        }
    }
    if has_when_then {
        let range = sheet_range(&mut wb, WHEN_THEN_SHEET)?;
        for (n, row) in rows_to_maps(&range) {
            if row.is_empty() {
                continue;
            }
            results.push(parse_when_then_row(&row, n).map_err(|e| locate_row(e, n))?);
        }
    }
    Ok(results)
}

/// Load a typed [`Dbc`] document from the `DBC` sheet of an Excel workbook.
///
/// Rows are grouped into messages by `(Message ID, Message Name, Extended, DLC)`
/// in first-seen order; each row contributes one signal. Tier-2 metadata
/// (nodes, value tables, comments, attributes, …) is empty — the spreadsheet
/// layout carries only messages and signals, exactly like the peer loaders.
///
/// # Errors
/// The errors of [`load_checks_from_excel`], under the same conditions, plus
/// [`Error::Validation`] for a missing `DBC` sheet, no data rows, a fractional
/// whole-number field, a `Start Bit` or `Length` past 16 bits, a negative
/// `Multiplex Value`, or an out-of-range CAN id / DLC.
pub fn load_dbc_from_excel(path: impl AsRef<Path>) -> Result<Dbc, Error> {
    load_dbc_within(path.as_ref(), MAX_INPUT_BYTES)
}

fn load_dbc_within(path: &Path, limit: u64) -> Result<Dbc, Error> {
    harden_path(path, limit)?;
    let mut wb: Xlsx<_> =
        open_workbook(path).map_err(|e| invalid(format!("cannot open {}: {e}", path.display())))?;
    if !wb.sheet_names().iter().any(|n| n == DBC_SHEET) {
        return Err(invalid(format!("workbook has no '{DBC_SHEET}' sheet")));
    }
    let range = sheet_range(&mut wb, DBC_SHEET)?;
    let data: Vec<(usize, Row)> = rows_to_maps(&range)
        .into_iter()
        .filter(|(_, r)| !r.is_empty())
        .collect();
    if data.is_empty() {
        return Err(invalid("DBC sheet has no data rows"));
    }
    parse_dbc_rows(&data)
}

/// Create a blank Excel template (`DBC`, `Checks`, `When-Then` sheets, each with
/// a bold header row). Does not overwrite an existing file.
///
/// # Errors
/// [`Error::Validation`] if the file already exists, its parent directory does
/// not exist, or the workbook cannot be written.
pub fn create_template(path: impl AsRef<Path>) -> Result<(), Error> {
    let path = path.as_ref();
    if path.exists() {
        return Err(invalid(format!("file already exists: {}", path.display())));
    }
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() && !parent.is_dir() {
            return Err(invalid(format!(
                "parent directory does not exist: {}",
                parent.display()
            )));
        }
    }
    let mut wb = Workbook::new();
    let bold = Format::new().set_bold();
    write_template_sheet(&mut wb, DBC_SHEET, &DBC_HEADERS, &bold)?;
    write_template_sheet(&mut wb, CHECKS_SHEET, &CHECKS_HEADERS, &bold)?;
    write_template_sheet(&mut wb, WHEN_THEN_SHEET, &WHEN_THEN_HEADERS, &bold)?;
    wb.save(path)
        .map_err(|e| invalid(format!("cannot write {}: {e}", path.display())))?;
    Ok(())
}

fn write_template_sheet(
    wb: &mut Workbook,
    name: &str,
    headers: &[&str],
    bold: &Format,
) -> Result<(), Error> {
    let ws = wb.add_worksheet();
    ws.set_name(name)
        .map_err(|e| invalid(format!("cannot name sheet {name}: {e}")))?;
    for (col, h) in headers.iter().enumerate() {
        let col = u16::try_from(col).map_err(|_| invalid("too many columns"))?;
        ws.write_string_with_format(0, col, *h, bold)
            .map_err(|e| invalid(format!("cannot write header {h}: {e}")))?;
    }
    Ok(())
}

/// Resolve a worksheet's cell range, normalising calamine's error shape.
fn sheet_range(
    wb: &mut Xlsx<impl std::io::Read + std::io::Seek>,
    name: &str,
) -> Result<Range<Data>, Error> {
    wb.worksheet_range(name)
        .map_err(|e| invalid(format!("cannot read sheet '{name}': {e}")))
}

// ── Check-row parsers (mirror Python `excel_loader` / C++ `excel.cpp`) ─────────

fn parse_simple_row(row: &Row, n: usize) -> Result<Check, Error> {
    let ctx = format!("Row {n}");
    let signal = get_str(row, "Signal", &ctx)?;
    let condition = get_str(row, "Condition", &ctx)?;
    let sig = check::signal(signal);
    let check = match condition.as_str() {
        "never_exceeds" => sig.never_exceeds(get_rational(row, "Value", &ctx)?)?,
        "never_below" => sig.never_below(get_rational(row, "Value", &ctx)?)?,
        "never_equals" => sig.never_equals(get_rational(row, "Value", &ctx)?)?,
        "equals" => sig.equals(get_rational(row, "Value", &ctx)?).always()?,
        "stays_between" => {
            let (lo, hi) = simple_range(row, &ctx, &condition)?;
            sig.stays_between(lo, hi)?
        }
        "settles_between" => {
            let (lo, hi) = simple_range(row, &ctx, &condition)?;
            if !row.contains_key("Time (µs)") {
                return Err(invalid(format!(
                    "{ctx}: condition 'settles_between' requires 'Time (µs)'"
                )));
            }
            let bound = get_time_bound(row, "Time (µs)", &ctx)?;
            sig.settles_between(lo, hi).within(bound)?
        }
        other => return Err(invalid(format!("{ctx}: unknown condition '{other}'"))),
    };
    Ok(apply_metadata(check, row))
}

fn parse_when_then_row(row: &Row, n: usize) -> Result<Check, Error> {
    let ctx = format!("Row {n}");
    let when_signal = get_str(row, "When Signal", &ctx)?;
    let when_cond = get_str(row, "When Condition", &ctx)?;
    let when = check::when(when_signal);
    let when_condition = match when_cond.as_str() {
        "exceeds" => when.exceeds(get_rational(row, "When Value", &ctx)?),
        "equals" => when.equals(get_rational(row, "When Value", &ctx)?),
        "drops_below" => when.drops_below(get_rational(row, "When Value", &ctx)?),
        other => return Err(invalid(format!("{ctx}: unknown when condition '{other}'"))),
    };

    let then_signal = get_str(row, "Then Signal", &ctx)?;
    let then_cond = get_str(row, "Then Condition", &ctx)?;
    let response = when_condition.then(then_signal);
    let bound = get_time_bound(row, "Within (µs)", &ctx)?;
    let then_condition = match then_cond.as_str() {
        "equals" => response.equals(get_rational(row, "Then Value", &ctx)?),
        "exceeds" => response.exceeds(get_rational(row, "Then Value", &ctx)?),
        "stays_between" => {
            if !row.contains_key("Then Min") || !row.contains_key("Then Max") {
                return Err(invalid(format!(
                    "{ctx}: then condition 'stays_between' requires 'Then Min' and 'Then Max'"
                )));
            }
            response.stays_between(
                get_rational(row, "Then Min", &ctx)?,
                get_rational(row, "Then Max", &ctx)?,
            )
        }
        other => return Err(invalid(format!("{ctx}: unknown then condition '{other}'"))),
    };
    let check = then_condition.within(bound)?;
    Ok(apply_metadata(check, row))
}

/// Both `Min` and `Max` must be present for a range condition.
fn simple_range(row: &Row, ctx: &str, cond: &str) -> Result<(Rational, Rational), Error> {
    if !row.contains_key("Min") || !row.contains_key("Max") {
        return Err(invalid(format!(
            "{ctx}: condition '{cond}' requires 'Min' and 'Max'"
        )));
    }
    Ok((
        get_rational(row, "Min", ctx)?,
        get_rational(row, "Max", ctx)?,
    ))
}

/// A refusal no single column holds, such as a check its builder refused,
/// located at the row with no key: a refusal carrying the kernel's code, or a
/// bound refusal, that no reader located gains `Row <n>`; one a reader located,
/// or one without a code (the loader's own words, the runtime down), comes
/// back as it was.
fn locate_row(err: Error, n: usize) -> Error {
    let coded = matches!(
        &err,
        Error::Validation { code: Some(_), .. } | Error::InputBoundExceeded(_)
    );
    if coded && err.location().is_none() {
        err.located_at(format!("Row {n}"))
    } else {
        err
    }
}

/// Apply optional `Check Name` / `Severity` metadata (only when present and text).
fn apply_metadata(mut check: Check, row: &Row) -> Check {
    if let Some(Data::String(name)) = row.get("Check Name") {
        if !name.trim().is_empty() {
            check = check.named(name.clone());
        }
    }
    if let Some(Data::String(sev)) = row.get("Severity") {
        if !sev.trim().is_empty() {
            check = check.with_severity(sev.clone());
        }
    }
    check
}

// ── DBC-row parser ────────────────────────────────────────────────────────────

/// The row-level identity of a message: rows sharing this key are one message.
/// The DLC is kept as written, and held to a code when the message is built.
#[derive(Clone, PartialEq, Eq, Hash)]
struct MessageKey {
    id: u32,
    name: String,
    extended: bool,
    dlc: SignMagnitude,
}

fn parse_dbc_rows(data: &[(usize, Row)]) -> Result<Dbc, Error> {
    // Group by message key, preserving first-seen order.
    let mut order: Vec<MessageKey> = Vec::new();
    let mut groups: HashMap<MessageKey, Vec<usize>> = HashMap::new();
    for (idx, (n, row)) in data.iter().enumerate() {
        let ctx = format!("Row {n}");
        let key = MessageKey {
            id: parse_message_id(row, &ctx)?,
            name: get_str(row, "Message Name", &ctx)?,
            // `Extended` is optional — an absent column defaults to standard.
            extended: if row.contains_key("Extended") {
                get_bool(row, "Extended", &ctx)?
            } else {
                false
            },
            dlc: get_whole(row, "DLC", &ctx)?,
        };
        if !groups.contains_key(&key) {
            order.push(key.clone());
        }
        groups.entry(key).or_default().push(idx);
    }

    let mut messages = Vec::with_capacity(order.len());
    for key in order {
        let mut signals = Vec::new();
        for &idx in &groups[&key] {
            let (n, row) = &data[idx];
            signals.push(parse_dbc_signal(row, &format!("Row {n}"))?);
        }
        // Validate the CAN id against its declared width (delegates the range to
        // the typed CanId constructor; the rest of the semantic validation is
        // delegated to the verified core at parse_dbc time).
        validate_can_id(key.id, key.extended)?;
        let dlc = dlc_code(key.dlc)?;
        messages.push(DbcMessage {
            id: key.id,
            extended: key.extended,
            name: key.name,
            dlc: u32::from(dlc.value()),
            sender: String::new(),
            senders: Vec::new(),
            signals,
        });
    }

    Ok(Dbc {
        version: String::new(),
        messages,
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    })
}

/// `Message ID` is the one numeric field that also accepts text — a hex string
/// (`0x100`) or a decimal string — so it bypasses the strict number path.
fn parse_message_id(row: &Row, ctx: &str) -> Result<u32, Error> {
    let bad = || {
        invalid(format!(
            "{ctx}: invalid 'Message ID' — expected an integer or hex string (e.g. 0x100)"
        ))
    };
    let raw: i64 = match row.get("Message ID") {
        Some(Data::Int(n)) => *n,
        // A number cell stores a lossy double (the all-text contract); a Message
        // ID must be a text-formatted decimal or `0x`-hex value, so a number cell
        // falls through to `bad()` below.
        Some(Data::String(s)) => {
            let t = s.trim();
            let parsed = t
                .strip_prefix("0x")
                .or_else(|| t.strip_prefix("0X"))
                .map_or_else(|| t.parse::<i64>(), |hex| i64::from_str_radix(hex, 16));
            parsed.map_err(|_| bad())?
        }
        _ => return Err(bad()),
    };
    u32::try_from(raw).map_err(|_| {
        invalid(format!(
            "{ctx}: 'Message ID' {raw} is out of range for a CAN identifier"
        ))
    })
}

/// The DLC code a message's `DLC` cell writes: a value past a byte is refused
/// here, and [`Dlc::new`] refuses the rest.
fn dlc_code(dlc: SignMagnitude) -> Result<Dlc, Error> {
    match u8::try_from(dlc.magnitude) {
        Ok(code) if !dlc.negative => Dlc::new(code),
        _ => Err(invalid(format!("DLC {dlc} out of range"))),
    }
}

fn validate_can_id(id: u32, extended: bool) -> Result<(), Error> {
    if extended {
        CanId::extended(id).map(|_| ())
    } else {
        u16::try_from(id)
            .map_err(|_| invalid(format!("standard CAN id {id} out of 11-bit range")))
            .and_then(CanId::standard)
            .map(|_| ())
    }
}

fn parse_dbc_signal(row: &Row, ctx: &str) -> Result<DbcSignal, Error> {
    let name = get_str(row, "Signal", ctx)?;

    // The kernel decides a start bit's and a length's range when it reads the
    // definition; only a value their 16-bit fields cannot hold is refused here.
    let start_bit = u32::from(get_u16(row, "Start Bit", ctx)?);
    let length = u32::from(get_u16(row, "Length", ctx)?);

    let byte_order = match get_str(row, "Byte Order", ctx)?.as_str() {
        "little_endian" => ByteOrder::LittleEndian,
        "big_endian" => ByteOrder::BigEndian,
        other => {
            return Err(invalid(format!(
                "{ctx}: 'Byte Order' must be 'little_endian' or 'big_endian', got {other:?}"
            )))
        }
    };
    let signed = get_bool(row, "Signed", ctx)?;
    let factor = get_rational(row, "Factor", ctx)?;
    let offset = get_rational(row, "Offset", ctx)?;
    let minimum = get_rational(row, "Min", ctx)?;
    let maximum = get_rational(row, "Max", ctx)?;
    // `Unit` is optional, defaulting to empty.
    let unit = row
        .get("Unit")
        .and_then(|d| match d {
            Data::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    // Multiplexing: the pair must be both-present or both-absent.
    let has_muxor = row.contains_key("Multiplexor");
    let has_mux_val = row.contains_key("Multiplex Value");
    if has_muxor != has_mux_val {
        return Err(invalid(format!(
            "{ctx}: 'Multiplexor' and 'Multiplex Value' must both be provided or both be empty"
        )));
    }
    let presence = if has_muxor {
        let multiplexor = get_str(row, "Multiplexor", ctx)?;
        // A multiplex value has no sign, so a negative one, which the kernel
        // would refuse, is refused here; the kernel decides the rest.
        let mux_val = get_whole(row, "Multiplex Value", ctx)?;
        if mux_val.negative {
            return Err(invalid(format!(
                "{ctx}: 'Multiplex Value' must be non-negative, got {mux_val}"
            )));
        }
        Presence::Multiplexed {
            multiplexor,
            values: vec![mux_val.magnitude],
        }
    } else {
        Presence::Always
    };

    Ok(DbcSignal {
        name,
        start_bit,
        length,
        byte_order,
        signed,
        factor,
        offset,
        minimum,
        maximum,
        unit,
        receivers: Vec::new(),
        value_descriptions: Vec::new(),
        presence,
    })
}

// ── Trust-boundary hardening (mirror the YAML loader + Go `hardening.go`) ──────

fn harden_path(path: &Path, limit: u64) -> Result<(), Error> {
    let meta = std::fs::symlink_metadata(path)
        .map_err(|e| invalid(format!("cannot stat {}: {e}", path.display())))?;
    let ft = meta.file_type();
    if ft.is_symlink() {
        return Err(invalid(format!(
            "refusing to load {}: symbolic link (resolve the link and pass the real path)",
            path.display()
        )));
    }
    if !ft.is_file() {
        return Err(invalid(format!(
            "refusing to load {}: not a regular file",
            path.display()
        )));
    }
    if meta.len() > limit {
        return Err(invalid(format!(
            "Excel file {} exceeds the {limit}-byte input bound ({} bytes)",
            path.display(),
            meta.len()
        )));
    }
    check_uncompressed_bound(path, limit)
}

/// Walk the `.xlsx` ZIP central directory and reject when the sum of
/// uncompressed entry sizes exceeds the bound — a ZIP-bomb guard for the reader,
/// which all-loads the workbook. Saturating add refuses to wrap on a forged
/// entry. Mirrors Go `checkXlsxUncompressedBound` / Python
/// `_check_xlsx_uncompressed_bound`.
fn check_uncompressed_bound(path: &Path, limit: u64) -> Result<(), Error> {
    let file = std::fs::File::open(path)
        .map_err(|e| invalid(format!("cannot open {}: {e}", path.display())))?;
    let mut archive = zip::ZipArchive::new(file).map_err(|_| {
        invalid(format!(
            "{}: not a valid .xlsx (ZIP) archive",
            path.display()
        ))
    })?;
    let mut total: u64 = 0;
    for i in 0..archive.len() {
        let entry = archive
            .by_index(i)
            .map_err(|e| invalid(format!("{}: corrupt ZIP entry: {e}", path.display())))?;
        total = total.saturating_add(entry.size());
        if total > limit {
            return Err(invalid(format!(
                "{}: uncompressed contents exceed the {limit}-byte input bound",
                path.display()
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
