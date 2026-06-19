// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Aletheia Excel check + DBC loader (slice R3c).
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
//! Coercion is **strict**, matching the Python reference (`openpyxl`, typed
//! cells) and the typed substrate calamine gives us: a numeric field requires a
//! real number cell, so a number stored as *text* (`"8"`) is rejected rather
//! than silently parsed. The one exception is `Message ID`, which legitimately
//! takes a hex string (`0x100`). The compiled formulas and the typed [`Dbc`]
//! delegate every value to the verified core via the main `aletheia` crate.

use std::collections::HashMap;
use std::path::Path;

use calamine::{open_workbook, Data, Range, Reader, Xlsx};
use rust_xlsxwriter::{Format, Workbook};

use aletheia::check::{self, Check};
use aletheia::{ByteOrder, CanId, Dbc, DbcMessage, DbcSignal, Error, Presence, Rational};

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
    "Time (ms)",
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
    "Within (ms)",
    "Severity",
];

fn invalid(msg: impl Into<String>) -> Error {
    Error::Validation(msg.into())
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

/// A required numeric field as an exact [`Rational`] (an integer becomes `n/1`, a
/// decimal goes through the shared [`Rational::from_f64`] convention).
fn get_rational(row: &Row, key: &str, ctx: &str) -> Result<Rational, Error> {
    match row.get(key) {
        Some(Data::Int(n)) => Ok(Rational::integer(*n)),
        Some(Data::Float(f)) => Rational::from_f64(*f),
        Some(other) => Err(invalid(format!(
            "{ctx}: '{key}' must be a number, got {}; format the cell as a number",
            describe(other)
        ))),
        None => Err(invalid(format!(
            "{ctx}: missing required '{key}' (expected a number)"
        ))),
    }
}

/// A required whole-number field. xlsx stores every number as a double, so an
/// *integral* float (`8.0`) is accepted and a fractional one is rejected —
/// matching Python's effective behaviour (openpyxl normalises whole floats to
/// `int` before its `int`-only check).
fn get_int(row: &Row, key: &str, ctx: &str) -> Result<i64, Error> {
    match row.get(key) {
        Some(Data::Int(n)) => Ok(*n),
        Some(Data::Float(f))
            if f.fract() == 0.0 && *f >= i64::MIN as f64 && *f <= i64::MAX as f64 =>
        {
            Ok(*f as i64)
        }
        Some(Data::Float(_)) => Err(invalid(format!("{ctx}: '{key}' must be a whole number"))),
        Some(other) => Err(invalid(format!(
            "{ctx}: '{key}' must be a whole number, got {}; format the cell as a number",
            describe(other)
        ))),
        None => Err(invalid(format!(
            "{ctx}: missing required '{key}' (expected a whole number)"
        ))),
    }
}

/// A required non-negative whole-number millisecond field as `u64`.
fn get_u64_ms(row: &Row, key: &str, ctx: &str) -> Result<u64, Error> {
    let n = get_int(row, key, ctx)?;
    u64::try_from(n).map_err(|_| invalid(format!("{ctx}: '{key}' must be non-negative")))
}

/// A required boolean field. Accepts a native boolean, an integral `1`/`0`, or
/// the strings `TRUE`/`FALSE` (case-insensitive) — the multi-form set Python's
/// `get_bool` accepts.
fn get_bool(row: &Row, key: &str, ctx: &str) -> Result<bool, Error> {
    match row.get(key) {
        Some(Data::Bool(b)) => Ok(*b),
        Some(Data::Int(1)) => Ok(true),
        Some(Data::Int(0)) => Ok(false),
        Some(Data::Float(f)) if *f == 1.0 => Ok(true),
        Some(Data::Float(f)) if *f == 0.0 => Ok(false),
        Some(Data::String(s)) => match s.trim().to_ascii_uppercase().as_str() {
            "TRUE" => Ok(true),
            "FALSE" => Ok(false),
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
/// compiles each row through the [`check`](aletheia::check) DSL into a [`Check`].
///
/// # Errors
/// [`Error::Validation`] if the path is a symlink / non-regular file, the file or
/// its uncompressed contents exceed the 64 MiB bound, the workbook has neither
/// sheet, or a row is malformed (unknown condition, missing/ill-typed cell).
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
            results.push(parse_simple_row(&row, n)?);
        }
    }
    if has_when_then {
        let range = sheet_range(&mut wb, WHEN_THEN_SHEET)?;
        for (n, row) in rows_to_maps(&range) {
            if row.is_empty() {
                continue;
            }
            results.push(parse_when_then_row(&row, n)?);
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
/// [`Error::Validation`] under the same conditions as [`load_checks_from_excel`],
/// plus a missing `DBC` sheet, no data rows, or an out-of-range CAN id / DLC.
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
        "never_exceeds" => sig.never_exceeds(get_rational(row, "Value", &ctx)?),
        "never_below" => sig.never_below(get_rational(row, "Value", &ctx)?),
        "never_equals" => sig.never_equals(get_rational(row, "Value", &ctx)?),
        "equals" => sig.equals(get_rational(row, "Value", &ctx)?).always(),
        "stays_between" => {
            let (lo, hi) = simple_range(row, &ctx, &condition)?;
            sig.stays_between(lo, hi)?
        }
        "settles_between" => {
            let (lo, hi) = simple_range(row, &ctx, &condition)?;
            if !row.contains_key("Time (ms)") {
                return Err(invalid(format!(
                    "{ctx}: condition 'settles_between' requires 'Time (ms)'"
                )));
            }
            let ms = get_u64_ms(row, "Time (ms)", &ctx)?;
            sig.settles_between(lo, hi).within(ms)?
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
    let ms = get_u64_ms(row, "Within (ms)", &ctx)?;
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
    let check = then_condition.within(ms)?;
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
#[derive(Clone, PartialEq, Eq, Hash)]
struct MessageKey {
    id: u32,
    name: String,
    extended: bool,
    dlc: u32,
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
            dlc: parse_dlc(row, &ctx)?,
        };
        if !groups.contains_key(&key) {
            order.push(key.clone());
        }
        groups.entry(key).or_default().push(idx);
    }

    let mut messages = Vec::with_capacity(order.len());
    for key in order {
        // Validate the CAN id against its declared width (delegates the range to
        // the typed CanId constructor; the rest of the semantic validation is
        // delegated to the verified core at parse_dbc time).
        validate_can_id(key.id, key.extended)?;
        let mut signals = Vec::new();
        for &idx in &groups[&key] {
            let (n, row) = &data[idx];
            signals.push(parse_dbc_signal(row, &format!("Row {n}"))?);
        }
        messages.push(DbcMessage {
            id: key.id,
            extended: key.extended,
            name: key.name,
            dlc: key.dlc,
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
        // Range-check before the cast: `as i64` saturates an out-of-range float,
        // which would otherwise surface as a misleading "out of range" on the
        // saturated value rather than the real one (matches `get_int`).
        Some(Data::Float(f))
            if f.fract() == 0.0 && *f >= i64::MIN as f64 && *f <= i64::MAX as f64 =>
        {
            *f as i64
        }
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

fn parse_dlc(row: &Row, ctx: &str) -> Result<u32, Error> {
    let dlc = get_int(row, "DLC", ctx)?;
    if !(0..=15).contains(&dlc) {
        return Err(invalid(format!("{ctx}: 'DLC' {dlc} out of range [0, 15]")));
    }
    Ok(dlc as u32)
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
    let byte_order = match get_str(row, "Byte Order", ctx)?.as_str() {
        "little_endian" => ByteOrder::LittleEndian,
        "big_endian" => ByteOrder::BigEndian,
        other => {
            return Err(invalid(format!(
                "{ctx}: 'Byte Order' must be 'little_endian' or 'big_endian', got {other:?}"
            )))
        }
    };

    // Multiplexing: the pair must be both-present or both-absent.
    let has_muxor = row.contains_key("Multiplexor");
    let has_mux_val = row.contains_key("Multiplex Value");
    if has_muxor != has_mux_val {
        return Err(invalid(format!(
            "{ctx}: 'Multiplexor' and 'Multiplex Value' must both be provided or both be empty"
        )));
    }
    let presence = if has_muxor {
        let mux_val = get_int(row, "Multiplex Value", ctx)?;
        let value = u64::try_from(mux_val).map_err(|_| {
            invalid(format!(
                "{ctx}: 'Multiplex Value' must be non-negative, got {mux_val}"
            ))
        })?;
        Presence::Multiplexed {
            multiplexor: get_str(row, "Multiplexor", ctx)?,
            values: vec![value],
        }
    } else {
        Presence::Always
    };

    let start_bit = u32::try_from(get_int(row, "Start Bit", ctx)?)
        .map_err(|_| invalid(format!("{ctx}: 'Start Bit' must be non-negative")))?;
    let length = u32::try_from(get_int(row, "Length", ctx)?)
        .map_err(|_| invalid(format!("{ctx}: 'Length' must be non-negative")))?;

    Ok(DbcSignal {
        name: get_str(row, "Signal", ctx)?,
        start_bit,
        length,
        byte_order,
        signed: get_bool(row, "Signed", ctx)?,
        factor: get_rational(row, "Factor", ctx)?,
        offset: get_rational(row, "Offset", ctx)?,
        minimum: get_rational(row, "Min", ctx)?,
        maximum: get_rational(row, "Max", ctx)?,
        // `Unit` is optional, defaulting to empty.
        unit: row
            .get("Unit")
            .and_then(|d| match d {
                Data::String(s) => Some(s.clone()),
                _ => None,
            })
            .unwrap_or_default(),
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
mod tests {
    use super::*;
    use rust_xlsxwriter::Workbook;
    use std::path::PathBuf;

    /// A typed test cell — mirrors how a real Excel file (and the demo workbook)
    /// stores values: numbers as numbers, booleans as booleans, text as text.
    enum Cell {
        Num(f64),
        Bool(bool),
        Str(&'static str),
        Empty,
    }

    /// `(sheet name, header names, data rows)`.
    type SheetSpec<'a> = (&'a str, &'a [&'a str], &'a [&'a [Cell]]);

    fn write_book(path: &Path, sheets: &[SheetSpec]) {
        let mut wb = Workbook::new();
        for (name, headers, rows) in sheets {
            let ws = wb.add_worksheet();
            ws.set_name(*name).unwrap();
            for (c, h) in headers.iter().enumerate() {
                ws.write_string(0, c as u16, *h).unwrap();
            }
            for (r, row) in rows.iter().enumerate() {
                let rr = (r + 1) as u32;
                for (c, cell) in row.iter().enumerate() {
                    let cc = c as u16;
                    match cell {
                        Cell::Num(n) => {
                            ws.write_number(rr, cc, *n).unwrap();
                        }
                        Cell::Bool(b) => {
                            ws.write_boolean(rr, cc, *b).unwrap();
                        }
                        Cell::Str(s) => {
                            ws.write_string(rr, cc, *s).unwrap();
                        }
                        Cell::Empty => {}
                    }
                }
            }
        }
        wb.save(path).unwrap();
    }

    struct TempXlsx(PathBuf);
    impl Drop for TempXlsx {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    fn temp(tag: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        p.push(format!("aletheia_excel_{}_{tag}.xlsx", std::process::id()));
        p
    }

    const CHECKS_HDR: &[&str] = &CHECKS_HEADERS;
    const WT_HDR: &[&str] = &WHEN_THEN_HEADERS;
    const DBC_HDR: &[&str] = &DBC_HEADERS;
    // A 13-column DBC layout that omits Extended / mux columns (the demo shape).
    const DBC_HDR_MINIMAL: &[&str] = &[
        "Message ID",
        "Message Name",
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
    ];

    #[test]
    fn simple_checks_round_trip_to_the_builders() {
        let path = temp("checks");
        let _g = TempXlsx(path.clone());
        write_book(
            &path,
            &[(
                "Checks",
                CHECKS_HDR,
                &[
                    &[
                        Cell::Str("Speed limit"),
                        Cell::Str("VehicleSpeed"),
                        Cell::Str("never_exceeds"),
                        Cell::Num(220.0),
                        Cell::Empty,
                        Cell::Empty,
                        Cell::Empty,
                        Cell::Str("safety"),
                    ],
                    &[
                        Cell::Str("Battery range"),
                        Cell::Str("BatteryVoltage"),
                        Cell::Str("stays_between"),
                        Cell::Empty,
                        Cell::Num(11.5),
                        Cell::Num(14.5),
                        Cell::Empty,
                        Cell::Str("warning"),
                    ],
                    &[
                        Cell::Str("Coolant"),
                        Cell::Str("CoolantTemp"),
                        Cell::Str("settles_between"),
                        Cell::Empty,
                        Cell::Num(80.0),
                        Cell::Num(100.0),
                        Cell::Num(5000.0),
                        Cell::Str("info"),
                    ],
                ],
            )],
        );
        let checks = load_checks_from_excel(&path).expect("load");
        assert_eq!(checks.len(), 3);
        assert_eq!(
            checks[0].formula(),
            check::signal("VehicleSpeed").never_exceeds(220).formula()
        );
        assert_eq!(checks[0].name(), "Speed limit");
        assert_eq!(checks[0].severity(), "safety");
        assert_eq!(
            checks[1].formula(),
            check::signal("BatteryVoltage")
                .stays_between(
                    Rational::from_f64(11.5).unwrap(),
                    Rational::from_f64(14.5).unwrap()
                )
                .unwrap()
                .formula()
        );
        assert_eq!(
            checks[2].formula(),
            check::signal("CoolantTemp")
                .settles_between(80, 100)
                .within(5000)
                .unwrap()
                .formula()
        );
    }

    #[test]
    fn when_then_round_trips_to_the_builder() {
        let path = temp("wt");
        let _g = TempXlsx(path.clone());
        write_book(
            &path,
            &[(
                "When-Then",
                WT_HDR,
                &[&[
                    Cell::Str("Brake light"),
                    Cell::Str("BrakePedal"),
                    Cell::Str("exceeds"),
                    Cell::Num(50.0),
                    Cell::Str("BrakeLight"),
                    Cell::Str("equals"),
                    Cell::Num(1.0),
                    Cell::Empty,
                    Cell::Empty,
                    Cell::Num(100.0),
                    Cell::Str("safety"),
                ]],
            )],
        );
        let checks = load_checks_from_excel(&path).expect("load");
        assert_eq!(checks.len(), 1);
        assert_eq!(
            checks[0].formula(),
            check::when("BrakePedal")
                .exceeds(50)
                .then("BrakeLight")
                .equals(1)
                .within(100)
                .unwrap()
                .formula()
        );
        assert_eq!(checks[0].name(), "Brake light");
    }

    #[test]
    fn dbc_round_trips_with_typed_fields() {
        let path = temp("dbc");
        let _g = TempXlsx(path.clone());
        write_book(
            &path,
            &[(
                "DBC",
                DBC_HDR,
                &[
                    &[
                        Cell::Str("0x100"),
                        Cell::Str("EngineData"),
                        Cell::Bool(false),
                        Cell::Num(8.0),
                        Cell::Str("EngineSpeed"),
                        Cell::Num(0.0),
                        Cell::Num(16.0),
                        Cell::Str("little_endian"),
                        Cell::Bool(false),
                        Cell::Num(0.25),
                        Cell::Num(0.0),
                        Cell::Num(0.0),
                        Cell::Num(8000.0),
                        Cell::Str("rpm"),
                        Cell::Empty,
                        Cell::Empty,
                    ],
                    &[
                        Cell::Str("0x100"),
                        Cell::Str("EngineData"),
                        Cell::Bool(false),
                        Cell::Num(8.0),
                        Cell::Str("EngineTemp"),
                        Cell::Num(16.0),
                        Cell::Num(8.0),
                        Cell::Str("little_endian"),
                        Cell::Bool(true),
                        Cell::Num(1.0),
                        Cell::Num(-40.0),
                        Cell::Num(-40.0),
                        Cell::Num(215.0),
                        Cell::Str("C"),
                        Cell::Empty,
                        Cell::Empty,
                    ],
                ],
            )],
        );
        let dbc = load_dbc_from_excel(&path).expect("load");
        assert_eq!(dbc.messages.len(), 1);
        let m = &dbc.messages[0];
        assert_eq!((m.id, m.extended, m.dlc), (0x100, false, 8));
        assert_eq!(m.name, "EngineData");
        assert_eq!(m.signals.len(), 2);
        let s = &m.signals[0];
        assert_eq!(s.name, "EngineSpeed");
        assert_eq!((s.start_bit, s.length), (0, 16));
        assert_eq!(s.byte_order, ByteOrder::LittleEndian);
        assert!(!s.signed);
        // 0.25 must scale-and-reduce to exactly 1/4 via the shared convention.
        assert_eq!(s.factor, Rational::new(1, 4).unwrap());
        assert_eq!(s.unit, "rpm");
        assert_eq!(s.presence, Presence::Always);
        assert!(m.signals[1].signed);
    }

    #[test]
    fn extended_column_is_optional() {
        // A 13-column sheet that omits Extended / mux columns (the demo shape)
        // loads — the absent Extended column behaves like an empty cell → standard.
        let path = temp("noext");
        let _g = TempXlsx(path.clone());
        write_book(
            &path,
            &[(
                "DBC",
                DBC_HDR_MINIMAL,
                &[&[
                    Cell::Num(512.0),
                    Cell::Str("BrakeStatus"),
                    Cell::Num(8.0),
                    Cell::Str("BrakePressure"),
                    Cell::Num(0.0),
                    Cell::Num(16.0),
                    Cell::Str("little_endian"),
                    Cell::Bool(false),
                    Cell::Num(0.1),
                    Cell::Num(0.0),
                    Cell::Num(0.0),
                    Cell::Num(6553.5),
                    Cell::Str("bar"),
                ]],
            )],
        );
        let dbc = load_dbc_from_excel(&path).expect("load");
        assert_eq!(dbc.messages.len(), 1);
        assert!(!dbc.messages[0].extended);
        assert_eq!(dbc.messages[0].id, 512);
    }

    #[test]
    fn strict_rejects_a_number_stored_as_text() {
        // THE LOCK for the strict-coercion decision: a numeric field stored as
        // TEXT ("220" / "0.25") must be rejected, not silently parsed. The demo
        // workbook can't exercise this (it stores numbers natively).
        let cpath = temp("text_check");
        let _gc = TempXlsx(cpath.clone());
        write_book(
            &cpath,
            &[(
                "Checks",
                CHECKS_HDR,
                &[&[
                    Cell::Str("bad"),
                    Cell::Str("S"),
                    Cell::Str("never_exceeds"),
                    Cell::Str("220"), // number-as-TEXT
                    Cell::Empty,
                    Cell::Empty,
                    Cell::Empty,
                    Cell::Empty,
                ]],
            )],
        );
        let err = load_checks_from_excel(&cpath).unwrap_err();
        assert!(format!("{err}").contains("must be a number"), "got: {err}");

        let dpath = temp("text_dbc");
        let _gd = TempXlsx(dpath.clone());
        write_book(
            &dpath,
            &[(
                "DBC",
                DBC_HDR_MINIMAL,
                &[&[
                    Cell::Num(256.0),
                    Cell::Str("M"),
                    Cell::Num(8.0),
                    Cell::Str("Sig"),
                    Cell::Num(0.0),
                    Cell::Num(8.0),
                    Cell::Str("little_endian"),
                    Cell::Bool(false),
                    Cell::Str("0.25"), // Factor as number-as-TEXT
                    Cell::Num(0.0),
                    Cell::Num(0.0),
                    Cell::Num(1.0),
                    Cell::Empty,
                ]],
            )],
        );
        let err = load_dbc_from_excel(&dpath).unwrap_err();
        assert!(format!("{err}").contains("must be a number"), "got: {err}");
    }

    #[test]
    fn create_template_then_round_trip() {
        let path = temp("tmpl");
        let _g = TempXlsx(path.clone());
        let _ = std::fs::remove_file(&path);
        create_template(&path).expect("create");
        assert!(path.exists());
        // Header-only sheets: checks load to an empty set; the DBC sheet has no
        // data rows so loading a DBC is an error.
        assert!(load_checks_from_excel(&path)
            .expect("load checks")
            .is_empty());
        assert!(load_dbc_from_excel(&path).is_err());
        // No overwrite.
        assert!(create_template(&path).is_err());
    }

    #[test]
    fn workbook_without_either_check_sheet_errors() {
        let path = temp("nosheets");
        let _g = TempXlsx(path.clone());
        write_book(&path, &[("Other", &["A"], &[&[Cell::Str("x")]])]);
        assert!(load_checks_from_excel(&path).is_err());
    }

    // ── Trust-boundary hardening (parity with the YAML / Go / Python loaders) ──

    #[test]
    fn raw_size_bound_is_enforced() {
        let path = temp("size");
        let _g = TempXlsx(path.clone());
        write_book(&path, &[("Checks", CHECKS_HDR, &[])]);
        // A tiny injectable bound rejects before parsing; the real bound is 64 MiB.
        assert!(load_checks_within(&path, 16).is_err());
        assert!(load_checks_within(&path, MAX_INPUT_BYTES).is_ok());
    }

    #[test]
    fn uncompressed_bound_rejects_a_real_xlsx_under_a_tiny_limit() {
        let path = temp("zipbomb");
        let _g = TempXlsx(path.clone());
        write_book(&path, &[("Checks", CHECKS_HDR, &[])]);
        // A real .xlsx unzips to several KiB of XML — over a 10-byte bound.
        assert!(check_uncompressed_bound(&path, 10).is_err());
        assert!(check_uncompressed_bound(&path, MAX_INPUT_BYTES).is_ok());
    }

    #[test]
    fn rejects_non_regular_file() {
        let dir = std::env::temp_dir().join(format!("aletheia_excel_dir_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mkdir");
        let err = load_checks_from_excel(&dir).unwrap_err();
        let _ = std::fs::remove_dir(&dir);
        assert!(
            format!("{err}").contains("not a regular file"),
            "got: {err}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlink() {
        let target = temp("sym_target");
        let link =
            std::env::temp_dir().join(format!("aletheia_excel_{}_sym.xlsx", std::process::id()));
        let _gt = TempXlsx(target.clone());
        let _gl = TempXlsx(link.clone());
        write_book(&target, &[("Checks", CHECKS_HDR, &[])]);
        if std::os::unix::fs::symlink(&target, &link).is_err() {
            return; // symlink creation not permitted — skip (mirrors the Go test)
        }
        let err = load_checks_from_excel(&link).unwrap_err();
        assert!(format!("{err}").contains("symbolic link"), "got: {err}");
    }
}
