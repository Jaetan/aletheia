// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

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

/// Bring the GHC RTS up for a loader test. The typed cell accessors
/// parse every numeric field through the kernel decimal SSOT
/// (`Rational::from_decimal`), which is RTS-gated — so any test that loads a
/// sheet with a numeric field needs a live backend first. `aletheia::Client`
/// is the sole RTS initialiser; the process-global one-shot latch keeps the
/// RTS up for the rest of the run, so any one call suffices for all tests.
fn test_backend() -> aletheia::Client {
    aletheia::Client::new().expect(
        "init GHC RTS for excel loader test (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)",
    )
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
    let _rts = test_backend();
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
                    Cell::Str("220"),
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
                    Cell::Str("11.5"),
                    Cell::Str("14.5"),
                    Cell::Empty,
                    Cell::Str("warning"),
                ],
                &[
                    Cell::Str("Coolant"),
                    Cell::Str("CoolantTemp"),
                    Cell::Str("settles_between"),
                    Cell::Empty,
                    Cell::Str("80"),
                    Cell::Str("100"),
                    Cell::Str("5000"),
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
            .stays_between(Rational::new(23, 2).unwrap(), Rational::new(29, 2).unwrap())
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
    let _rts = test_backend();
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
                Cell::Str("50"),
                Cell::Str("BrakeLight"),
                Cell::Str("equals"),
                Cell::Str("1"),
                Cell::Empty,
                Cell::Empty,
                Cell::Str("100"),
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
    let _rts = test_backend();
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
                    Cell::Str("8"),
                    Cell::Str("EngineSpeed"),
                    Cell::Str("0"),
                    Cell::Str("16"),
                    Cell::Str("little_endian"),
                    Cell::Bool(false),
                    Cell::Str("0.25"),
                    Cell::Str("0"),
                    Cell::Str("0"),
                    Cell::Str("8000"),
                    Cell::Str("rpm"),
                    Cell::Empty,
                    Cell::Empty,
                ],
                &[
                    Cell::Str("0x100"),
                    Cell::Str("EngineData"),
                    Cell::Bool(false),
                    Cell::Str("8"),
                    Cell::Str("EngineTemp"),
                    Cell::Str("16"),
                    Cell::Str("8"),
                    Cell::Str("little_endian"),
                    Cell::Bool(true),
                    Cell::Str("1"),
                    Cell::Str("-40"),
                    Cell::Str("-40"),
                    Cell::Str("215"),
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
    // "0.25" parses EXACTLY to 1/4 via the kernel decimal SSOT (from_decimal).
    assert_eq!(s.factor, Rational::new(1, 4).unwrap());
    assert_eq!(s.unit, "rpm");
    assert_eq!(s.presence, Presence::Always);
    assert!(m.signals[1].signed);
}

#[test]
fn extended_column_is_optional() {
    // A 13-column sheet that omits Extended / mux columns (the demo shape)
    // loads — the absent Extended column behaves like an empty cell → standard.
    let _rts = test_backend();
    let path = temp("noext");
    let _g = TempXlsx(path.clone());
    write_book(
        &path,
        &[(
            "DBC",
            DBC_HDR_MINIMAL,
            &[&[
                Cell::Str("512"),
                Cell::Str("BrakeStatus"),
                Cell::Str("8"),
                Cell::Str("BrakePressure"),
                Cell::Str("0"),
                Cell::Str("16"),
                Cell::Str("little_endian"),
                Cell::Bool(false),
                Cell::Str("0.1"),
                Cell::Str("0"),
                Cell::Str("0"),
                Cell::Str("6553.5"),
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
fn strict_rejects_a_number_cell() {
    // THE LOCK for the all-text decimal contract: a numeric field stored
    // as a NUMBER cell holds a lossy IEEE-754 double, so it is rejected — the
    // exact value survives only when the cell is TEXT-formatted (parsed by the
    // kernel `from_decimal`). The generated template stores numbers as text for
    // exactly this reason. Needs a live backend (decimal parsing is RTS-gated).
    let _rts = test_backend();
    let cpath = temp("num_check");
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
                Cell::Num(220.0), // number cell — must be TEXT
                Cell::Empty,
                Cell::Empty,
                Cell::Empty,
                Cell::Empty,
            ]],
        )],
    );
    let err = load_checks_from_excel(&cpath).unwrap_err();
    assert!(format!("{err}").contains("format it as TEXT"), "got: {err}");

    // A DBC Factor stored as a number cell is likewise rejected.
    let dpath = temp("num_dbc");
    let _gd = TempXlsx(dpath.clone());
    write_book(
        &dpath,
        &[(
            "DBC",
            DBC_HDR_MINIMAL,
            &[&[
                Cell::Str("256"),
                Cell::Str("M"),
                Cell::Str("8"),
                Cell::Str("Sig"),
                Cell::Str("0"),
                Cell::Str("8"),
                Cell::Str("little_endian"),
                Cell::Bool(false),
                Cell::Num(0.25), // Factor as a number cell — must be TEXT
                Cell::Str("0"),
                Cell::Str("0"),
                Cell::Str("1"),
                Cell::Empty,
            ]],
        )],
    );
    let err = load_dbc_from_excel(&dpath).unwrap_err();
    assert!(format!("{err}").contains("format it as TEXT"), "got: {err}");
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
    let link = std::env::temp_dir().join(format!("aletheia_excel_{}_sym.xlsx", std::process::id()));
    let _gt = TempXlsx(target.clone());
    let _gl = TempXlsx(link.clone());
    write_book(&target, &[("Checks", CHECKS_HDR, &[])]);
    if std::os::unix::fs::symlink(&target, &link).is_err() {
        return; // symlink creation not permitted — skip (mirrors the Go test)
    }
    let err = load_checks_from_excel(&link).unwrap_err();
    assert!(format!("{err}").contains("symbolic link"), "got: {err}");
}

#[test]
fn stat_failure_surfaces_errno_not_missing() {
    // A path component over NAME_MAX makes symlink_metadata (lstat) fail
    // with ENAMETOOLONG — a stat *failure*, not an absent file. The loader
    // embeds the raw io::Error ("cannot stat …: <errno>"), so a
    // resource/permission failure under load can never be mislabelled a
    // missing file (the cross-binding ec-vs-not-found invariant; cf. the
    // C++ validate_loader_path split and Go's os.ErrNotExist branch).
    // ENAMETOOLONG is deterministic and root-safe.
    let long = std::env::temp_dir().join("a".repeat(5000));
    let err = load_checks_from_excel(&long).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("cannot stat"), "got: {msg}");
    assert!(
        !msg.contains("No such file"),
        "stat failure mislabelled as a missing file: {msg}"
    );
}
