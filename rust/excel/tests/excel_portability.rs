// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Portability proof: the Rust loader reads the **shared** `demo_workbook.xlsx`
//! fixture — the same file the Python, Go, and C++ binding tests load — and
//! produces the same checks and DBC. This is the cross-binding lock for the
//! "absent `Extended` column ≡ standard message" contract: the fixture is a
//! 13-column DBC sheet that omits `Extended` / mux columns and stores numbers
//! natively, exactly as a real Excel file does.

use aletheia::{check, ByteOrder, Presence, Rational};
use aletheia_excel::{load_checks_from_excel, load_dbc_from_excel};

fn demo() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/demo/demo_workbook.xlsx")
}

#[test]
fn demo_workbook_checks_match_the_builders() {
    let checks = load_checks_from_excel(demo()).expect("load checks from demo workbook");
    // 6 simple checks (Checks sheet) + 3 causal checks (When-Then sheet).
    assert_eq!(
        checks.len(),
        9,
        "demo workbook has 6 simple + 3 when/then checks"
    );

    // checks[0] is the first Checks-sheet row; checks[6] the first When-Then row.
    assert_eq!(
        checks[0].formula(),
        check::signal("VehicleSpeed").never_exceeds(220).formula()
    );
    assert_eq!(checks[0].name(), "Speed limit");
    assert_eq!(checks[0].severity(), "safety");

    assert_eq!(
        checks[6].formula(),
        check::when("BrakePedal")
            .exceeds(50)
            .then("BrakeLight")
            .equals(1)
            .within(100)
            .unwrap()
            .formula()
    );
    assert_eq!(checks[6].name(), "Brake light");
}

#[test]
fn demo_workbook_dbc_loads_as_standard_messages() {
    let dbc = load_dbc_from_excel(demo()).expect("load DBC from demo workbook");
    assert_eq!(dbc.messages.len(), 2, "EngineData + BrakeStatus");

    let engine = dbc
        .message_by_name("EngineData")
        .expect("EngineData message");
    // 0x100 = 256; the sheet omits Extended → standard (the contract under test).
    assert_eq!(engine.id, 0x100);
    assert!(
        !engine.extended,
        "absent Extended column ⇒ standard message"
    );
    assert_eq!(engine.dlc, 8);
    assert_eq!(engine.signals.len(), 2);

    let speed = engine.signal_by_name("EngineSpeed").expect("EngineSpeed");
    // Factor 0.25 must scale-and-reduce to exactly 1/4 via the shared convention.
    assert_eq!(speed.factor, Rational::new(1, 4).unwrap());
    assert_eq!(speed.byte_order, ByteOrder::LittleEndian);
    assert_eq!(speed.presence, Presence::Always);
    assert_eq!(speed.unit, "rpm");

    let brake = dbc
        .message_by_name("BrakeStatus")
        .expect("BrakeStatus message");
    assert_eq!(brake.id, 512);
    assert!(!brake.extended);
}
