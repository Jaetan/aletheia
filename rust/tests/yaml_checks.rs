// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#![cfg(feature = "yaml")]

//! Cross-binding portability test for the YAML check loader (Slice R3b): the
//! Rust loader must accept the *same* check file the Go and Python loaders do and
//! compile it to the same formulas. The fixture's decimal operands are
//! parsed via the kernel decimal SSOT (`Rational::from_decimal`), which is
//! RTS-gated — so this test brings up a backend (`Client::new`) first, then loads.

use aletheia::{check, load_checks_from_yaml, Client, Rational};

/// The exact fixture the Go doc-example tests load
/// (`go/aletheia/testdata/doc_examples/checks.yaml`) — proving a check file is
/// portable across bindings, not just schema-compatible in the abstract.
const SHARED_FIXTURE: &str = include_str!("../../go/aletheia/testdata/doc_examples/checks.yaml");

#[test]
fn loads_the_shared_cross_binding_fixture() {
    // The fixture's `stays_between 11.5 14.5` operands are decimals parsed via the
    // kernel decimal SSOT (`Rational::from_decimal`) — RTS-gated, so a backend
    // must exist first.
    let _rts =
        Client::new().expect("init GHC RTS (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)");
    let checks = load_checks_from_yaml(SHARED_FIXTURE).expect("load shared fixture");
    assert_eq!(checks.len(), 2);

    // First check: Speed never_exceeds 220 (integer scalar → 220/1).
    assert_eq!(
        checks[0].formula(),
        check::signal("Speed").never_exceeds(220).formula()
    );
    assert_eq!(checks[0].signal_name(), "Speed");

    // Second check: Voltage stays_between 11.5 and 14.5 — the decimals parse
    // EXACTLY to 23/2 and 29/2, the same Rationals every binding produces.
    let voltage = check::signal("Voltage")
        .stays_between(Rational::new(23, 2).unwrap(), Rational::new(29, 2).unwrap())
        .unwrap();
    assert_eq!(checks[1].formula(), voltage.formula());
}
