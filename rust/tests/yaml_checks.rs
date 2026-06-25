// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#![cfg(feature = "yaml")]

//! Cross-binding portability test for the YAML check loader (Slice R3b): the
//! Rust loader must accept the *same* check file the Go and Python loaders do and
//! compile it to the same formulas. No `libaletheia-ffi.so` is needed — the
//! loader builds [`aletheia::Check`]s purely client-side.

use aletheia::{check, load_checks_from_yaml, Rational};

/// The exact fixture the Go doc-example tests load
/// (`go/aletheia/testdata/doc_examples/checks.yaml`) — proving a check file is
/// portable across bindings, not just schema-compatible in the abstract.
const SHARED_FIXTURE: &str = include_str!("../../go/aletheia/testdata/doc_examples/checks.yaml");

#[test]
fn loads_the_shared_cross_binding_fixture() {
    let checks = load_checks_from_yaml(SHARED_FIXTURE).expect("load shared fixture");
    assert_eq!(checks.len(), 2);

    // First check: Speed never_exceeds 220 (integer scalar → 220/1).
    assert_eq!(
        checks[0].formula(),
        check::signal("Speed").never_exceeds(220).formula()
    );
    assert_eq!(checks[0].signal_name(), "Speed");

    // Second check: Voltage stays_between 11.5 and 14.5 (decimals → 23/2, 29/2 via
    // the shared from_f64 convention — the same Rationals the other bindings produce).
    let voltage = check::signal("Voltage")
        .stays_between(
            Rational::from_f64(11.5).unwrap(),
            Rational::from_f64(14.5).unwrap(),
        )
        .unwrap();
    assert_eq!(checks[1].formula(), voltage.formula());
    assert_eq!(
        Rational::from_f64(11.5).unwrap(),
        Rational::new(23, 2).unwrap()
    );
    assert_eq!(
        Rational::from_f64(14.5).unwrap(),
        Rational::new(29, 2).unwrap()
    );
}
