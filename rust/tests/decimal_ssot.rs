// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Cross-binding parity test for `Rational::from_decimal` — the kernel decimal
//! single source of truth (the float principle: a decimal is an exact rational,
//! never a float). Mirrors `python/tests/test_parse_decimal_ffi.py` so the four
//! bindings accept and reject the *same* decimal grammar and produce the *same*
//! exact rationals. Decimal parsing is RTS-gated, so the suite brings up a backend
//! first; the RTS-down path is covered in `rts_uninitialized.rs`.

use aletheia::{Client, Error, Rational};

/// (input, expected numerator, expected denominator) — exact, lowest-terms.
const SUCCESS: &[(&str, i64, i64)] = &[
    ("3.14", 157, 50),
    ("42", 42, 1),
    ("0.1", 1, 10),
    ("-3.14", -157, 50),
    ("0", 0, 1),
    ("-0", 0, 1),                                    // negative zero collapses to +0
    ("0.000", 0, 1),                                 // trailing-zero fraction canonicalises
    ("0.10", 1, 10),                                 // trailing zero trimmed
    ("00.1", 1, 10),                                 // leading zeros accepted
    ("9223372036854775807", 9223372036854775807, 1), // Int64 max fits
];

/// Malformed per the grammar `-?digits[.digits+]`: no `+`, no leading `.`, no
/// exponent, no fraction syntax, and full consumption (trailing input rejected).
const PARSE_FAIL: &[&str] = &[
    "3.14xyz", "1e3", ".5", "+1", "1/2", "1.", "1 ", " 1", "", "-",
];

/// A numerator or denominator beyond the Int64 wire range.
const OVERFLOW: &[&str] = &["99999999999999999999.5", "0.0000000000000000001"];

fn rts() -> Client {
    Client::new().expect("init GHC RTS (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)")
}

#[test]
fn parses_valid_decimals_to_exact_rationals() {
    let _rts = rts();
    for &(text, num, den) in SUCCESS {
        let r = Rational::from_decimal(text).unwrap_or_else(|e| panic!("{text:?}: {e}"));
        assert_eq!(
            r,
            Rational::new(num, den).unwrap(),
            "{text:?} should parse to {num}/{den}"
        );
    }
}

#[test]
fn rejects_malformed_decimals_as_validation_errors() {
    let _rts = rts();
    for &text in PARSE_FAIL {
        let err = Rational::from_decimal(text)
            .expect_err(&format!("{text:?} should be rejected by the grammar"));
        // The grammar/overflow failures map to the user-input error class
        // (Validation) — NOT Protocol/RtsNotInitialized — across every binding.
        assert!(
            matches!(err, Error::Validation(_)),
            "{text:?}: expected Error::Validation, got {err:?}"
        );
    }
}

#[test]
fn rejects_overflowing_decimals_as_validation_errors() {
    let _rts = rts();
    for &text in OVERFLOW {
        let err = Rational::from_decimal(text)
            .expect_err(&format!("{text:?} overflows the i64 wire range"));
        assert!(
            matches!(err, Error::Validation(_)),
            "{text:?}: expected Error::Validation, got {err:?}"
        );
    }
}

#[test]
fn rejects_non_ascii_decimal_as_validation_error() {
    // Regression guard for the shim's JSON encoding of the echoed error-envelope
    // `input` field: a non-ASCII byte must round-trip as valid JSON. Before the
    // Marshal.hs jsonString fix, `show` emitted an invalid-JSON `\NNN` escape, so
    // the envelope failed to parse and surfaced Error::Protocol instead of
    // Error::Validation.
    let _rts = rts();
    let err = Rational::from_decimal("1.5€").expect_err("non-ASCII must be rejected");
    assert!(
        matches!(err, Error::Validation(_)),
        "expected Error::Validation, got {err:?}"
    );
}
