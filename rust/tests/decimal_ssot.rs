// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Cross-binding parity test for `Rational::from_decimal`, the kernel decimal
//! single source of truth (the float principle: a decimal is an exact rational,
//! never a float). Mirrors `python/tests/test_parse_decimal_ffi.py` so every
//! binding accepts and rejects the *same* decimal grammar, produces the *same*
//! exact rationals and reads the *same* kernel refusal. Decimal parsing is
//! RTS-gated, so the suite brings up a backend first; the RTS-down path is
//! covered in `rts_uninitialized.rs`.

use aletheia::{Client, Error, Rational};

/// (input, expected numerator, expected denominator): exact, lowest terms.
const SUCCESS: &[(&str, i64, i64)] = &[
    ("3.14", 157, 50),
    ("42", 42, 1),
    ("0.1", 1, 10),
    ("-3.14", -157, 50),
    ("0", 0, 1),
    ("-0", 0, 1),                                      // negative zero collapses to +0
    ("0.000", 0, 1),                                   // trailing-zero fraction canonicalises
    ("0.10", 1, 10),                                   // trailing zero trimmed
    ("00.1", 1, 10),                                   // leading zeros accepted
    ("9223372036854775807", 9223372036854775807, 1),   // the component bound itself
    ("-9223372036854775807", -9223372036854775807, 1), // and its negation
];

/// (input, the kernel's refusal code). The grammar is `-?digits[.digits+]`:
/// text that is not a literal at all is `text_parse_failure`; a literal
/// followed by more text (a `+` sign is not a literal, a leading `.` is not,
/// an exponent, a fraction bar, a trailing `.` or a space is more text) is
/// `text_trailing_input`.
const PARSE_FAIL: &[(&str, &str)] = &[
    ("3.14xyz", "text_trailing_input"),
    ("1e3", "text_trailing_input"),
    (".5", "text_parse_failure"),
    ("+1", "text_parse_failure"),
    ("1/2", "text_trailing_input"),
    ("1.", "text_trailing_input"),
    ("1 ", "text_trailing_input"),
    (" 1", "text_parse_failure"),
    ("", "text_parse_failure"),
    ("-", "text_parse_failure"),
];

/// The rational component magnitude bound the kernel holds the numerator and
/// the denominator to.
const COMPONENT_LIMIT: u64 = 9223372036854775807;

/// (input, the magnitude the kernel observed). A magnitude the kernel's
/// counter cannot hold is reported as its ceiling, 18446744073709551615, and
/// the message then says "at least".
const OVERFLOW: &[(&str, u64)] = &[
    ("99999999999999999999.5", 18446744073709551615),
    ("0.0000000000000000001", 10000000000000000000),
    ("-9223372036854775808", 9223372036854775808),
];

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
fn rejects_malformed_decimals_with_the_kernel_code() {
    let _rts = rts();
    for &(text, expected) in PARSE_FAIL {
        let err = Rational::from_decimal(text)
            .expect_err(&format!("{text:?} should be rejected by the grammar"));
        assert!(
            matches!(err, Error::Validation { code: Some(ref code), .. } if code == expected),
            "{text:?}: expected Error::Validation with code {expected:?}, got {err:?}"
        );
    }
}

#[test]
fn rejects_overflowing_decimals_as_the_bound_refusal() {
    let _rts = rts();
    for &(text, expected_observed) in OVERFLOW {
        let err = Rational::from_decimal(text)
            .expect_err(&format!("{text:?} crosses the component magnitude bound"));
        assert!(
            matches!(
                err,
                Error::InputBoundExceeded {
                    observed,
                    limit: COMPONENT_LIMIT,
                    field: Some(ref field),
                    ..
                } if observed == expected_observed && field == "decimal"
            ),
            "{text:?}: expected Error::InputBoundExceeded observing {expected_observed} \
             against {COMPONENT_LIMIT} in field \"decimal\", got {err:?}"
        );
    }
}

#[test]
fn rejects_non_ascii_decimal_as_trailing_input() {
    // A non-ASCII character after a literal is a grammar failure, not a UTF-8
    // one: the kernel reads the text as UTF-8 and refuses what follows the
    // literal.
    let _rts = rts();
    let err = Rational::from_decimal("1.5€").expect_err("non-ASCII must be rejected");
    assert!(
        matches!(
            err,
            Error::Validation { code: Some(ref code), .. } if code == "text_trailing_input"
        ),
        "expected Error::Validation with code \"text_trailing_input\", got {err:?}"
    );
}

#[test]
fn rejects_a_nul_byte_as_the_shims_refusal() {
    // The binding passes the text's every byte, so a NUL inside it reaches
    // the shim, which refuses it before the kernel reads the literal.
    let _rts = rts();
    let err = Rational::from_decimal("1\u{0}5").expect_err("a NUL byte must be rejected");
    assert!(
        matches!(
            err,
            Error::Validation { ref message, code: Some(ref code), located: None }
                if code == "ffi_validation_error" && message == "input contains a NUL byte"
        ),
        "expected Error::Validation with code \"ffi_validation_error\", got {err:?}"
    );
}
