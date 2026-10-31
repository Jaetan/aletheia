// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Cross-binding parity test for `Rational::from_decimal`, the kernel decimal
//! single source of truth (the float principle: a decimal is an exact rational,
//! never a float). Mirrors `python/tests/test_parse_decimal_ffi.py` so every
//! binding accepts and rejects the *same* decimal grammar, produces the *same*
//! exact rationals and reads the *same* kernel refusal. Decimal parsing is
//! RTS-gated, so the suite brings up a backend first; the RTS-down path is
//! covered in `rts_uninitialized.rs`.

use aletheia::limits::BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE;
use aletheia::{BoundRefusal, Client, Error, Rational};

/// (input, negative, numerator magnitude, denominator): exact, lowest terms.
/// A negative zero is zero, trailing fraction zeros are trimmed, leading zeros
/// are accepted, a magnitude past 64 bits is carried, and the magnitude bound
/// 2^128-1 fits, as does its negation.
const SUCCESS: &[(&str, bool, u128, u128)] = &[
    ("3.14", false, 157, 50),
    ("42", false, 42, 1),
    ("0.1", false, 1, 10),
    ("-3.14", true, 157, 50),
    ("0", false, 0, 1),
    ("-0", false, 0, 1),
    ("0.000", false, 0, 1),
    ("0.10", false, 1, 10),
    ("00.1", false, 1, 10),
    ("9223372036854775807", false, 9_223_372_036_854_775_807, 1),
    ("-9223372036854775808", true, 9_223_372_036_854_775_808, 1),
    (
        "99999999999999999999.5",
        false,
        199_999_999_999_999_999_999,
        2,
    ),
    (
        "340282366920938463463374607431768211455",
        false,
        u128::MAX,
        1,
    ),
    (
        "-340282366920938463463374607431768211455",
        true,
        u128::MAX,
        1,
    ),
];

/// (input, the kernel's refusal code, the column it stopped at). The grammar
/// is `-?digits[.digits+]`: text that is not a literal at all is
/// `text_parse_failure`; a literal followed by more text (a `+` sign is not a
/// literal, a leading `.` is not, an exponent, a fraction bar, a trailing `.`
/// or a space is more text) is `text_trailing_input`.
const PARSE_FAIL: &[(&str, &str, u32)] = &[
    ("3.14xyz", "text_trailing_input", 5),
    ("1e3", "text_trailing_input", 2),
    (".5", "text_parse_failure", 1),
    ("+1", "text_parse_failure", 1),
    ("1/2", "text_trailing_input", 2),
    ("1.", "text_trailing_input", 3),
    ("1 ", "text_trailing_input", 2),
    (" 1", "text_parse_failure", 1),
    ("", "text_parse_failure", 1),
    ("-", "text_parse_failure", 2),
];

/// The rational component magnitude bound the kernel holds the numerator and
/// the denominator to, 2^128-1.
const COMPONENT_LIMIT: u128 = u128::MAX;

/// Inputs whose numerator or denominator magnitude is past the bound: a
/// forty-digit integer part, thirty-nine decimal places and one past the
/// bound on the negative side.
fn overflowing() -> [String; 3] {
    [
        format!("1{}", "0".repeat(39)),
        format!("0.{}1", "0".repeat(38)),
        "-340282366920938463463374607431768211456".to_owned(),
    ]
}

fn rts() -> Client {
    Client::new().expect("init GHC RTS (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)")
}

#[test]
fn parses_valid_decimals_to_exact_rationals() {
    let _rts = rts();
    for &(text, negative, num, den) in SUCCESS {
        let r = Rational::from_decimal(text).unwrap_or_else(|e| panic!("{text:?}: {e}"));
        assert_eq!(
            (r.is_negative(), r.numerator(), r.denominator()),
            (negative, num, den),
            "{text:?} should parse to {negative} {num}/{den}"
        );
    }
}

#[test]
fn rejects_malformed_decimals_with_the_kernel_code() {
    let _rts = rts();
    for &(text, expected, column) in PARSE_FAIL {
        let err = Rational::from_decimal(text)
            .expect_err(&format!("{text:?} should be rejected by the grammar"));
        let at = format!("parse failed at line 1, column {column}");
        assert!(
            matches!(
                &err,
                Error::Validation { code: Some(code), message, .. }
                    if code == expected && message.contains(&at)
            ),
            "{text:?}: expected Error::Validation with code {expected:?} saying {at:?}, got {err:?}"
        );
    }
}

#[test]
fn rejects_overflowing_decimals_as_the_bound_refusal() {
    // The kernel reports a magnitude up to the bound, so each observes the
    // bound and the message names no number.
    let _rts = rts();
    let message = format!("decimal: rational component magnitude exceeds limit {COMPONENT_LIMIT}");
    for text in overflowing() {
        let err = Rational::from_decimal(&text)
            .expect_err(&format!("{text:?} crosses the component magnitude bound"));
        assert!(
            matches!(
                &err,
                Error::InputBoundExceeded(refusal) if matches!(
                    &**refusal,
                    BoundRefusal {
                        code,
                        bound_kind,
                        observed: COMPONENT_LIMIT,
                        limit: COMPONENT_LIMIT,
                        field: Some(field),
                        ..
                    } if code == "input_bound_exceeded"
                        && bound_kind == BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE
                        && field == "decimal"
                )
            ),
            "{text:?}: expected Error::InputBoundExceeded observing {COMPONENT_LIMIT} \
             against {COMPONENT_LIMIT} in field \"decimal\", got {err:?}"
        );
        assert_eq!(err.to_string(), message, "{text:?}");
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
            &err,
            Error::Validation { code: Some(code), message, .. }
                if code == "text_trailing_input"
                    && message.contains("parse failed at line 1, column 4")
        ),
        "expected Error::Validation with code \"text_trailing_input\" at column 4, got {err:?}"
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
