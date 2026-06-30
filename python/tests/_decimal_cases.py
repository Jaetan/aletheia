# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared decimal-grammar test cases for the decimal-SSOT suites.

The public ``from_decimal`` test (``test_from_decimal``) and the raw-FFI
``aletheia_parse_decimal`` test (``test_parse_decimal_ffi``) exercise the
identical kernel decimal grammar, so the case set lives here rather than
duplicated in both (pylint R0801).  The C++/Go/Rust suites mirror this set in
their own languages (a cross-language parity set that cannot share this module).
"""

from __future__ import annotations

# (input, expected numerator, expected denominator) — exact rationals only.
SUCCESS_CASES = [
    ("3.14", 157, 50),
    ("42", 42, 1),
    ("0.1", 1, 10),
    ("-3.14", -157, 50),
    ("0", 0, 1),
    ("-0", 0, 1),  # negative zero collapses to +0
    ("0.000", 0, 1),  # trailing-zero fraction canonicalises
    ("0.10", 1, 10),  # trailing zero trimmed
    ("00.1", 1, 10),  # leading zeros accepted
    ("9223372036854775807", 9223372036854775807, 1),  # Int64 max fits
]

# Malformed per the grammar -?digits[.digits+]: no '+', no leading '.', no
# exponent, no fraction syntax, and full consumption (trailing input rejected).
PARSE_FAIL_CASES = [
    "3.14xyz",
    "1e3",
    ".5",
    "+1",
    "1/2",
    "1.",  # dot with no fractional digit
    "1 ",  # trailing space — full-consume rejects
    " 1",  # leading space
    "",
    "-",
]

# A numerator or denominator beyond the Int64 wire range.
OVERFLOW_CASES = ["99999999999999999999.5", "0.0000000000000000001"]
