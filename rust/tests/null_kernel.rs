// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A library that answers the decimal entry with failure and no error envelope
//! is a wire fault, `Error::Protocol`, as in every binding. The null kernel the
//! build makes beside the library answers so. Its own test binary (= its own
//! process) because a library stays loaded for the process lifetime, and this
//! one must be the first the process loads.

mod stand_in;

use aletheia::{Client, Error, Rational};

#[test]
fn a_decimal_failure_without_an_envelope_is_a_protocol_error() {
    std::env::set_var("ALETHEIA_LIB", stand_in::stand_in("null_kernel"));
    // The null kernel's runtime entry is a no-op, so the runtime reads as up,
    // and its session entry answers null, so the client itself is refused.
    let refused = Client::new();
    assert!(
        matches!(refused, Err(Error::InitFailed)),
        "got: {:?}",
        refused.err()
    );
    let err = Rational::from_decimal("1").expect_err("the null kernel answers no rational");
    assert!(
        matches!(&err, Error::Protocol(m) if m == "aletheia_parse_decimal failed without an error"),
        "got: {err:?}"
    );
}
