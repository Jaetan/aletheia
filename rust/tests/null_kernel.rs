// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A library that answers the decimal entry with failure and no error envelope
//! is a wire fault, `Error::Protocol`, as in every binding, and the allocation
//! count reads the library's own answer. The null kernel the build makes
//! beside the library answers so, and counts nothing. Its own test binary (=
//! its own process) because a library stays loaded for the process lifetime,
//! and this one must be the first the process loads.

mod stand_in;

use std::sync::Once;

use aletheia::{Client, Error, Rational};

/// Point `ALETHEIA_LIB` at the null kernel, once: the stand-in is found from
/// the variable's first value, before it names the stand-in itself.
fn on_the_null_kernel() {
    static POINTED: Once = Once::new();
    POINTED.call_once(|| std::env::set_var("ALETHEIA_LIB", stand_in::stand_in("null_kernel")));
}

#[test]
fn a_decimal_failure_without_an_envelope_is_a_protocol_error() {
    on_the_null_kernel();
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

#[test]
fn the_allocation_count_is_the_null_kernel_s_zero() {
    on_the_null_kernel();
    // A refused client has still started the runtime the count is read from.
    let refused = Client::new();
    assert!(
        matches!(refused, Err(Error::InitFailed)),
        "got: {:?}",
        refused.err()
    );
    assert_eq!(aletheia::allocated_bytes(), Some(0));
}
