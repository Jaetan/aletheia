// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A library laid out for another ABI version is refused by the version it
//! reports, before any other entry is resolved. Its own test binary (= its own
//! process) for the reason `symbol_missing.rs` gives: once the stand-in loads,
//! it stays loaded for the process lifetime. The stand-in is the one the build
//! makes beside the library, exporting nothing but a version no binding was
//! written against.

mod stand_in;

use aletheia::{Client, Error};

#[test]
fn a_library_at_another_abi_version_is_refused() {
    let out = stand_in::stand_in("stale_abi_kernel");
    std::env::set_var("ALETHEIA_LIB", &out);
    let Err(err) = Client::new() else {
        panic!("Client::new must refuse a library at another ABI version")
    };
    match err {
        Error::AbiMismatch { library, binding } => {
            assert_eq!(
                library,
                binding + 1,
                "the stand-in reports one past the binding"
            );
            assert_eq!(
                err.to_string(),
                format!(
                    "the library implements ABI version {library}, and this binding needs {binding}"
                )
            );
        }
        other => panic!("expected Error::AbiMismatch; got: {other:?}"),
    }
}
