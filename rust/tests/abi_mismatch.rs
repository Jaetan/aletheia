// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A library laid out for another ABI version is refused by the version it
//! reports, before any other entry is resolved. Its own test binary (= its own
//! process) for the reason `symbol_missing.rs` gives: once the stand-in loads,
//! it stays loaded for the process lifetime. The stand-in is the one every
//! binding's suite compiles, exporting nothing but a version no binding was
//! written against; it is built here with the C compiler the environment names.

use std::path::Path;
use std::process::Command;

use aletheia::{Client, Error};

#[test]
fn a_library_at_another_abi_version_is_refused() {
    let shim = Path::new(env!("CARGO_MANIFEST_DIR")).join("../haskell-shim");
    let out = std::env::temp_dir().join(format!("stale_abi_kernel_{}.so", std::process::id()));
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let status = Command::new(cc)
        .args(["-shared", "-fPIC", "-I"])
        .arg(shim.join("include"))
        .arg("-o")
        .arg(&out)
        .arg(shim.join("test/stale_abi_kernel.c"))
        .status()
        .expect("run the C compiler");
    assert!(status.success(), "the stale-ABI stand-in did not compile");
    std::env::set_var("ALETHEIA_LIB", &out);
    let Err(err) = Client::new() else {
        panic!("Client::new must refuse a library at another ABI version")
    };
    let _ = std::fs::remove_file(&out);
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
