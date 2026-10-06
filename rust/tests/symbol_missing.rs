// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The missing-export half of the symbol-cache contract: a shared object that
//! *loads* but lacks the Aletheia exports fails construction with the precise
//! missing-symbol name. Its own test binary (= its own process) because once
//! the export-less library successfully loads, it stays loaded for the process
//! lifetime (the loaded-once contract) — every later `Client::new()` in the
//! same process would resolve against it and fail, so this test must not share
//! a binary with any suite that needs the real library (`symbol_cache.rs`
//! covers the load-failure/recovery sequence in its own process).

mod stand_in;

use aletheia::{Client, Error};

#[test]
fn loadable_library_without_exports_names_the_missing_symbol() {
    // The stand-in the build makes that loads and exports no kernel symbol.
    std::env::set_var("ALETHEIA_LIB", stand_in::stand_in("symbolless"));
    let Err(err) = Client::new() else {
        panic!("Client::new must fail against an export-less library")
    };
    match err {
        Error::SymbolMissing(name) => assert_eq!(
            name, "aletheia_abi_version",
            "the error must name the first export the resolver looks up"
        ),
        other => panic!("expected Error::SymbolMissing; got: {other:?}"),
    }
}
