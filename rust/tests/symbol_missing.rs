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

use aletheia::{Client, Error};

/// A shared object that is loadable but carries no Aletheia exports:
/// glibc's math library, at its Debian/Ubuntu multiarch path (CI runs
/// ubuntu-24.04). Other glibc distros place it elsewhere (e.g. `/lib64` on
/// Fedora/RHEL); the prerequisite check below fails loudly there rather than
/// silently skipping.
const EXPORTLESS_SO: &str = "/lib/x86_64-linux-gnu/libm.so.6";

#[test]
fn loadable_library_without_exports_names_the_missing_symbol() {
    assert!(
        std::path::Path::new(EXPORTLESS_SO).exists(),
        "prerequisite missing: {EXPORTLESS_SO} not found — this test needs a \
         loadable shared object without Aletheia exports (glibc's libm); on a \
         non-glibc or non-x86-64 host, point EXPORTLESS_SO at an equivalent"
    );
    std::env::set_var("ALETHEIA_LIB", EXPORTLESS_SO);
    let Err(err) = Client::new() else {
        panic!("Client::new must fail against an export-less library")
    };
    match err {
        Error::SymbolMissing(name) => assert_eq!(
            name, "aletheia_process",
            "the error must name the first export the resolver looks up"
        ),
        other => panic!("expected Error::SymbolMissing; got: {other:?}"),
    }
}
