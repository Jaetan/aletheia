// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The FFI symbol cache's headline semantics: a failed library *load* never
//! latches. Its own test binary because it manipulates the process-global
//! `ALETHEIA_LIB` environment variable — the whole sequence lives in a single
//! `#[test]` so it runs on one thread (no cross-test env races), and a
//! dedicated binary keeps other suites' `Client::new()` calls out of this
//! process. The missing-export half of the contract (a library that *loads*
//! but lacks the Aletheia exports) lives in `symbol_missing.rs`: once a
//! library successfully loads it stays loaded for the process lifetime (the
//! loaded-once contract), so that step would poison this binary's recovery
//! step and needs its own process.

use aletheia::{Client, Error};

/// A known-good DBC the verified text parser accepts (the shared corpus
/// `minimal.dbc`) — the trivial round-trip proving the recovered client works.
const DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

#[test]
fn load_failures_never_latch() {
    // Save the harness-provided real path FIRST: the final step restores it.
    let real = std::env::var("ALETHEIA_LIB").expect(
        "ALETHEIA_LIB must point at a built libaletheia-ffi.so before this test \
         runs (run_ci / CI set it); it is the recovery path for the final step",
    );

    // A nonexistent path: construction fails with the load error naming it.
    std::env::set_var(
        "ALETHEIA_LIB",
        "/nonexistent/aletheia-one/libaletheia-ffi.so",
    );
    let Err(err) = Client::new() else {
        panic!("Client::new must fail for a nonexistent library path")
    };
    match err {
        Error::LibraryLoad { path, .. } => assert_eq!(
            path, "/nonexistent/aletheia-one/libaletheia-ffi.so",
            "the load error must name the path that failed"
        ),
        other => panic!("expected Error::LibraryLoad; got: {other:?}"),
    }

    // A SECOND nonexistent path: the error names the NEW path — the first
    // failure latched nothing (neither the library nor the symbol table).
    std::env::set_var(
        "ALETHEIA_LIB",
        "/nonexistent/aletheia-two/libaletheia-ffi.so",
    );
    let Err(err) = Client::new() else {
        panic!("Client::new must fail for the second bad path too")
    };
    match err {
        Error::LibraryLoad { path, .. } => assert_eq!(
            path, "/nonexistent/aletheia-two/libaletheia-ffi.so",
            "the load error must name the SECOND path — a failed load must not latch"
        ),
        other => panic!("expected Error::LibraryLoad; got: {other:?}"),
    }

    // The real path again: construction now succeeds and completes a trivial
    // round-trip — the failed loads left the caches clean for this process.
    std::env::set_var("ALETHEIA_LIB", &real);
    let client = Client::new()
        .expect("Client::new must succeed once ALETHEIA_LIB points at the real library again");
    client
        .parse_dbc_text(DBC)
        .expect("parse a minimal DBC through the recovered client");
}
