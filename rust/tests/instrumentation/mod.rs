// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The variables through which a coverage run instruments what cargo builds,
//! which a test that builds and runs a program of its own removes from both.

use std::env;
use std::ffi::OsString;

/// The variables a coverage run sets to instrument a build and the programs it
/// makes, and the prefixes of the ones cargo-llvm-cov adds.
const INSTRUMENTATION: [&str; 6] = [
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "RUSTDOCFLAGS",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "LLVM_PROFILE_FILE",
];
const INSTRUMENTATION_PREFIXES: [&str; 2] = ["CARGO_LLVM_COV", "__CARGO_LLVM_COV"];

fn is_instrumentation(key: &OsString) -> bool {
    let key = key.to_string_lossy();
    INSTRUMENTATION.contains(&key.as_ref())
        || INSTRUMENTATION_PREFIXES
            .iter()
            .any(|prefix| key.starts_with(prefix))
}

/// The instrumentation variables this process's environment sets.
pub fn variables() -> impl Iterator<Item = OsString> {
    env::vars_os()
        .map(|(key, _)| key)
        .filter(is_instrumentation)
}
