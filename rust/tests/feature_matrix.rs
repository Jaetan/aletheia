// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! FEATURE_MATRIX parity gate for the Rust binding (Cat 32-style mandatory gate).
//!
//! Loads `docs/FEATURE_MATRIX.yaml`, validates the schema for every binding
//! column, and — for each feature the `rust` column claims `implemented` —
//! resolves the entry symbol against the crate source. Catches silent removal
//! or rename of a public symbol, or matrix drift. Mirrors the per-binding gates
//! in `python/tests/`, `go/aletheia/`, and `cpp/tests/`.

use std::fs;
use std::path::{Path, PathBuf};

use yaml_rust2::{Yaml, YamlLoader};

const BINDINGS: [&str; 4] = ["python", "cpp", "go", "rust"];
const VALID_STATUS: [&str; 3] = ["implemented", "not_applicable", "planned"];

fn matrix_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/FEATURE_MATRIX.yaml")
}

fn src_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

/// Replace `//` line comments and `/* */` block comments with spaces, so a stale
/// doc-comment reference (`[Client::send_frame]`) cannot satisfy a symbol check
/// after the item itself has been deleted.
fn strip_comments(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            out.push(' '); // replace (not remove) so tokens cannot concatenate across the comment
        } else if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                i += 1;
            }
            i += 2;
            out.push(' '); // e.g. `Cli/* */ent` -> `Cli ent`, never `Client`
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Whole-word presence of `sym` in `haystack` (no partial-identifier matches).
fn symbol_present(haystack: &str, sym: &str) -> bool {
    if sym.is_empty() {
        return false;
    }
    let mut from = 0;
    while let Some(rel) = haystack[from..].find(sym) {
        let pos = from + rel;
        let before_ok = pos == 0 || !is_ident_char(haystack[..pos].chars().next_back().unwrap());
        let after = pos + sym.len();
        let after_ok =
            after >= haystack.len() || !is_ident_char(haystack[after..].chars().next().unwrap());
        if before_ok && after_ok {
            return true;
        }
        from = pos + 1;
    }
    false
}

/// Concatenated, comment-stripped text of every `.rs` file under `dir`.
fn collect_source(dir: &Path) -> String {
    fn collect(dir: &Path, acc: &mut String) {
        for entry in fs::read_dir(dir).expect("read src dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect(&path, acc);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let text = fs::read_to_string(&path).expect("read .rs file");
                acc.push_str(&strip_comments(&text));
                acc.push('\n');
            }
        }
    }
    let mut acc = String::new();
    collect(dir, &mut acc);
    acc
}

/// Source of the main crate (`rust/src`).
fn crate_source() -> String {
    collect_source(&src_dir())
}

/// The `src/` dir of a nested sub-crate (`rust/<pkg>/src`) — e.g. the optional
/// `aletheia-excel` crate. Mirrors the Go gate's sub-package resolution
/// (`feature_matrix_test.go`), adapted to Rust's nested-crate layout.
fn pkg_src_dir(pkg: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(pkg).join("src")
}

#[test]
fn feature_matrix_rust_parity() {
    let text = fs::read_to_string(matrix_path()).expect("read FEATURE_MATRIX.yaml");
    let docs = YamlLoader::load_from_str(&text).expect("parse FEATURE_MATRIX.yaml");
    let features = docs[0]["features"]
        .as_vec()
        .expect("features must be a sequence");
    assert!(!features.is_empty(), "FEATURE_MATRIX has no features");

    let source = crate_source();
    // Sub-crate sources (e.g. `excel`) are read on demand and cached, since a
    // `pkg:symbol` entry resolves against `rust/<pkg>/src` rather than `rust/src`.
    let mut pkg_sources: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    let mut failures: Vec<String> = Vec::new();

    for feat in features {
        let id = feat["id"].as_str().unwrap_or("<no-id>");
        for &field in &["id", "name", "description"] {
            if feat[field].as_str().map(str::is_empty).unwrap_or(true) {
                failures.push(format!("{id}: missing/empty '{field}'"));
            }
        }
        for binding in BINDINGS {
            let b = &feat["bindings"][binding];
            if matches!(b, Yaml::BadValue) {
                failures.push(format!("{id}: missing '{binding}' binding"));
                continue;
            }
            let status = b["status"].as_str().unwrap_or("");
            if !VALID_STATUS.contains(&status) {
                failures.push(format!("{id}/{binding}: invalid status {status:?}"));
                continue;
            }
            if status == "implemented" && b["entry"].as_str().map(str::is_empty).unwrap_or(true) {
                failures.push(format!(
                    "{id}/{binding}: implemented requires non-empty 'entry'"
                ));
            }
            if status == "not_applicable" && b["reason"].as_str().map(str::is_empty).unwrap_or(true)
            {
                failures.push(format!(
                    "{id}/{binding}: not_applicable requires non-empty 'reason'"
                ));
            }
        }

        // Rust-specific: resolve every `implemented` entry against the source.
        let rust = &feat["bindings"]["rust"];
        if rust["status"].as_str() == Some("implemented") {
            if let Some(entry) = rust["entry"].as_str() {
                let entry = entry.trim();
                // A single-colon `pkg:symbol` entry (not a `::` Rust path) names a
                // symbol in the sub-crate `rust/<pkg>/src`; otherwise the last
                // `::` segment resolves against the main crate `rust/src`.
                if entry.contains(':') && !entry.contains("::") {
                    let mut parts = entry.splitn(2, ':');
                    let pkg = parts.next().unwrap_or("").trim();
                    let symbol = parts.next().unwrap_or("").trim();
                    let dir = pkg_src_dir(pkg);
                    if !dir.is_dir() {
                        failures.push(format!(
                            "{id}/rust: entry {entry:?} — sub-crate dir {} not found",
                            dir.display()
                        ));
                    } else {
                        let src = pkg_sources
                            .entry(pkg.to_string())
                            .or_insert_with(|| collect_source(&dir));
                        if !symbol_present(src, symbol) {
                            failures.push(format!(
                                "{id}/rust: entry {entry:?} — symbol {symbol:?} not found in rust/{pkg}/src"
                            ));
                        }
                    }
                } else {
                    let symbol = entry.rsplit("::").next().unwrap_or(entry).trim();
                    if !symbol_present(&source, symbol) {
                        failures.push(format!(
                            "{id}/rust: entry {entry:?} — symbol {symbol:?} not found in rust/src"
                        ));
                    }
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "FEATURE_MATRIX parity failures:\n  {}",
        failures.join("\n  ")
    );
}
