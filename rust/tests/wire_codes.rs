// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Cross-binding wire-code vocabulary parity — Rust side. Mirrors
//! `python/tests/test_wire_codes_parity.py`, `go/aletheia/wire_codes_parity_test.go`,
//! and `cpp/tests/test_wire_codes_parity.cpp` against `docs/WIRE_CODES.yaml`
//! (the cross-binding SSOT, itself anchored to the Agda kernel by the
//! `check-wire-codes` run_ci gate), with the same YAML mechanics as
//! `log_events.rs`.
//!
//! Issue codes: every SSOT code must decode to a NAMED [`IssueCode`] variant
//! (never the `Unknown(String)` forward-compat catch-all) and round-trip
//! through [`IssueCode::as_str`]. The reverse direction has no variant
//! iteration to walk, but it cannot rot silently either: `as_str`'s
//! exhaustive in-crate match forces every new variant to declare a wire
//! string, and the kernel↔YAML gate plus the distinct-count assertion below
//! fail until that variant's SSOT row lands.
//!
//! Error codes: Rust deliberately has NO `ErrorCode` enum — kernel error
//! codes travel as an open `String` in [`Error::Core`] (Go-consistent,
//! addition-proof), with exactly three codes lifted to typed variants. The
//! completeness statement for an open vocabulary is lossless passthrough:
//! every SSOT error code is driven through the real client decode path over
//! a [`MockBackend`] and must surface verbatim in `Error::Core { code, .. }`.
//! The three typed lifts are pinned separately: their trigger codes must be
//! SSOT members (a kernel rename rewrites the YAML via the kernel gate and
//! fails here, flagging the stale Rust literal) and their structured
//! envelopes must produce the typed variant carrying the same wire code.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use aletheia::{Client, Error, IssueCode, MockBackend};
use yaml_rust2::YamlLoader;

/// The `name` column of one `docs/WIRE_CODES.yaml` section, in file order.
fn yaml_section(section: &str) -> Vec<String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/WIRE_CODES.yaml");
    let text = fs::read_to_string(&path).expect("read docs/WIRE_CODES.yaml");
    let docs = YamlLoader::load_from_str(&text).expect("parse WIRE_CODES.yaml");
    let names: Vec<String> = docs[0][section]
        .as_vec()
        .unwrap_or_else(|| panic!("{section} sequence missing"))
        .iter()
        .map(|e| e["name"].as_str().expect("code name").to_string())
        .collect();
    assert!(!names.is_empty(), "{section} is empty");
    names
}

#[test]
fn every_issue_code_decodes_to_a_named_variant() {
    let yaml_names = yaml_section("issue_codes");
    let mut decoded = BTreeSet::new();
    for name in &yaml_names {
        let code = IssueCode::from_wire(name);
        assert!(
            !matches!(code, IssueCode::Unknown(_)),
            "issue code {name:?} is in docs/WIRE_CODES.yaml but IssueCode::from_wire \
             maps it to Unknown — add the named variant (and its from_wire/as_str arms)"
        );
        assert_eq!(
            code.as_str(),
            name,
            "IssueCode::as_str does not round-trip the wire string for {name:?}"
        );
        decoded.insert(code.as_str().to_string());
    }
    // Distinctness: n SSOT codes -> n distinct named variants (from_wire is
    // injective on the canonical vocabulary).
    assert_eq!(
        decoded.len(),
        yaml_names.len(),
        "two SSOT issue codes decoded to the same IssueCode variant"
    );
    // The forward-compat catch-all is a binding-local sentinel, never a wire
    // code: the SSOT must not list the string it renders for a missing code.
    assert!(
        !yaml_names.iter().any(|n| n == "unknown"),
        "docs/WIRE_CODES.yaml issue_codes contains \"unknown\" — the binding-local \
         sentinel must not become a canonical wire code"
    );
}

#[test]
fn every_error_code_passes_through_the_client_losslessly() {
    let yaml_names = yaml_section("error_codes");

    // The mock is cloned before boxing: clones share the response queue, so
    // responses can be queued per iteration while the client owns the box.
    let mock = MockBackend::new();
    let feeder = mock.clone();
    let client = Client::with_backend(Box::new(mock));

    for name in &yaml_names {
        // A bare error envelope: the three structured lifts degrade to
        // Error::Core without their payload fields, so every code takes the
        // same open-world passthrough path here.
        feeder.respond_json(format!(
            r#"{{"status":"error","code":"{name}","message":"synthetic"}}"#
        ));
        let err = client
            .parse_dbc_text("VERSION \"\"\n")
            .expect_err("queued error envelope must surface as Err");
        match err {
            Error::Core { code, message } => {
                assert_eq!(&code, name, "wire code did not pass through verbatim");
                assert_eq!(message, "synthetic");
            }
            other => panic!("error code {name:?} decoded to {other:?}, expected Error::Core"),
        }
    }
}

#[test]
fn typed_lift_trigger_codes_are_ssot_members_and_lift() {
    let yaml_names: BTreeSet<String> = yaml_section("error_codes").into_iter().collect();
    for lifted in [
        "input_bound_exceeded",
        "handler_validation_failed",
        "handler_text_roundtrip_failed",
    ] {
        assert!(
            yaml_names.contains(lifted),
            "Rust lifts {lifted:?} to a typed Error variant but the code is not in \
             docs/WIRE_CODES.yaml — the kernel renamed or retired it; update the lift"
        );
    }

    let mock = MockBackend::new();
    let feeder = mock.clone();
    let client = Client::with_backend(Box::new(mock));

    feeder.respond_json(
        r#"{"status":"error","code":"input_bound_exceeded","message":"m",
            "bound_kind":"input_length_bytes","observed":10,"limit":5}"#,
    );
    match client
        .parse_dbc_text("VERSION \"\"\n")
        .expect_err("queued error")
    {
        Error::InputBoundExceeded {
            code,
            bound_kind,
            observed,
            limit,
        } => {
            assert_eq!(code, "input_bound_exceeded");
            assert_eq!(bound_kind, "input_length_bytes");
            assert_eq!((observed, limit), (10, 5));
        }
        other => panic!("expected Error::InputBoundExceeded, got {other:?}"),
    }

    let issues_payload = r#""has_errors":true,"issues":[
        {"severity":"error","code":"duplicate_message_id","detail":"d"}]"#;
    feeder.respond_json(format!(
        r#"{{"status":"error","code":"handler_validation_failed","message":"m",{issues_payload}}}"#
    ));
    match client
        .parse_dbc_text("VERSION \"\"\n")
        .expect_err("queued error")
    {
        Error::ValidationFailed {
            code,
            has_errors,
            issues,
            ..
        } => {
            assert_eq!(code, "handler_validation_failed");
            assert!(has_errors);
            assert_eq!(issues.len(), 1);
            assert_eq!(issues[0].code, IssueCode::DuplicateMessageId);
        }
        other => panic!("expected Error::ValidationFailed, got {other:?}"),
    }

    feeder.respond_json(format!(
        r#"{{"status":"error","code":"handler_text_roundtrip_failed","message":"m",{issues_payload}}}"#
    ));
    match client
        .parse_dbc_text("VERSION \"\"\n")
        .expect_err("queued error")
    {
        Error::TextRoundtripFailed { code, .. } => {
            assert_eq!(code, "handler_text_roundtrip_failed");
        }
        other => panic!("expected Error::TextRoundtripFailed, got {other:?}"),
    }
}
