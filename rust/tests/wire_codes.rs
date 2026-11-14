// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Cross-binding wire-code vocabulary parity — Rust side. Mirrors
//! `python/tests/test_wire_codes_parity.py`, `go/aletheia/wire_codes_parity_test.go`,
//! and `cpp/tests/test_wire_codes_parity.cpp` against `docs/WIRE_CODES.yaml`
//! (the cross-binding SSOT, itself anchored to the Agda kernel by the
//! `check-wire-codes` run_ci gate), with the same YAML mechanics as
//! `log_events.rs`.
//!
//! Issue codes: every SSOT code must decode to an [`IssueCode`] variant and
//! round-trip through [`IssueCode::as_str`]. The reverse direction has no variant
//! iteration to walk, but it cannot rot silently either: `as_str`'s
//! exhaustive in-crate match forces every new variant to declare a wire
//! string, and the kernel↔YAML gate plus the distinct-count assertion below
//! fail until that variant's SSOT row lands.
//!
//! Error codes: every SSOT code must decode to an [`ErrorCode`] variant and
//! round-trip through [`ErrorCode::as_str`] and its `Display`; an in-crate
//! test holds the variants to the SSOT in its order, and a code outside them
//! is refused. Every SSOT error code is driven through the real client decode
//! path over a [`MockBackend`] and must surface as its variant in
//! `Error::Core { code, .. }`, but for the codes whose envelope carries a
//! payload of its own, which a bare envelope lacks and which is refused at its
//! place instead.
//! The typed lifts are pinned separately: their trigger codes must be
//! SSOT members (a kernel rename rewrites the YAML via the kernel gate and
//! fails here, flagging the stale Rust literal) and their structured
//! envelopes must produce the typed variant carrying the same wire code.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use aletheia::limits::BOUND_KIND_INPUT_LENGTH_BYTES;
use aletheia::{BoundRefusal, Client, Error, ErrorCode, IssueCode, MockBackend};
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
    let mut decoded: BTreeSet<&'static str> = BTreeSet::new();
    for name in &yaml_names {
        let word = IssueCode::from_wire(name)
            .map(IssueCode::as_str)
            .unwrap_or_else(|| {
                panic!(
                    "issue code {name:?} is in docs/WIRE_CODES.yaml but IssueCode::from_wire \
                     names no variant for it: add the variant (and its from_wire/as_str arms)"
                )
            });
        assert_eq!(
            word, name,
            "IssueCode::as_str does not round-trip the wire string for {name:?}"
        );
        decoded.insert(word);
    }
    // Distinctness: n SSOT codes -> n distinct variants (from_wire is
    // injective on the canonical vocabulary).
    assert_eq!(
        decoded.len(),
        yaml_names.len(),
        "two SSOT issue codes decoded to the same IssueCode variant"
    );
}

#[test]
fn every_error_code_decodes_to_a_named_variant() {
    for name in &yaml_section("error_codes") {
        let code = ErrorCode::from_wire(name).unwrap_or_else(|| {
            panic!(
                "error code {name:?} is in docs/WIRE_CODES.yaml but ErrorCode::from_wire \
                 names no variant for it: add the variant and its as_str arm"
            )
        });
        let word: &'static str = code.as_str();
        assert_eq!(word, name, "ErrorCode::as_str does not round-trip {name:?}");
        assert_eq!(code.to_string(), *name, "ErrorCode's text is not {name:?}");
    }
    assert_eq!(ErrorCode::from_wire("some_future_code"), None);
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
        // A bare error envelope: every code without a payload of its own takes
        // the same passthrough path, and a code with one is refused
        // at the payload's first place, the envelope being read whole.
        feeder.respond_json(format!(
            r#"{{"status":"error","code":"{name}","message":"synthetic"}}"#
        ));
        let err = client
            .parse_dbc_text("VERSION \"\"\n")
            .expect_err("queued error envelope must surface as Err");
        let payload_refusal = match name.as_str() {
            "input_bound_exceeded" => Some("reply bound_kind: expected string, got nothing"),
            "handler_validation_failed" | "handler_text_roundtrip_failed" => {
                Some("reply has_errors: expected boolean, got nothing")
            }
            _ => None,
        };
        match (err, payload_refusal) {
            (Error::Core { code, message }, None) => {
                assert_eq!(
                    code.as_str(),
                    name,
                    "wire code did not pass through verbatim"
                );
                assert_eq!(message, "synthetic");
            }
            (Error::Protocol(refusal), Some(expected)) => {
                assert_eq!(refusal, expected, "the bare {name:?} envelope's refusal");
            }
            (other, None) => {
                panic!("error code {name:?} decoded to {other:?}, expected Error::Core")
            }
            (other, Some(expected)) => panic!(
                "error code {name:?} decoded to {other:?}, expected Error::Protocol({expected:?})"
            ),
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
        Error::InputBoundExceeded(refusal) => {
            let BoundRefusal {
                code,
                message,
                bound_kind,
                observed,
                limit,
                field,
                located,
            } = *refusal;
            assert_eq!(code, ErrorCode::InputBoundExceeded);
            assert_eq!(message, "m");
            assert_eq!(bound_kind, BOUND_KIND_INPUT_LENGTH_BYTES);
            assert_eq!((observed, limit), (10, 5));
            assert_eq!(field, None, "a bound on the input's length names no field");
            assert_eq!(located, None, "the lift locates nothing");
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
            assert_eq!(code, ErrorCode::HandlerValidationFailed);
            assert!(has_errors);
            let codes: Vec<IssueCode> = issues.iter().map(|issue| issue.code).collect();
            assert_eq!(codes, [IssueCode::DuplicateMessageId]);
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
            assert_eq!(code, ErrorCode::HandlerTextRoundtripFailed);
        }
        other => panic!("expected Error::TextRoundtripFailed, got {other:?}"),
    }
}
