// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

use super::*;

#[test]
fn decode_extraction_accepts_well_formed() {
    let r =
        decode_extraction(r#"{"values":[],"errors":[{"name":"S","error":"bad"}],"absent":["A"]}"#)
            .expect("well-formed");
    assert_eq!(
        r.errors,
        vec![SignalError {
            name: "S".into(),
            reason: "bad".into()
        }]
    );
    assert_eq!(r.absent, vec!["A".to_string()]);
}

#[test]
fn decode_extraction_rejects_non_string_absent_entry() {
    assert!(decode_extraction(r#"{"values":[],"errors":[],"absent":[123]}"#).is_err());
}

#[test]
fn decode_extraction_rejects_non_object_error_entry() {
    assert!(decode_extraction(r#"{"values":[],"errors":["oops"],"absent":[]}"#).is_err());
    // missing "name" inside an object entry is also rejected
    assert!(decode_extraction(r#"{"values":[],"errors":[{"error":"x"}],"absent":[]}"#).is_err());
}

#[test]
fn decode_validation_rejects_missing_issue_code() {
    // A present-but-unknown code is fine (Unknown fallback); a *missing* code
    // (or severity) is a protocol error.
    let ok = decode_validation(
        r#"{"status":"validation","has_errors":false,"issues":[{"severity":"warning","code":"some_future_code","detail":"d"}]}"#,
    )
    .expect("unknown-but-present code is accepted");
    assert_eq!(
        ok.issues[0].code,
        IssueCode::Unknown("some_future_code".into())
    );
    assert!(decode_validation(
        r#"{"status":"validation","has_errors":false,"issues":[{"severity":"warning","detail":"d"}]}"#,
    )
    .is_err());
}

// --- Reject-branch coverage (cross-binding parity with Go #86). Each drives a
// decoder directly with a malformed/unexpected wire response the verified core
// never emits, so only a direct test reaches these rejects. cargo-llvm-cov
// confirmed these response.rs branches were previously uncovered. ---

#[test]
fn rational_from_value_rejects_non_number_non_object() {
    // A value that is neither a scalar integer nor a {numerator, denominator}
    // object is rejected, not silently coerced to zero.
    let err = decode_extraction(r#"{"values":[{"name":"S","value":"x"}]}"#).unwrap_err();
    assert!(
        err.to_string()
            .contains("expected number or rational object"),
        "got: {err}"
    );
}

#[test]
fn issue_severity_rejects_unknown() {
    // The severity vocabulary is closed — an unknown severity is a protocol
    // error (unlike IssueCode, which falls back to Unknown).
    let err = decode_validation(
        r#"{"status":"validation","has_errors":false,"issues":[{"severity":"fatal","code":"factor_zero","detail":"d"}]}"#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("unknown validation severity"),
        "got: {err}"
    );
}

#[test]
fn parse_verdict_rejects_unknown_status() {
    // A property result whose verdict status is unrecognised is rejected.
    let err = decode_frame(
        r#"{"type":"property_batch","results":[{"status":"bogus","property_index":0,"reason":"r"}]}"#,
    )
    .unwrap_err();
    assert!(err.to_string().contains("unknown verdict"), "got: {err}");
}

#[test]
fn decode_frame_rejects_empty_property_batch() {
    // A zero-event frame is encoded as ack; an empty property_batch is drift.
    let err = decode_frame(r#"{"type":"property_batch","results":[]}"#).unwrap_err();
    assert!(err.to_string().contains("must be non-empty"), "got: {err}");
}

#[test]
fn decode_frame_rejects_unexpected_shape() {
    // Neither an ack nor a property_batch — unrecognised frame response.
    let err = decode_frame(r#"{"status":"weird"}"#).unwrap_err();
    assert!(
        err.to_string().contains("unexpected frame response"),
        "got: {err}"
    );
}

#[test]
fn decode_ack_or_success_rejects_unexpected_status() {
    let err = decode_ack_or_success(r#"{"status":"weird"}"#).unwrap_err();
    assert!(err.to_string().contains("expected status"), "got: {err}");
}

#[test]
fn decode_validation_rejects_unexpected_status() {
    let err = decode_validation(r#"{"status":"weird"}"#).unwrap_err();
    assert!(err.to_string().contains("expected status"), "got: {err}");
}

#[test]
fn decode_format_text_rejects_unexpected_status() {
    let err = decode_format_text(r#"{"status":"weird"}"#).unwrap_err();
    assert!(err.to_string().contains("expected status"), "got: {err}");
}

#[test]
fn decode_format_text_carries_text_and_issues() {
    // A formatDBCText success response yields the text image plus its
    // wfTextIssues diagnostics (warning-severity, advisory).
    let dt = decode_format_text(
        r#"{"status":"success","text":"VERSION \"\"\n","issues":[{"severity":"warning","code":"unknown_value_description_target","detail":"VAL_ for an undeclared signal"}]}"#,
    )
    .expect("decode success");
    assert_eq!(dt.text, "VERSION \"\"\n");
    assert_eq!(dt.issues.len(), 1);
    assert_eq!(dt.issues[0].severity, IssueSeverity::Warning);
    assert_eq!(dt.issues[0].code, IssueCode::UnknownValueDescriptionTarget);
}

#[test]
fn decode_format_text_absent_issues_defaults_empty() {
    // No `issues` field on a success response → empty advisory list.
    let dt = decode_format_text(r#"{"status":"success","text":"x"}"#).expect("decode success");
    assert!(dt.issues.is_empty());
}

#[test]
fn decode_format_text_rejects_non_array_issues() {
    // A present-but-non-array `issues` on a success response is a protocol
    // error, not silently dropped to empty (parity with Python/Go).
    let err = decode_format_text(r#"{"status":"success","text":"","issues":{}}"#).unwrap_err();
    assert!(
        err.to_string().contains("'issues' must be an array"),
        "got: {err}"
    );
}

#[test]
fn format_text_refusal_lifts_to_text_roundtrip_failed() {
    // format_dbc_text is always strict: a handler_text_roundtrip_failed
    // envelope lifts into the typed Error::TextRoundtripFailed (led by the
    // error-severity text_roundtrip_divergence issue, plus the mux diagnostic)
    // rather than a generic Error::Core.
    let err = decode_format_text(
        r#"{"status":"error","code":"handler_text_roundtrip_failed","message":"text round-trip failed","has_errors":true,"issues":[{"severity":"error","code":"text_roundtrip_divergence","detail":"does not reproduce the input DBC"},{"severity":"warning","code":"multi_value_mux_selector","detail":"multi-value mux selector"}]}"#,
    )
    .unwrap_err();
    match err {
        Error::TextRoundtripFailed {
            code,
            has_errors,
            issues,
            ..
        } => {
            assert_eq!(code, "handler_text_roundtrip_failed");
            assert!(has_errors);
            assert_eq!(issues.len(), 2);
            assert_eq!(issues[0].code, IssueCode::TextRoundtripDivergence);
            assert_eq!(issues[1].code, IssueCode::MultiValueMuxSelector);
        }
        other => panic!("expected TextRoundtripFailed, got {other:?}"),
    }
}

#[test]
fn parse_object_lifts_input_bound_exceeded_triple() {
    // A well-typed input_bound_exceeded triple lifts into the typed
    // Error::InputBoundExceeded (parity with Go/C++/Python), not a generic Core.
    let err = parse_object(
        r#"{"status":"error","code":"input_bound_exceeded","message":"too deep","bound_kind":"nesting_depth","observed":65,"limit":64}"#,
    )
    .unwrap_err();
    let text = err.to_string();
    match err {
        Error::InputBoundExceeded {
            code,
            message,
            bound_kind,
            observed,
            limit,
            field,
        } => {
            assert_eq!(code, "input_bound_exceeded");
            assert_eq!(message, "too deep");
            assert_eq!(bound_kind, "nesting_depth");
            assert_eq!(observed, 65);
            assert_eq!(limit, 64);
            assert_eq!(field, None, "an envelope naming no field lifts to None");
        }
        other => panic!("expected Error::InputBoundExceeded, got {other:?}"),
    }
    // Display renders the kernel's message and nothing else.
    assert_eq!(text, "too deep");
}

#[test]
fn parse_object_lifts_the_field_a_dbc_size_refusal_names() {
    let err = parse_object(
        r#"{"status":"error","code":"input_bound_exceeded","message":"ParseDBC: senders array: array cardinality 10001 exceeds limit 10000","field":"senders array","bound_kind":"array_cardinality","observed":10001,"limit":10000}"#,
    )
    .unwrap_err();
    let kernel = "ParseDBC: senders array: array cardinality 10001 exceeds limit 10000";
    assert!(
        matches!(&err, Error::InputBoundExceeded { message, field: Some(f), observed: 10_001, limit: 10_000, .. }
            if message == kernel && f == "senders array"),
        "got: {err:?}"
    );
    assert_eq!(err.to_string(), kernel);
}

#[test]
fn parse_object_degrades_a_message_missing_or_not_a_string_to_core() {
    for member in [
        "",
        r#","message":7"#,
        r#","message":null"#,
        r#","message":[]"#,
    ] {
        let err = parse_object(&format!(
            r#"{{"status":"error","code":"input_bound_exceeded"{member},"field":"senders array","bound_kind":"array_cardinality","observed":10001,"limit":10000}}"#
        ))
        .unwrap_err();
        assert!(
            matches!(&err, Error::Core { code, message }
                if code == "input_bound_exceeded" && message.is_empty()),
            "member {member:?}: expected Error::Core, got {err:?}"
        );
    }
}

#[test]
fn parse_object_degrades_a_field_that_is_not_a_string_to_core() {
    for field in ["7", "null", "[]"] {
        let err = parse_object(&format!(
            r#"{{"status":"error","code":"input_bound_exceeded","message":"m","field":{field},"bound_kind":"array_cardinality","observed":10001,"limit":10000}}"#
        ))
        .unwrap_err();
        assert!(
            matches!(&err, Error::Core { code, message }
                if code == "input_bound_exceeded" && message == "m"),
            "field {field}: expected Error::Core, got {err:?}"
        );
    }
}

#[test]
fn parse_object_degrades_malformed_bound_triple_to_core() {
    // A malformed triple (observed is a string, not a number) degrades to the
    // generic Error::Core — never a partial InputBoundExceeded (matches the peers).
    let err = parse_object(
        r#"{"status":"error","code":"input_bound_exceeded","message":"m","bound_kind":"nesting_depth","observed":"65","limit":64}"#,
    )
    .unwrap_err();
    assert!(
        matches!(err, Error::Core { .. }),
        "expected Error::Core, got {err:?}"
    );
}

#[test]
fn parse_object_lifts_handler_validation_failed_issues() {
    // A well-typed has_errors/issues payload lifts into the typed
    // Error::ValidationFailed, carrying the legacy message unchanged and
    // every issue (errors and warnings) in report order.
    let err = parse_object(
        r#"{"status":"error","code":"handler_validation_failed","message":"ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'","has_errors":true,"issues":[{"severity":"error","code":"duplicate_signal_name","detail":"Message 'M': duplicate signal name 'S'"},{"severity":"warning","code":"offset_scale_range","detail":"w"}]}"#,
    )
    .unwrap_err();
    // Display renders the legacy message plus the issue count.
    assert!(
        err.to_string().contains(
            "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S' (2 validation issues)"
        ),
        "Display: {err}"
    );
    match err {
        Error::ValidationFailed {
            code,
            message,
            has_errors,
            issues,
        } => {
            assert_eq!(code, "handler_validation_failed");
            assert_eq!(
                message,
                "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'"
            );
            assert!(has_errors);
            assert_eq!(
                issues,
                vec![
                    ValidationIssue {
                        severity: IssueSeverity::Error,
                        code: IssueCode::DuplicateSignalName,
                        detail: "Message 'M': duplicate signal name 'S'".into(),
                    },
                    ValidationIssue {
                        severity: IssueSeverity::Warning,
                        code: IssueCode::OffsetScaleRange,
                        detail: "w".into(),
                    },
                ]
            );
        }
        other => panic!("expected Error::ValidationFailed, got {other:?}"),
    }
}

#[test]
fn parse_object_lifts_unknown_issue_code_in_validation_payload() {
    // An unknown-but-present issue code is NOT malformed (IssueCode::Unknown
    // fallback, matching decode_validation) — the lift still applies.
    let err = parse_object(
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":[{"severity":"error","code":"some_future_code","detail":"d"}]}"#,
    )
    .unwrap_err();
    match err {
        Error::ValidationFailed { issues, .. } => {
            assert_eq!(
                issues[0].code,
                IssueCode::Unknown("some_future_code".into())
            );
        }
        other => panic!("expected Error::ValidationFailed, got {other:?}"),
    }
}

#[test]
fn parse_object_degrades_malformed_validation_payload_to_core() {
    // A missing or ill-typed has_errors/issues payload degrades to the
    // generic Error::Core (message preserved) — never a partial
    // ValidationFailed, and never harder than the pre-lift decode.
    let malformed = [
        // no issues, no has_errors (the legacy envelope)
        r#"{"status":"error","code":"handler_validation_failed","message":"m"}"#,
        // has_errors present but issues missing
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true}"#,
        // issues present but has_errors missing
        r#"{"status":"error","code":"handler_validation_failed","message":"m","issues":[]}"#,
        // has_errors ill-typed (string, not bool)
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":"true","issues":[]}"#,
        // issues ill-typed (object, not array)
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":{}}"#,
        // issue element outside the closed severity vocabulary
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":[{"severity":"fatal","code":"factor_zero","detail":"d"}]}"#,
        // issue element missing its code
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":[{"severity":"error","detail":"d"}]}"#,
        // issue element not an object
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":["oops"]}"#,
    ];
    for raw in malformed {
        let err = parse_object(raw).unwrap_err();
        match err {
            Error::Core { code, message } => {
                assert_eq!(code, "handler_validation_failed", "for {raw}");
                assert_eq!(message, "m", "for {raw}");
            }
            other => panic!("expected Error::Core for {raw}, got {other:?}"),
        }
    }
}

// ── decode_extraction_bin (the packed binary hot path) ──────────────────
// Crafted-byte tests: the real-FFI happy path is mutation-excluded, so these
// pure-function tests are the only unit + mutation coverage of the offset
// arithmetic. Every section carries >= 2 entries so a stride off-by-one is
// caught. Native byte order matches the decoder (Storable poke).

fn push_value(buf: &mut Vec<u8>, idx: u16, num: i64, den: i64) {
    buf.extend_from_slice(&idx.to_ne_bytes());
    buf.extend_from_slice(&num.to_ne_bytes());
    buf.extend_from_slice(&den.to_ne_bytes());
}

fn push_error(buf: &mut Vec<u8>, idx: u16, code: u8) {
    buf.extend_from_slice(&idx.to_ne_bytes());
    buf.push(code);
}

fn push_offsets(buf: &mut Vec<u8>, offsets: &[u32]) {
    for off in offsets {
        buf.extend_from_slice(&off.to_ne_bytes());
    }
}

fn bin_header(nvals: u16, nerrs: u16, nabss: u16, reason_bytes: u32) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&nvals.to_ne_bytes());
    buf.extend_from_slice(&nerrs.to_ne_bytes());
    buf.extend_from_slice(&nabss.to_ne_bytes());
    buf.extend_from_slice(&reason_bytes.to_ne_bytes());
    buf
}

fn names() -> Vec<String> {
    vec!["Speed".to_string(), "Rpm".to_string(), "Temp".to_string()]
}

#[test]
fn decode_bin_happy_two_of_each() {
    // The FIRST reason contains a multi-byte UTF-8 char ('∉' = 3 bytes), so a
    // decoder that counted chars instead of bytes would slice the SECOND
    // reason at the wrong boundary — this pins offsets as byte counts.
    let reason_a = "value out of bounds: 16383.75 ∉ [0, 8000]";
    let reason_b = "signal 'Speed' not found in message";
    let blob = [reason_a, reason_b].concat();
    let mut buf = bin_header(2, 2, 2, blob.len() as u32);
    push_value(&mut buf, 0, 100, 4); // Speed = 100/4
    push_value(&mut buf, 2, -7, 2); // Temp = -7/2
    push_error(&mut buf, 1, 1); // Rpm: OutOfBounds
    push_error(&mut buf, 0, 0); // Speed: NotInDBC
    push_offsets(&mut buf, &[0, reason_a.len() as u32, blob.len() as u32]);
    buf.extend_from_slice(blob.as_bytes());
    buf.extend_from_slice(&1u16.to_ne_bytes()); // absent: Rpm
    buf.extend_from_slice(&2u16.to_ne_bytes()); // absent: Temp

    let r = decode_extraction_bin(&buf, &names()).expect("well-formed buffer");
    assert_eq!(
        r.values,
        vec![
            SignalValue {
                name: "Speed".into(),
                value: Rational::new(100, 4).unwrap()
            },
            SignalValue {
                name: "Temp".into(),
                value: Rational::new(-7, 2).unwrap()
            },
        ]
    );
    assert_eq!(
        r.errors,
        vec![
            SignalError {
                name: "Rpm".into(),
                reason: reason_a.into()
            },
            SignalError {
                name: "Speed".into(),
                reason: reason_b.into()
            },
        ]
    );
    assert_eq!(r.absent, vec!["Rpm".to_string(), "Temp".to_string()]);
}

#[test]
fn decode_bin_empty_is_empty_result() {
    // Zero errors: the offsets section is still present — the single entry 0.
    let mut buf = bin_header(0, 0, 0, 0);
    push_offsets(&mut buf, &[0]);
    let r = decode_extraction_bin(&buf, &names()).expect("empty buffer");
    assert!(r.values.is_empty() && r.errors.is_empty() && r.absent.is_empty());
}

#[test]
fn decode_bin_names_what_a_short_buffer_lacks() {
    // Nine bytes cannot hold the header; ten hold it and nothing else, and
    // the smallest well-formed buffer is fourteen (the header plus the one
    // offset a zero-error section still carries), so ten is refused for
    // its total length, not for its header.
    let header = decode_extraction_bin(&[0u8; 9], &names())
        .unwrap_err()
        .to_string();
    assert!(header.contains("header"), "got: {header}");
    let total = decode_extraction_bin(&[0u8; 10], &names())
        .unwrap_err()
        .to_string();
    assert!(total.contains("length 10 != expected 14"), "got: {total}");
}

#[test]
fn decode_bin_accepts_an_empty_reason() {
    // Two errors whose first reason is empty: consecutive equal offsets are
    // non-decreasing and decode to an empty string, not a refusal.
    let reason_b = "signal 'Speed' not found in message";
    let mut buf = bin_header(0, 2, 0, reason_b.len() as u32);
    push_error(&mut buf, 1, 1);
    push_error(&mut buf, 0, 0);
    push_offsets(&mut buf, &[0, 0, reason_b.len() as u32]);
    buf.extend_from_slice(reason_b.as_bytes());
    let r = decode_extraction_bin(&buf, &names()).expect("well-formed");
    assert_eq!(
        r.errors
            .iter()
            .map(|e| e.reason.as_str())
            .collect::<Vec<_>>(),
        vec!["", reason_b]
    );
}

#[test]
fn severity_and_code_display_their_wire_strings() {
    assert_eq!(IssueSeverity::Error.as_str(), "error");
    assert_eq!(IssueSeverity::Warning.as_str(), "warning");
    assert_eq!(IssueSeverity::Error.to_string(), "error");
    assert_eq!(IssueSeverity::Warning.to_string(), "warning");
    assert_eq!(
        IssueCode::AttributeEnumDefaultUnstable.to_string(),
        "attribute_enum_default_unstable"
    );
    assert_eq!(
        IssueCode::Unknown("later_code".into()).to_string(),
        "later_code"
    );
}

#[test]
fn decode_bin_transports_every_code_reason_is_authoritative() {
    // The u8 code never selects the reason — the wire string does. All eight
    // kernel codes plus an out-of-vocabulary one (99) decode fine, each
    // surfacing its own wire reason (unknown codes are NOT rejected).
    let codes = [0u8, 1, 2, 3, 4, 5, 6, 7, 99];
    let reasons: Vec<String> = codes.iter().map(|c| format!("reason #{c}")).collect();
    let blob = reasons.concat();
    let nerrs = u16::try_from(codes.len()).unwrap();
    let mut buf = bin_header(0, nerrs, 0, blob.len() as u32);
    for code in codes {
        push_error(&mut buf, 0, code);
    }
    let mut offsets = vec![0u32];
    for r in &reasons {
        offsets.push(offsets.last().unwrap() + r.len() as u32);
    }
    push_offsets(&mut buf, &offsets);
    buf.extend_from_slice(blob.as_bytes());

    let r = decode_extraction_bin(&buf, &names()).expect("well-formed");
    let decoded: Vec<&str> = r.errors.iter().map(|e| e.reason.as_str()).collect();
    let expected: Vec<&str> = reasons.iter().map(String::as_str).collect();
    assert_eq!(decoded, expected);
}

#[test]
fn decode_bin_name_fallback_for_out_of_range_index() {
    let mut buf = bin_header(1, 0, 0, 0);
    push_value(&mut buf, 42, 1, 1); // index past the 3-name cache
    push_offsets(&mut buf, &[0]);
    let r = decode_extraction_bin(&buf, &names()).expect("well-formed");
    assert_eq!(r.values[0].name, "signal_42");
}

#[test]
fn decode_bin_rejects_non_positive_denominator() {
    let mut buf = bin_header(1, 0, 0, 0);
    push_value(&mut buf, 0, 5, 0); // den = 0
    push_offsets(&mut buf, &[0]);
    assert!(matches!(
        decode_extraction_bin(&buf, &names()),
        Err(Error::Protocol(_))
    ));
}

#[test]
fn decode_bin_rejects_short_header() {
    // 9 bytes is one short of the 10-byte header.
    assert!(matches!(
        decode_extraction_bin(&[0u8; 9], &names()),
        Err(Error::Protocol(_))
    ));
    assert!(matches!(
        decode_extraction_bin(&[], &names()),
        Err(Error::Protocol(_))
    ));
}

#[test]
fn decode_bin_rejects_truncated_body() {
    let mut buf = bin_header(2, 0, 0, 0);
    push_value(&mut buf, 0, 1, 1); // only 1 of 2 values present
    push_offsets(&mut buf, &[0]);
    assert!(matches!(
        decode_extraction_bin(&buf, &names()),
        Err(Error::Protocol(_))
    ));
}

#[test]
fn decode_bin_rejects_trailing_bytes() {
    let mut buf = bin_header(1, 0, 0, 0);
    push_value(&mut buf, 0, 1, 1);
    push_offsets(&mut buf, &[0]);
    buf.push(0xFF); // one byte too many
    assert!(matches!(
        decode_extraction_bin(&buf, &names()),
        Err(Error::Protocol(_))
    ));
}

#[test]
fn decode_bin_rejects_nonzero_first_offset() {
    // off[0] must be 0; the total size is otherwise consistent, so this
    // failure is attributable to the first-offset invariant alone.
    let mut buf = bin_header(0, 1, 0, 1);
    push_error(&mut buf, 0, 1);
    push_offsets(&mut buf, &[1, 1]);
    buf.push(b'x');
    let err = decode_extraction_bin(&buf, &names()).unwrap_err();
    assert!(err.to_string().contains("must start at 0"), "got: {err}");
}

#[test]
fn decode_bin_rejects_non_monotone_offsets() {
    // off = [0, 2, 1] with reasonBytes = 1: first and last invariants hold,
    // so this failure is attributable to monotonicity alone.
    let mut buf = bin_header(0, 2, 0, 1);
    push_error(&mut buf, 0, 1);
    push_error(&mut buf, 1, 1);
    push_offsets(&mut buf, &[0, 2, 1]);
    buf.push(b'x');
    let err = decode_extraction_bin(&buf, &names()).unwrap_err();
    assert!(
        err.to_string().contains("not monotone non-decreasing"),
        "got: {err}"
    );
}

#[test]
fn decode_bin_rejects_final_offset_mismatch() {
    // off[nErrors] = 1 but reasonBytes = 2: start + monotonicity hold, so
    // this failure is attributable to the final-offset invariant alone.
    let mut buf = bin_header(0, 1, 0, 2);
    push_error(&mut buf, 0, 1);
    push_offsets(&mut buf, &[0, 1]);
    buf.extend_from_slice(b"xy");
    let err = decode_extraction_bin(&buf, &names()).unwrap_err();
    assert!(err.to_string().contains("!= reasonBytes"), "got: {err}");
}

#[test]
fn decode_bin_rejects_invalid_utf8_reason() {
    // 0xFF 0xFE is not valid UTF-8 anywhere in a string; the offsets are
    // consistent, so the decode fails on UTF-8 validation alone.
    let mut buf = bin_header(0, 1, 0, 2);
    push_error(&mut buf, 1, 1);
    push_offsets(&mut buf, &[0, 2]);
    buf.extend_from_slice(&[0xFF, 0xFE]);
    let err = decode_extraction_bin(&buf, &names()).unwrap_err();
    assert!(err.to_string().contains("not valid UTF-8"), "got: {err}");
}
