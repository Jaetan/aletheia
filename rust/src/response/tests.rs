// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

use super::*;
use crate::error::Located;
use crate::limits::{
    BOUND_KIND_ATOM_COUNT, BOUND_KIND_NESTING_DEPTH, BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
};

/// Assert that `result` is the reply refusal printing `text`: a protocol
/// error in the one form of every reply place.
#[track_caller]
fn assert_refused<T: std::fmt::Debug>(result: Result<T, Error>, text: &str) {
    match result {
        Err(Error::Protocol(m)) => assert_eq!(m, text),
        other => panic!("expected the refusal {text:?}, got {other:?}"),
    }
}

/// An extraction reply holding `values`, `errors` and `absent` as given.
fn extraction(values: &str, errors: &str, absent: &str) -> String {
    format!(r#"{{"status":"success","values":{values},"errors":{errors},"absent":{absent}}}"#)
}

#[test]
fn decode_extraction_accepts_well_formed() {
    let r = decode_extraction(&extraction(
        r#"[]"#,
        r#"[{"name":"S","error":"bad"}]"#,
        r#"["A"]"#,
    ))
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
    assert_refused(
        decode_extraction(&extraction("[]", "[]", "[123]")),
        "reply absent: expected string, got number",
    );
}

#[test]
fn decode_extraction_rejects_non_object_error_entry() {
    assert_refused(
        decode_extraction(&extraction("[]", r#"["oops"]"#, "[]")),
        "reply errors: expected object, got string",
    );
    // A missing "name" inside an object entry is refused at its place.
    assert_refused(
        decode_extraction(&extraction("[]", r#"[{"error":"x"}]"#, "[]")),
        "reply errors/name: expected string, got nothing",
    );
}

#[test]
fn decode_validation_rejects_missing_issue_code() {
    // A present-but-unknown code is fine (Unknown fallback); a *missing* code
    // is refused at its place.
    let ok = decode_validation(
        r#"{"status":"validation","has_errors":false,"issues":[{"severity":"warning","code":"some_future_code","detail":"d"}]}"#,
    )
    .expect("unknown-but-present code is accepted");
    assert_eq!(
        ok.issues[0].code,
        IssueCode::Unknown("some_future_code".into())
    );
    assert_refused(
        decode_validation(
            r#"{"status":"validation","has_errors":false,"issues":[{"severity":"warning","detail":"d"}]}"#,
        ),
        "reply issues/code: expected string, got nothing",
    );
}

// --- Reject-branch coverage (cross-binding parity with Go). Each drives a
// decoder directly with a malformed/unexpected wire response the verified core
// never emits, so only a direct test reaches these places. ---

#[test]
fn a_rational_place_refuses_a_value_neither_a_number_nor_a_fraction() {
    // A value that is neither a whole number nor a {numerator, denominator}
    // object is refused, not silently coerced to zero.
    assert_refused(
        decode_extraction(&extraction(r#"[{"name":"S","value":"x"}]"#, "[]", "[]")),
        "reply values/value: expected a rational, got string",
    );
}

#[test]
fn an_issue_severity_outside_its_set_reads_as_its_last_arm() {
    // The kernel proves the severity set it writes, so any word but `error`
    // reads as `warning`, the set's last arm.
    let r = decode_validation(
        r#"{"status":"validation","has_errors":false,"issues":[{"severity":"fatal","code":"factor_zero","detail":"d"}]}"#,
    )
    .expect("the last arm");
    assert_eq!(r.issues[0].severity, IssueSeverity::Warning);
}

#[test]
fn a_verdict_word_outside_its_set_reads_as_its_last_arm() {
    // The kernel proves the verdicts it writes, so any word but `fails` and
    // `holds` reads as `unresolved`, the set's last arm, with its reason.
    let r = decode_frame(
        r#"{"type":"property_batch","results":[{"type":"property","status":"bogus","property_index":0,"reason":"r"}]}"#,
    )
    .expect("the last arm");
    assert_eq!(
        r,
        FrameResponse::Verdicts(vec![PropertyResult {
            property_index: 0,
            verdict: Verdict::Unresolved,
            reason: "r".to_string(),
            timestamp: None,
            enrichment: None,
        }])
    );
}

#[test]
fn an_empty_property_batch_reads_as_no_verdicts() {
    // The kernel proves a batch it writes non-empty, so the reader takes the
    // list as it comes.
    assert_eq!(
        decode_frame(r#"{"type":"property_batch","results":[]}"#).expect("an empty batch"),
        FrameResponse::Verdicts(Vec::new())
    );
}

#[test]
fn decode_frame_rejects_unexpected_shape() {
    // Neither an ack nor a property_batch: the status is the answer's own.
    assert_refused(
        decode_frame(r#"{"status":"weird"}"#),
        r#"reply status: expected "ack" or "error", got "weird""#,
    );
}

#[test]
fn a_reply_with_text_after_its_object_is_refused_as_no_json_text() {
    // The frame and end-of-stream reads each take a reply's one object, and
    // refuse text after it with serde_json's reason.
    for (raw, column) in [
        (r#"{"type":"property_batch","results":[]} x"#, 40),
        (r#"{"status":"ack"} {}"#, 18),
    ] {
        assert_refused(
            decode_frame(raw),
            &format!(
                "reply: expected JSON text, got trailing characters at line 1 column {column}"
            ),
        );
    }
    assert_refused(
        decode_stream(r#"{"status":"complete","results":[],"warnings":[]}}"#),
        "reply: expected JSON text, got trailing characters at line 1 column 49",
    );
}

#[test]
fn each_command_awaits_its_own_status() {
    // set_properties and start_stream await "success", send_error and
    // send_remote "ack"; each refuses the other's status as it refuses any
    // word outside its own, the words quoted.
    assert!(decode_success(r#"{"status":"success"}"#).is_ok());
    assert!(decode_event_ack(r#"{"status":"ack"}"#).is_ok());
    for (raw, came) in [
        (r#"{"status":"weird"}"#, r#""weird""#),
        (r#"{"status":"ack"}"#, r#""ack""#),
    ] {
        assert_refused(
            decode_success(raw),
            &format!(r#"reply status: expected "success" or "error", got {came}"#),
        );
    }
    for (raw, came) in [
        (r#"{"status":"weird"}"#, r#""weird""#),
        (r#"{"status":"success"}"#, r#""success""#),
    ] {
        assert_refused(
            decode_event_ack(raw),
            &format!(r#"reply status: expected "ack" or "error", got {came}"#),
        );
    }
}

#[test]
fn decode_validation_rejects_unexpected_status() {
    assert_refused(
        decode_validation(r#"{"status":"weird"}"#),
        r#"reply status: expected "validation" or "error", got "weird""#,
    );
}

#[test]
fn decode_format_text_rejects_unexpected_status() {
    assert_refused(
        decode_format_text(r#"{"status":"weird"}"#),
        r#"reply status: expected "success" or "error", got "weird""#,
    );
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
fn decode_format_text_refuses_absent_issues() {
    // The kernel writes `issues` on every success, so a reply lacking it is
    // refused at its place rather than read as an empty list.
    assert_refused(
        decode_format_text(r#"{"status":"success","text":"x"}"#),
        "reply issues: expected array, got nothing",
    );
}

#[test]
fn decode_format_text_rejects_non_array_issues() {
    // A present-but-non-array `issues` on a success response is refused, not
    // silently dropped to empty (parity with Python/Go).
    assert_refused(
        decode_format_text(r#"{"status":"success","text":"","issues":{}}"#),
        "reply issues: expected array, got object",
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
fn error_envelope_lifts_input_bound_exceeded_triple() {
    // A well-typed input_bound_exceeded triple lifts into the typed
    // Error::InputBoundExceeded (parity with Go/C++/Python), not a generic Core.
    let err = error_envelope(
        r#"{"status":"error","code":"input_bound_exceeded","message":"too deep","bound_kind":"nesting_depth","observed":65,"limit":64}"#,
    );
    let text = err.to_string();
    match err {
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
            assert_eq!(code, "input_bound_exceeded");
            assert_eq!(message, "too deep");
            assert_eq!(bound_kind, BOUND_KIND_NESTING_DEPTH);
            assert_eq!(observed, 65);
            assert_eq!(limit, 64);
            assert_eq!(field, None, "an envelope naming no field lifts to None");
            assert_eq!(located, None, "the lift locates nothing");
        }
        other => panic!("expected Error::InputBoundExceeded, got {other:?}"),
    }
    // Display renders the kernel's message and nothing else.
    assert_eq!(text, "too deep");
}

#[test]
fn error_envelope_lifts_the_field_a_dbc_size_refusal_names() {
    let err = error_envelope(
        r#"{"status":"error","code":"input_bound_exceeded","message":"ParseDBC: senders array: array cardinality 10001 exceeds limit 10000","field":"senders array","bound_kind":"array_cardinality","observed":10001,"limit":10000}"#,
    );
    let kernel = "ParseDBC: senders array: array cardinality 10001 exceeds limit 10000";
    assert!(
        matches!(&err, Error::InputBoundExceeded(refusal)
            if refusal.message == kernel && refusal.field.as_deref() == Some("senders array")
                && refusal.observed == 10_001 && refusal.limit == 10_000),
        "got: {err:?}"
    );
    assert_eq!(err.to_string(), kernel);
}

#[test]
fn error_envelope_lifts_the_saturated_observed_the_kernel_reports() {
    // The kernel reports a measured value past 2^128 - 1 as 2^128 - 1, its
    // message naming only the limit: the typed observed and limit hold both
    // exactly at 128 bits.
    let kernel = "ParseDBCText: signal maximum: rational component magnitude exceeds limit 340282366920938463463374607431768211455";
    let err = error_envelope(&format!(
        r#"{{"status":"error","code":"input_bound_exceeded","message":"{kernel}","bound_kind":"rational_component_magnitude","observed":340282366920938463463374607431768211455,"limit":340282366920938463463374607431768211455}}"#
    ));
    assert!(
        matches!(&err, Error::InputBoundExceeded(refusal)
            if refusal.message == kernel && refusal.field.is_none()
                && refusal.observed == u128::MAX && refusal.limit == u128::MAX),
        "got: {err:?}"
    );
    assert_eq!(err.to_string(), kernel);
}

#[test]
fn error_envelope_refuses_a_message_missing_or_not_a_string() {
    // The envelope's message is read whole: an absent one, or one of another
    // kind, is refused at its place, never degraded to Error::Core.
    for (member, came) in [
        ("", "nothing"),
        (r#","message":7"#, "number"),
        (r#","message":null"#, "null"),
        (r#","message":[]"#, "array"),
    ] {
        assert_refused::<()>(
            Err(error_envelope(&format!(
                r#"{{"status":"error","code":"input_bound_exceeded"{member},"field":"senders array","bound_kind":"array_cardinality","observed":10001,"limit":10000}}"#
            ))),
            &format!("reply message: expected string, got {came}"),
        );
    }
}

#[test]
fn error_envelope_refuses_a_field_that_is_not_a_string() {
    for (field, came) in [("7", "number"), ("null", "null"), ("[]", "array")] {
        assert_refused::<()>(
            Err(error_envelope(&format!(
                r#"{{"status":"error","code":"input_bound_exceeded","message":"m","field":{field},"bound_kind":"array_cardinality","observed":10001,"limit":10000}}"#
            ))),
            &format!("reply field: expected string, got {came}"),
        );
    }
}

#[test]
fn error_envelope_refuses_a_malformed_bound_triple() {
    // A malformed triple (observed is a string, not a number) is refused at
    // its place, never a partial InputBoundExceeded nor a degraded Core.
    assert_refused::<()>(
        Err(error_envelope(
            r#"{"status":"error","code":"input_bound_exceeded","message":"m","bound_kind":"nesting_depth","observed":"65","limit":64}"#,
        )),
        "reply observed: expected number, got string",
    );
}

#[test]
fn error_envelope_lifts_handler_validation_failed_issues() {
    // A well-typed has_errors/issues payload lifts into the typed
    // Error::ValidationFailed, carrying the legacy message unchanged and
    // every issue (errors and warnings) in report order.
    let err = error_envelope(
        r#"{"status":"error","code":"handler_validation_failed","message":"ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'","has_errors":true,"issues":[{"severity":"error","code":"duplicate_signal_name","detail":"Message 'M': duplicate signal name 'S'"},{"severity":"warning","code":"offset_scale_range","detail":"w"}]}"#,
    );
    // Display renders the kernel's message alone; the issues are fields.
    assert_eq!(
        err.to_string(),
        "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'"
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
fn error_envelope_lifts_unknown_issue_code_in_validation_payload() {
    // An unknown-but-present issue code is NOT malformed (IssueCode::Unknown
    // fallback, matching decode_validation): the lift still applies.
    let err = error_envelope(
        r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":[{"severity":"error","code":"some_future_code","detail":"d"}]}"#,
    );
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
fn error_envelope_refuses_a_malformed_validation_payload() {
    // A missing or ill-typed has_errors/issues payload is refused at its
    // place: never a partial ValidationFailed, never a degraded Core.
    let malformed = [
        // no issues, no has_errors
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m"}"#,
            "reply has_errors: expected boolean, got nothing",
        ),
        // has_errors present but issues missing
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true}"#,
            "reply issues: expected array, got nothing",
        ),
        // issues present but has_errors missing
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m","issues":[]}"#,
            "reply has_errors: expected boolean, got nothing",
        ),
        // has_errors ill-typed (string, not bool)
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":"true","issues":[]}"#,
            "reply has_errors: expected boolean, got string",
        ),
        // issues ill-typed (object, not array)
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":{}}"#,
            "reply issues: expected array, got object",
        ),
        // issue element missing its code
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":[{"severity":"error","detail":"d"}]}"#,
            "reply issues/code: expected string, got nothing",
        ),
        // issue element not an object
        (
            r#"{"status":"error","code":"handler_validation_failed","message":"m","has_errors":true,"issues":["oops"]}"#,
            "reply issues: expected object, got string",
        ),
    ];
    for (raw, refusal) in malformed {
        assert_refused::<()>(Err(error_envelope(raw)), refusal);
    }
}

// ── decode_extraction_bin (the packed binary hot path) ──────────────────
// Crafted-byte tests: the real-FFI happy path is mutation-excluded, so these
// pure-function tests are the only unit + mutation coverage of the offset
// arithmetic. Every section carries >= 2 entries so a stride off-by-one is
// caught. Every multi-byte field is little-endian, as the decoder reads it.

/// A 128-bit magnitude as the wire carries it: its low `u64`, then its high
/// `u64`, each little-endian.
fn push_u128(buf: &mut Vec<u8>, n: u128) {
    buf.extend_from_slice(&(n as u64).to_le_bytes());
    buf.extend_from_slice(&((n >> 64) as u64).to_le_bytes());
}

/// One value entry: its signal index, its sign byte, its numerator and its
/// denominator, as the kernel writes the rational `negative`, `num` / `den`.
fn push_parts(buf: &mut Vec<u8>, idx: u16, negative: bool, num: u128, den: u128) {
    buf.extend_from_slice(&idx.to_le_bytes());
    buf.push(u8::from(negative));
    push_u128(buf, num);
    push_u128(buf, den);
}

/// One value entry holding `r`, reduced as the kernel writes every rational.
fn push_value(buf: &mut Vec<u8>, idx: u16, r: Rational) {
    push_parts(buf, idx, r.is_negative(), r.numerator(), r.denominator());
}

fn push_error(buf: &mut Vec<u8>, idx: u16, code: u8) {
    buf.extend_from_slice(&idx.to_le_bytes());
    buf.push(code);
}

fn push_offsets(buf: &mut Vec<u8>, offsets: &[u32]) {
    for off in offsets {
        buf.extend_from_slice(&off.to_le_bytes());
    }
}

fn bin_header(nvals: u16, nerrs: u16, nabss: u16, reason_bytes: u32) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&nvals.to_le_bytes());
    buf.extend_from_slice(&nerrs.to_le_bytes());
    buf.extend_from_slice(&nabss.to_le_bytes());
    buf.extend_from_slice(&reason_bytes.to_le_bytes());
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
    // Speed's numerator and denominator each reach past 64 bits, so both
    // words of each u128 are read, high word above low.
    let speed = Rational::from_parts(false, u128::MAX, (1 << 64) + 3).unwrap();
    let temp = Rational::new(-7, 2).unwrap();
    let mut buf = bin_header(2, 2, 2, blob.len() as u32);
    push_value(&mut buf, 0, speed);
    push_value(&mut buf, 2, temp);
    push_error(&mut buf, 1, 1); // Rpm: OutOfBounds
    push_error(&mut buf, 0, 0); // Speed: NotInDBC
    push_offsets(&mut buf, &[0, reason_a.len() as u32, blob.len() as u32]);
    buf.extend_from_slice(blob.as_bytes());
    buf.extend_from_slice(&1u16.to_le_bytes()); // absent: Rpm
    buf.extend_from_slice(&2u16.to_le_bytes()); // absent: Temp

    let r = decode_extraction_bin(&buf, &names()).expect("well-formed buffer");
    assert_eq!(
        r.values,
        vec![
            SignalValue {
                name: "Speed".into(),
                value: speed
            },
            SignalValue {
                name: "Temp".into(),
                value: temp
            },
        ]
    );
    assert_eq!(
        (
            r.values[0].value.numerator(),
            r.values[0].value.denominator()
        ),
        (u128::MAX, (1 << 64) + 3)
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
fn decode_bin_stores_each_value_as_written() {
    // The kernel proves every rational it writes reduced over a positive
    // denominator, so the reader stores each as written: a zero denominator
    // and an unreduced fraction come back unchanged, and a sign byte other
    // than 0 is negative, a zero unsigned whatever its byte.
    let mut buf = bin_header(3, 0, 0, 0);
    push_parts(&mut buf, 0, false, 5, 0);
    push_parts(&mut buf, 1, false, 4, 2);
    push_parts(&mut buf, 2, true, 0, 1);
    buf[10 + 2] = 7; // the first value's sign byte, neither 0 nor 1
    push_offsets(&mut buf, &[0]);
    let r = decode_extraction_bin(&buf, &names()).expect("well-formed");
    let parts: Vec<(bool, u128, u128)> = r
        .values
        .iter()
        .map(|v| {
            (
                v.value.is_negative(),
                v.value.numerator(),
                v.value.denominator(),
            )
        })
        .collect();
    assert_eq!(parts, vec![(true, 5, 0), (false, 4, 2), (false, 0, 1)]);
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
    push_value(&mut buf, 0, Rational::integer(1)); // only 1 of 2 values present
    push_offsets(&mut buf, &[0]);
    assert!(matches!(
        decode_extraction_bin(&buf, &names()),
        Err(Error::Protocol(_))
    ));
}

#[test]
fn decode_bin_rejects_trailing_bytes() {
    let mut buf = bin_header(1, 0, 0, 0);
    push_value(&mut buf, 0, Rational::integer(1));
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

#[test]
fn an_error_prints_its_message_alone() {
    // Every binding prints a refusal as its message, the kernel's text when
    // the kernel refused; kind and code are the variant and its fields.
    let issues = Vec::new();
    let cases = [
        (
            Error::Validation {
                message: "parse failed at line 1, column 4".to_string(),
                code: Some("text_trailing_input".to_string()),
                located: None,
            },
            "parse failed at line 1, column 4",
        ),
        (
            Error::validation("rational denominator is zero"),
            "rational denominator is zero",
        ),
        (Error::Protocol("p".to_string()), "p"),
        (
            Error::Core {
                code: "handler_no_dbc".to_string(),
                message: "StartStream: DBC not loaded".to_string(),
            },
            "StartStream: DBC not loaded",
        ),
        (
            Error::TextRoundtripFailed {
                code: "handler_text_roundtrip_failed".to_string(),
                message: "FormatDBCText: the text does not re-parse".to_string(),
                has_errors: true,
                issues,
            },
            "FormatDBCText: the text does not re-parse",
        ),
    ];
    for (err, want) in cases {
        assert_eq!(err.to_string(), want);
    }
}

#[test]
fn a_located_refusal_prints_its_location_and_key_before_the_message() {
    // A loader locates a refused number; the kernel's message, code and fields
    // stay as the kernel answered them.
    let located = Error::Validation {
        message: "parse failed at line 1, column 4".to_string(),
        code: Some("text_trailing_input".to_string()),
        located: None,
    }
    .located("Check 'C'", "value");
    assert_eq!(
        located.to_string(),
        "Check 'C': invalid 'value': parse failed at line 1, column 4"
    );
    assert!(
        matches!(&located, Error::Validation { message, code: Some(code), located: Some(place) }
            if message == "parse failed at line 1, column 4" && code == "text_trailing_input"
                && place.location == "Check 'C'" && place.key.as_deref() == Some("value")),
        "got: {located:?}"
    );
    assert_eq!(
        (located.location(), located.key()),
        (Some("Check 'C'"), Some("value"))
    );

    let kernel = "decimal: rational component magnitude exceeds limit 340282366920938463463374607431768211455";
    let located = error_envelope(&format!(
        r#"{{"status":"error","code":"input_bound_exceeded","message":"{kernel}","bound_kind":"rational_component_magnitude","observed":340282366920938463463374607431768211455,"limit":340282366920938463463374607431768211455,"field":"decimal"}}"#
    ))
    .located("Row 2", "Factor");
    assert_eq!(
        located.to_string(),
        format!("Row 2: invalid 'Factor': {kernel}")
    );
    assert!(
        matches!(&located, Error::InputBoundExceeded(refusal)
            if matches!(&**refusal, BoundRefusal {
                code, message, bound_kind, observed: u128::MAX,
                limit: u128::MAX, field: Some(field), located: Some(place) }
                if code == "input_bound_exceeded" && message == kernel
                    && bound_kind == BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE && field == "decimal"
                    && place.location == "Row 2" && place.key.as_deref() == Some("Factor"))),
        "got: {located:?}"
    );
    assert_eq!(
        (located.location(), located.key()),
        (Some("Row 2"), Some("Factor"))
    );

    // An error no loader located has no place.
    let unlocated = Error::validation("rational denominator is zero");
    assert_eq!((unlocated.location(), unlocated.key()), (None, None));

    // Every other variant is returned as it was.
    let core = Error::Core {
        code: "handler_no_dbc".to_string(),
        message: "StartStream: DBC not loaded".to_string(),
    }
    .located("Row 2", "Value");
    assert!(
        matches!(&core, Error::Core { code, message }
            if code == "handler_no_dbc" && message == "StartStream: DBC not loaded"),
        "got: {core:?}"
    );
    assert_eq!(core.to_string(), "StartStream: DBC not loaded");
    assert_eq!((core.location(), core.key()), (None, None));
}

#[test]
fn a_bound_refusal_located_at_a_place_prints_the_place_before_the_message() {
    // A check the kernel refuses where it is built is located at the place
    // alone: the boxed refusal gains the place with no key, and its text is
    // the place, then the kernel's message.
    let kernel = "atom count 1025 exceeds limit 1024";
    let located = error_envelope(&format!(
        r#"{{"status":"error","code":"input_bound_exceeded","message":"{kernel}","bound_kind":"atom_count","observed":1025,"limit":1024}}"#
    ))
    .located_at("Check 'C'");
    assert_eq!(located.to_string(), format!("Check 'C': {kernel}"));
    assert_eq!(
        (located.location(), located.key()),
        (Some("Check 'C'"), None)
    );
    assert!(
        matches!(&located, Error::InputBoundExceeded(refusal)
            if refusal.message == kernel
                && refusal.bound_kind == BOUND_KIND_ATOM_COUNT
                && refusal.located.as_deref()
                    == Some(&Located { location: "Check 'C'".to_string(), key: None })),
        "got: {located:?}"
    );
}
