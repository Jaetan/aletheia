// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed decoding of the JSON responses the core returns.

use serde_json::Value;

use crate::error::Error;
use crate::types::Rational;

/// The final verdict for one property.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The property held over the whole trace.
    Holds,
    /// The property was violated.
    Fails,
    /// The property never resolved by end-of-stream (e.g. an uncached atom).
    Unresolved,
}

/// Violation enrichment: the last-known signal values and human-readable reason
/// that accompany a decided property (when the DBC + diagnostics are loaded).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Enrichment {
    /// Last-known signal values referenced by the formula.
    pub signals: Vec<(String, Rational)>,
    /// Human-readable description of the formula.
    pub formula_desc: String,
    /// Formatted reason combining the core reason with the signal values.
    pub enriched_reason: String,
    /// The raw reason string from the Agda kernel.
    pub core_reason: String,
}

/// One property's outcome within a streaming response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyResult {
    /// Index of the property in the set passed to `set_properties`.
    pub property_index: u32,
    /// The verdict.
    pub verdict: Verdict,
    /// The core's reason string (empty if none).
    pub reason: String,
    /// Microsecond timestamp at which the verdict was decided, if reported.
    pub timestamp: Option<u64>,
    /// Enrichment, present on violations when diagnostics are available.
    pub enrichment: Option<Enrichment>,
}

/// A diagnostic warning emitted at `end_stream` (e.g. an atom never cached).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamWarning {
    /// Warning kind (e.g. `uncached_atom`).
    pub kind: String,
    /// The property the warning concerns.
    pub property_index: u32,
    /// Free-text detail (e.g. the signal name).
    pub detail: String,
}

/// The final result of a stream: one verdict per property, plus warnings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamResult {
    /// Per-property verdicts.
    pub results: Vec<PropertyResult>,
    /// End-of-stream diagnostics.
    pub warnings: Vec<StreamWarning>,
}

/// The response to a single `send_frame`: either an acknowledgement, or the
/// property verdicts decided by that frame (a `property_batch`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrameResponse {
    /// No property was decided by this frame.
    Ack,
    /// Properties decided by this frame (violations carry enrichment).
    Verdicts(Vec<PropertyResult>),
}

/// A successfully extracted signal value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignalValue {
    /// Signal name.
    pub name: String,
    /// Exact physical value.
    pub value: Rational,
}

/// One signal's extraction error: the signal name and the core's reason string
/// (e.g. "Value out of bounds"). Mirrors the Go `SignalError` / Python
/// `errors: Mapping[str, str]` — the core emits each error as
/// `{"name": …, "error": …}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignalError {
    /// Signal name.
    pub name: String,
    /// Human-readable reason from the core.
    pub reason: String,
}

/// The result of `extract_signals`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtractionResult {
    /// Successfully extracted signal values.
    pub values: Vec<SignalValue>,
    /// Signals whose extraction errored, with the core's reason.
    pub errors: Vec<SignalError>,
    /// Names of signals absent from the frame (e.g. an inactive mux branch).
    pub absent: Vec<String>,
}

/// The severity of a validation issue. The core's severity set is closed
/// (exactly `error` / `warning`), so an unknown wire value is rejected at decode
/// — the deliberate counterpart to the forward-compatible [`IssueCode::Unknown`]
/// (the code set may grow; the severity set will not). Mirrors the Python / Go /
/// C++ typed severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IssueSeverity {
    /// A structural issue that prevents correct operation.
    Error,
    /// A non-fatal advisory.
    Warning,
}

impl IssueSeverity {
    fn from_wire(s: &str) -> Result<Self, Error> {
        match s {
            "error" => Ok(IssueSeverity::Error),
            "warning" => Ok(IssueSeverity::Warning),
            other => Err(protocol(format!("unknown validation severity {other:?}"))),
        }
    }

    /// The wire string for this severity.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            IssueSeverity::Error => "error",
            IssueSeverity::Warning => "warning",
        }
    }
}

impl std::fmt::Display for IssueSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A machine-readable DBC validation issue code, mirroring the Agda `IssueCode`
/// ADT and the Python / Go / C++ vocabularies. Unknown wire codes map to
/// [`IssueCode::Unknown`] so a future core code round-trips rather than failing
/// the decode (the code set may grow; cf. the strict [`IssueSeverity`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IssueCode {
    /// Two messages share the same CAN id.
    DuplicateMessageId,
    /// Two signals in the same message share a name.
    DuplicateSignalName,
    /// A signal's scale factor is zero.
    FactorZero,
    /// A multiplexed signal's multiplexor was not found.
    MultiplexorNotFound,
    /// A multiplexor cycle was detected.
    MultiplexorCycle,
    /// A signal name is not unique across all messages.
    GlobalNameCollision,
    /// A signal's declared minimum exceeds its maximum.
    MinExceedsMax,
    /// A signal's bit range exceeds the message DLC.
    SignalExceedsDlc,
    /// Two signals overlap in the same message.
    SignalOverlap,
    /// A signal has zero bit length.
    BitLengthZero,
    /// Two messages share the same name.
    DuplicateMessageName,
    /// The offset/scale combination is out of representable range.
    OffsetScaleRange,
    /// A message has no signals.
    EmptyMessage,
    /// A signal's start bit is out of range.
    StartBitOutOfRange,
    /// A signal's bit length is excessive.
    BitLengthExcessive,
    /// A multiplexor uses non-unit scaling.
    MultiplexorNonUnitScaling,
    /// `BA_DEF_` declares the same attribute name twice.
    DuplicateAttributeName,
    /// A comment references an unknown target.
    UnknownCommentTarget,
    /// A `BO_TX_BU_` names an unknown message sender.
    UnknownMessageSender,
    /// A signal receiver is not a known node.
    UnknownSignalReceiver,
    /// A `VAL_` line references a `(canId, signalName)` with no matching signal.
    UnknownValueDescriptionTarget,
    /// A code outside the known vocabulary (forward-compatible).
    Unknown(String),
}

impl IssueCode {
    /// Map a wire code string to an [`IssueCode`], falling back to
    /// [`IssueCode::Unknown`] for an unrecognised value.
    #[must_use]
    pub fn from_wire(s: &str) -> Self {
        match s {
            "duplicate_message_id" => IssueCode::DuplicateMessageId,
            "duplicate_signal_name" => IssueCode::DuplicateSignalName,
            "factor_zero" => IssueCode::FactorZero,
            "multiplexor_not_found" => IssueCode::MultiplexorNotFound,
            "multiplexor_cycle" => IssueCode::MultiplexorCycle,
            "global_name_collision" => IssueCode::GlobalNameCollision,
            "min_exceeds_max" => IssueCode::MinExceedsMax,
            "signal_exceeds_dlc" => IssueCode::SignalExceedsDlc,
            "signal_overlap" => IssueCode::SignalOverlap,
            "bit_length_zero" => IssueCode::BitLengthZero,
            "duplicate_message_name" => IssueCode::DuplicateMessageName,
            "offset_scale_range" => IssueCode::OffsetScaleRange,
            "empty_message" => IssueCode::EmptyMessage,
            "start_bit_out_of_range" => IssueCode::StartBitOutOfRange,
            "bit_length_excessive" => IssueCode::BitLengthExcessive,
            "multiplexor_non_unit_scaling" => IssueCode::MultiplexorNonUnitScaling,
            "duplicate_attribute_name" => IssueCode::DuplicateAttributeName,
            "unknown_comment_target" => IssueCode::UnknownCommentTarget,
            "unknown_message_sender" => IssueCode::UnknownMessageSender,
            "unknown_signal_receiver" => IssueCode::UnknownSignalReceiver,
            "unknown_value_description_target" => IssueCode::UnknownValueDescriptionTarget,
            other => IssueCode::Unknown(other.to_string()),
        }
    }

    /// The canonical wire string for this code.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            IssueCode::DuplicateMessageId => "duplicate_message_id",
            IssueCode::DuplicateSignalName => "duplicate_signal_name",
            IssueCode::FactorZero => "factor_zero",
            IssueCode::MultiplexorNotFound => "multiplexor_not_found",
            IssueCode::MultiplexorCycle => "multiplexor_cycle",
            IssueCode::GlobalNameCollision => "global_name_collision",
            IssueCode::MinExceedsMax => "min_exceeds_max",
            IssueCode::SignalExceedsDlc => "signal_exceeds_dlc",
            IssueCode::SignalOverlap => "signal_overlap",
            IssueCode::BitLengthZero => "bit_length_zero",
            IssueCode::DuplicateMessageName => "duplicate_message_name",
            IssueCode::OffsetScaleRange => "offset_scale_range",
            IssueCode::EmptyMessage => "empty_message",
            IssueCode::StartBitOutOfRange => "start_bit_out_of_range",
            IssueCode::BitLengthExcessive => "bit_length_excessive",
            IssueCode::MultiplexorNonUnitScaling => "multiplexor_non_unit_scaling",
            IssueCode::DuplicateAttributeName => "duplicate_attribute_name",
            IssueCode::UnknownCommentTarget => "unknown_comment_target",
            IssueCode::UnknownMessageSender => "unknown_message_sender",
            IssueCode::UnknownSignalReceiver => "unknown_signal_receiver",
            IssueCode::UnknownValueDescriptionTarget => "unknown_value_description_target",
            IssueCode::Unknown(s) => s,
        }
    }
}

impl std::fmt::Display for IssueCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A validation issue carried in a `parse_dbc_text` response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationIssue {
    /// Severity.
    pub severity: IssueSeverity,
    /// Machine-readable issue code.
    pub code: IssueCode,
    /// Human-readable detail.
    pub detail: String,
}

/// Decode one validation-issue wire object. Strict on field *presence/type*:
/// `severity` and `code` must be present strings (a missing/non-string field is a
/// protocol error, matching the peer bindings). Strict on the `severity`
/// *vocabulary* (closed set), but lenient on the `code` *vocabulary*
/// ([`IssueCode::from_wire`] maps an unrecognised — but present — code to
/// `Unknown`, since the code set may grow).
pub(crate) fn decode_issue(w: &Value) -> Result<ValidationIssue, Error> {
    Ok(ValidationIssue {
        severity: IssueSeverity::from_wire(&req_str_field(w, "severity", "validation issue")?)?,
        code: IssueCode::from_wire(&req_str_field(w, "code", "validation issue")?),
        detail: str_field(w, "detail"),
    })
}

/// The result of `validate_dbc`: every issue found, plus whether any are errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationResult {
    /// `true` if at least one issue is error-severity.
    pub has_errors: bool,
    /// All issues found (errors and warnings), in report order.
    pub issues: Vec<ValidationIssue>,
}

pub(crate) fn protocol(msg: impl Into<String>) -> Error {
    Error::Protocol(msg.into())
}

/// Parse a raw response string to a JSON object and surface any core error.
pub(crate) fn parse_object(raw: &str) -> Result<Value, Error> {
    let value: Value =
        serde_json::from_str(raw).map_err(|e| protocol(format!("invalid JSON response: {e}")))?;
    if value.get("status").and_then(Value::as_str) == Some("error") {
        let code = value
            .get("code")
            .and_then(Value::as_str)
            .unwrap_or("unknown")
            .to_string();
        let message = value
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        return Err(Error::Core { code, message });
    }
    Ok(value)
}

pub(crate) fn str_field(obj: &Value, key: &str) -> String {
    obj.get(key)
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string()
}

/// Read a *required* string field: a protocol error if it is missing or not a
/// string (the strict counterpart to [`str_field`], matching the peer bindings,
/// which reject a missing/non-string `code` / `name` rather than blanking it).
pub(crate) fn req_str_field(obj: &Value, key: &str, ctx: &str) -> Result<String, Error> {
    obj.get(key)
        .and_then(Value::as_str)
        .map(ToString::to_string)
        .ok_or_else(|| protocol(format!("{ctx}: missing or non-string {key:?} field")))
}

pub(crate) fn u32_field(obj: &Value, key: &str) -> Result<u32, Error> {
    obj.get(key)
        .and_then(Value::as_u64)
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| protocol(format!("missing or out-of-range u32 field {key:?}")))
}

pub(crate) fn bool_field(obj: &Value, key: &str) -> Result<bool, Error> {
    obj.get(key)
        .and_then(Value::as_bool)
        .ok_or_else(|| protocol(format!("missing or non-boolean field {key:?}")))
}

/// Decode a rational from a response scalar (plain integer) or
/// `{"numerator","denominator"}` object.
pub(crate) fn rational_from_value(v: &Value) -> Result<Rational, Error> {
    if let Some(n) = v.as_i64() {
        return Ok(Rational::integer(n));
    }
    if v.is_object() {
        let num = v
            .get("numerator")
            .and_then(Value::as_i64)
            .ok_or_else(|| protocol("rational object missing integer numerator"))?;
        let den = v
            .get("denominator")
            .and_then(Value::as_i64)
            .ok_or_else(|| protocol("rational object missing integer denominator"))?;
        return Rational::new(num, den);
    }
    Err(protocol(format!(
        "expected number or rational object, got {v}"
    )))
}

fn parse_verdict(s: &str) -> Result<Verdict, Error> {
    match s {
        "holds" => Ok(Verdict::Holds),
        "fails" => Ok(Verdict::Fails),
        "unresolved" => Ok(Verdict::Unresolved),
        other => Err(protocol(format!("unknown verdict status {other:?}"))),
    }
}

fn parse_property_result(obj: &Value) -> Result<PropertyResult, Error> {
    let verdict = parse_verdict(&str_field(obj, "status"))?;
    let property_index = u32_field(obj, "property_index")?;
    let timestamp = obj.get("timestamp").and_then(Value::as_u64);
    // Enrichment is not on the wire — the verified core emits only the raw
    // `reason`. The client computes [`Enrichment`] from the registered formulas
    // + last-known signal values (see `crate::enrich`) and fills this in.
    Ok(PropertyResult {
        property_index,
        verdict,
        reason: str_field(obj, "reason"),
        timestamp,
        enrichment: None,
    })
}

fn property_list(obj: &Value) -> Result<Vec<PropertyResult>, Error> {
    obj.get("results")
        .and_then(Value::as_array)
        .map(|arr| arr.iter().map(parse_property_result).collect())
        .unwrap_or_else(|| Ok(Vec::new()))
}

/// Decode a `set_properties` / `start_stream` success response (status only).
pub(crate) fn decode_ack_or_success(raw: &str) -> Result<(), Error> {
    let obj = parse_object(raw)?;
    // Require an explicit ack/success status so response-shape drift surfaces
    // instead of being silently accepted (parse_object already turned a
    // status:"error" envelope into Err).
    match obj.get("status").and_then(Value::as_str) {
        Some("ack" | "success") => Ok(()),
        other => Err(protocol(format!(
            "expected status \"ack\" or \"success\", got {other:?}"
        ))),
    }
}

/// Decode a `send_frame` response: `ack`, or a non-empty `property_batch` of
/// verdicts. Strict (mirrors Go `parseFrameResponse`): an empty batch or an
/// unrecognised status/type is a protocol error, not a silent `Ack` — so
/// wire-shape drift surfaces instead of being swallowed.
pub(crate) fn decode_frame(raw: &str) -> Result<FrameResponse, Error> {
    let obj = parse_object(raw)?;
    if obj.get("status").and_then(Value::as_str) == Some("ack") {
        return Ok(FrameResponse::Ack);
    }
    if obj.get("type").and_then(Value::as_str) == Some("property_batch") {
        let results = property_list(&obj)?;
        if results.is_empty() {
            return Err(protocol(
                "property_batch response 'results' must be non-empty (zero-event frames are encoded as ack)",
            ));
        }
        return Ok(FrameResponse::Verdicts(results));
    }
    Err(protocol(format!(
        "unexpected frame response: status={:?}, type={:?}",
        obj.get("status").and_then(Value::as_str),
        obj.get("type").and_then(Value::as_str)
    )))
}

/// Decode an `end_stream` (`status:"complete"`) response.
pub(crate) fn decode_stream(raw: &str) -> Result<StreamResult, Error> {
    let obj = parse_object(raw)?;
    let results = property_list(&obj)?;
    let warnings = obj
        .get("warnings")
        .and_then(Value::as_array)
        .map(|arr| -> Result<Vec<_>, Error> {
            arr.iter()
                .map(|w| {
                    Ok(StreamWarning {
                        kind: str_field(w, "kind"),
                        property_index: u32_field(w, "property_index")?,
                        detail: str_field(w, "detail"),
                    })
                })
                .collect()
        })
        .unwrap_or_else(|| Ok(Vec::new()))?;
    Ok(StreamResult { results, warnings })
}

/// Decode an `extract_signals` response.
pub(crate) fn decode_extraction(raw: &str) -> Result<ExtractionResult, Error> {
    let obj = parse_object(raw)?;
    let values = obj
        .get("values")
        .and_then(Value::as_array)
        .map(|arr| -> Result<Vec<_>, Error> {
            arr.iter()
                .map(|v| {
                    let value = v
                        .get("value")
                        .ok_or_else(|| protocol("extraction value missing 'value'"))
                        .and_then(rational_from_value)?;
                    Ok(SignalValue {
                        name: str_field(v, "name"),
                        value,
                    })
                })
                .collect()
        })
        .unwrap_or_else(|| Ok(Vec::new()))?;
    // `errors` entries are objects `{"name", "error"}`; `absent` entries are bare
    // strings (`JArray (map JStringS ...)`). Strict on structure (a non-object
    // error entry or non-string absent entry is a protocol error, matching the
    // Go/C++/Python decoders) so wire-shape drift surfaces; the `error` reason
    // field stays lenient (defaults to "" if absent, like the peers).
    let errors = obj
        .get("errors")
        .and_then(Value::as_array)
        .map(|arr| {
            arr.iter()
                .map(|e| {
                    Ok(SignalError {
                        name: req_str_field(e, "name", "extraction error")?,
                        reason: str_field(e, "error"),
                    })
                })
                .collect::<Result<Vec<_>, Error>>()
        })
        .unwrap_or_else(|| Ok(Vec::new()))?;
    let absent = obj
        .get("absent")
        .and_then(Value::as_array)
        .map(|arr| {
            arr.iter()
                .map(|a| {
                    a.as_str()
                        .map(ToString::to_string)
                        .ok_or_else(|| protocol("extraction 'absent' entry must be a string"))
                })
                .collect::<Result<Vec<_>, Error>>()
        })
        .unwrap_or_else(|| Ok(Vec::new()))?;
    Ok(ExtractionResult {
        values,
        errors,
        absent,
    })
}

fn issue_list(obj: &Value) -> Result<Vec<ValidationIssue>, Error> {
    obj.get("issues")
        .and_then(Value::as_array)
        .map(|arr| arr.iter().map(decode_issue).collect())
        .unwrap_or_else(|| Ok(Vec::new()))
}

/// Decode a `validateDBC` (`status:"validation"`) response.
pub(crate) fn decode_validation(raw: &str) -> Result<ValidationResult, Error> {
    let obj = parse_object(raw)?;
    match obj.get("status").and_then(Value::as_str) {
        Some("validation") => Ok(ValidationResult {
            has_errors: bool_field(&obj, "has_errors")?,
            issues: issue_list(&obj)?,
        }),
        other => Err(protocol(format!(
            "expected status \"validation\", got {other:?}"
        ))),
    }
}

/// Decode a `formatDBCText` (`status:"success"`) response into the `.dbc` text.
pub(crate) fn decode_format_text(raw: &str) -> Result<String, Error> {
    let obj = parse_object(raw)?;
    match obj.get("status").and_then(Value::as_str) {
        Some("success") => obj
            .get("text")
            .and_then(Value::as_str)
            .map(ToString::to_string)
            .ok_or_else(|| protocol("formatDBCText response missing 'text'")),
        other => Err(protocol(format!(
            "expected status \"success\", got {other:?}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_extraction_accepts_well_formed() {
        let r = decode_extraction(
            r#"{"values":[],"errors":[{"name":"S","error":"bad"}],"absent":["A"]}"#,
        )
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
        assert!(
            decode_extraction(r#"{"values":[],"errors":[{"error":"x"}],"absent":[]}"#).is_err()
        );
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
        assert!(decode_extraction(r#"{"values":[{"name":"S","value":"x"}]}"#).is_err());
    }

    #[test]
    fn issue_severity_rejects_unknown() {
        // The severity vocabulary is closed — an unknown severity is a protocol
        // error (unlike IssueCode, which falls back to Unknown).
        assert!(decode_validation(
            r#"{"status":"validation","has_errors":false,"issues":[{"severity":"fatal","code":"factor_zero","detail":"d"}]}"#,
        )
        .is_err());
    }

    #[test]
    fn parse_verdict_rejects_unknown_status() {
        // A property result whose verdict status is unrecognised is rejected.
        assert!(decode_frame(
            r#"{"type":"property_batch","results":[{"status":"bogus","property_index":0,"reason":"r"}]}"#,
        )
        .is_err());
    }

    #[test]
    fn decode_frame_rejects_empty_property_batch() {
        // A zero-event frame is encoded as ack; an empty property_batch is drift.
        assert!(decode_frame(r#"{"type":"property_batch","results":[]}"#).is_err());
    }

    #[test]
    fn decode_frame_rejects_unexpected_shape() {
        // Neither an ack nor a property_batch — unrecognised frame response.
        assert!(decode_frame(r#"{"status":"weird"}"#).is_err());
    }

    #[test]
    fn decode_ack_or_success_rejects_unexpected_status() {
        assert!(decode_ack_or_success(r#"{"status":"weird"}"#).is_err());
    }

    #[test]
    fn decode_validation_rejects_unexpected_status() {
        assert!(decode_validation(r#"{"status":"weird"}"#).is_err());
    }

    #[test]
    fn decode_format_text_rejects_unexpected_status() {
        assert!(decode_format_text(r#"{"status":"weird"}"#).is_err());
    }
}
