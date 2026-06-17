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

/// The result of `extract_signals`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtractionResult {
    /// Successfully extracted signal values.
    pub values: Vec<SignalValue>,
    /// Names of signals whose extraction errored.
    pub errors: Vec<String>,
    /// Names of signals absent from the frame (e.g. an inactive mux branch).
    pub absent: Vec<String>,
}

/// A validation issue carried in a `parse_dbc_text` response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationIssue {
    /// Severity (e.g. `warning`, `error`).
    pub severity: String,
    /// Machine-readable issue code.
    pub code: String,
    /// Human-readable detail.
    pub detail: String,
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

fn parse_enrichment(v: &Value) -> Result<Enrichment, Error> {
    // Surface a decode failure rather than silently dropping the signal — a
    // value that fails to decode signals protocol/FFI drift, and this module is
    // explicitly typed decoding.
    let signals = match v.get("signals").and_then(Value::as_object) {
        Some(m) => m
            .iter()
            .map(|(k, val)| {
                rational_from_value(val)
                    .map(|r| (k.clone(), r))
                    .map_err(|e| protocol(format!("enrichment signal {k:?}: {e}")))
            })
            .collect::<Result<Vec<_>, _>>()?,
        None => Vec::new(),
    };
    Ok(Enrichment {
        signals,
        formula_desc: str_field(v, "formula_desc"),
        enriched_reason: str_field(v, "enriched_reason"),
        core_reason: str_field(v, "core_reason"),
    })
}

fn parse_property_result(obj: &Value) -> Result<PropertyResult, Error> {
    let verdict = parse_verdict(&str_field(obj, "status"))?;
    let property_index = u32_field(obj, "property_index")?;
    let timestamp = obj.get("timestamp").and_then(Value::as_u64);
    let enrichment = obj
        .get("enrichment")
        .filter(|v| v.is_object())
        .map(parse_enrichment)
        .transpose()?;
    Ok(PropertyResult {
        property_index,
        verdict,
        reason: str_field(obj, "reason"),
        timestamp,
        enrichment,
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

/// Decode a `send_frame` response: `ack`, or a `property_batch` of verdicts.
pub(crate) fn decode_frame(raw: &str) -> Result<FrameResponse, Error> {
    let obj = parse_object(raw)?;
    if obj.get("type").and_then(Value::as_str) == Some("property_batch") {
        return Ok(FrameResponse::Verdicts(property_list(&obj)?));
    }
    Ok(FrameResponse::Ack)
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
    let names = |key: &str| -> Vec<String> {
        obj.get(key)
            .and_then(Value::as_array)
            .map(|arr| {
                arr.iter()
                    .map(|e| {
                        e.as_str()
                            .map(ToString::to_string)
                            .unwrap_or_else(|| str_field(e, "name"))
                    })
                    .collect()
            })
            .unwrap_or_default()
    };
    Ok(ExtractionResult {
        values,
        errors: names("errors"),
        absent: names("absent"),
    })
}

fn issue_list(obj: &Value) -> Vec<ValidationIssue> {
    obj.get("issues")
        .and_then(Value::as_array)
        .map(|arr| {
            arr.iter()
                .map(|w| ValidationIssue {
                    severity: str_field(w, "severity"),
                    code: str_field(w, "code"),
                    detail: str_field(w, "detail"),
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Decode a `validateDBC` (`status:"validation"`) response.
pub(crate) fn decode_validation(raw: &str) -> Result<ValidationResult, Error> {
    let obj = parse_object(raw)?;
    match obj.get("status").and_then(Value::as_str) {
        Some("validation") => Ok(ValidationResult {
            has_errors: bool_field(&obj, "has_errors")?,
            issues: issue_list(&obj),
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
