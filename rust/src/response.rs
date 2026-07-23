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

/// One signal's extraction error: the signal name and the kernel-minted reason
/// string (e.g. "value out of bounds: 16383.75 not in [0, 8000]"), identical on
/// the JSON and binary paths. Mirrors the Go `SignalError` / Python
/// `errors: Mapping[str, str]` — the JSON path emits each error as
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
///
/// The vocabulary is minted by the kernel and grows with kernel features, so
/// this enum is `#[non_exhaustive]`: matches outside this crate carry a `_`
/// arm, and a new kernel code is not a breaking change. Version-skew note: a
/// code arrives as [`IssueCode::Unknown`] while this crate predates it and as
/// a named variant once the crate knows it — so logic that must be stable
/// across crate upgrades should key on [`IssueCode::as_str`] (the wire string
/// for named and unknown codes alike), never on `Unknown`'s payload.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
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
    /// `format_dbc_text`: re-parsing the emitted text does not reproduce the input DBC.
    TextRoundtripDivergence,
    /// A mux signal is present for multiple selector values (not expressible in `.dbc` text).
    MultiValueMuxSelector,
    /// The mux master signal's presence is inconsistent with its slaves.
    MuxMasterIncoherent,
    /// A `BA_` assignment/default references an attribute with no `BA_DEF_` declaration.
    UnknownAttributeName,
    /// An attribute value's type does not match its `BA_DEF_` declaration.
    AttributeValueTypeMismatch,
    /// An enum attribute (`BA_DEF_ ENUM`) declares no values.
    AttributeEnumEmpty,
    /// An enum attribute's default index does not resolve back to itself.
    AttributeEnumDefaultUnstable,
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
            "text_roundtrip_divergence" => IssueCode::TextRoundtripDivergence,
            "multi_value_mux_selector" => IssueCode::MultiValueMuxSelector,
            "mux_master_incoherent" => IssueCode::MuxMasterIncoherent,
            "unknown_attribute_name" => IssueCode::UnknownAttributeName,
            "attribute_value_type_mismatch" => IssueCode::AttributeValueTypeMismatch,
            "attribute_enum_empty" => IssueCode::AttributeEnumEmpty,
            "attribute_enum_default_unstable" => IssueCode::AttributeEnumDefaultUnstable,
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
            IssueCode::TextRoundtripDivergence => "text_roundtrip_divergence",
            IssueCode::MultiValueMuxSelector => "multi_value_mux_selector",
            IssueCode::MuxMasterIncoherent => "mux_master_incoherent",
            IssueCode::UnknownAttributeName => "unknown_attribute_name",
            IssueCode::AttributeValueTypeMismatch => "attribute_value_type_mismatch",
            IssueCode::AttributeEnumEmpty => "attribute_enum_empty",
            IssueCode::AttributeEnumDefaultUnstable => "attribute_enum_default_unstable",
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

/// The success result of [`Client::format_dbc_text`](crate::Client::format_dbc_text):
/// the `.dbc` text image plus its `wfTextIssues` diagnostics (warning-severity,
/// advisory). `format_dbc_text` is always strict — it returns this only when the
/// emitted text provably re-parses to the input DBC — so `issues` may be non-empty
/// even on a proven round-trip. A divergent DBC yields [`Error::TextRoundtripFailed`]
/// instead.
///
/// [`Error::TextRoundtripFailed`]: crate::Error::TextRoundtripFailed
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DbcText {
    /// The `.dbc` file text.
    pub text: String,
    /// The advisory `wfTextIssues` diagnostics (warning-severity).
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
        // Lift the structured input_bound_exceeded triple into the typed
        // Error::InputBoundExceeded when it is present and well-typed (parity with
        // Go's *InputBoundExceededError, C++'s make_json_error, and Python's
        // build_error_response). A malformed or partial triple degrades to the
        // generic Error::Core rather than being reported as a bound error.
        if code == "input_bound_exceeded" {
            if let (Some(bound_kind), Some(observed), Some(limit)) = (
                value.get("bound_kind").and_then(Value::as_str),
                value.get("observed").and_then(Value::as_u64),
                value.get("limit").and_then(Value::as_u64),
            ) {
                return Err(Error::InputBoundExceeded {
                    code,
                    bound_kind: bound_kind.to_string(),
                    observed,
                    limit,
                });
            }
        }
        // Lift the structured handler_validation_failed envelope into the typed
        // Error::ValidationFailed when the `has_errors` flag and `issues` array
        // are present and well-typed (each element the exact shape of a
        // "validation" response issue). A missing or malformed payload —
        // including any single ill-typed issue element — degrades to the
        // generic Error::Core rather than being reported as a typed validation
        // failure; the legacy `message` text is carried unchanged either way.
        if code == "handler_validation_failed" {
            if let (Some(has_errors), Some(arr)) = (
                value.get("has_errors").and_then(Value::as_bool),
                value.get("issues").and_then(Value::as_array),
            ) {
                if let Ok(issues) = arr.iter().map(decode_issue).collect::<Result<Vec<_>, _>>() {
                    return Err(Error::ValidationFailed {
                        code,
                        message,
                        has_errors,
                        issues,
                    });
                }
            }
        }
        // Lift the structured handler_text_roundtrip_failed envelope into the
        // typed Error::TextRoundtripFailed (format_dbc_text round-trip refusal),
        // same shape and degrade rule as the handler_validation_failed lift
        // above.
        if code == "handler_text_roundtrip_failed" {
            if let (Some(has_errors), Some(arr)) = (
                value.get("has_errors").and_then(Value::as_bool),
                value.get("issues").and_then(Value::as_array),
            ) {
                if let Ok(issues) = arr.iter().map(decode_issue).collect::<Result<Vec<_>, _>>() {
                    return Err(Error::TextRoundtripFailed {
                        code,
                        message,
                        has_errors,
                        issues,
                    });
                }
            }
        }
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

/// Resolve a wire signal index to its name via the per-CAN-id name cache,
/// falling back to `signal_<idx>` for an index past the cache (matching Go's
/// `signalNameByIndex`).
fn name_by_index(names: &[String], idx: u16) -> String {
    names
        .get(idx as usize)
        .cloned()
        .unwrap_or_else(|| format!("signal_{idx}"))
}

fn read_u16_ne(bytes: &[u8]) -> u16 {
    u16::from_ne_bytes(bytes.try_into().expect("caller passes a 2-byte slice"))
}

fn read_u32_ne(bytes: &[u8]) -> u32 {
    u32::from_ne_bytes(bytes.try_into().expect("caller passes a 4-byte slice"))
}

/// Decode the packed binary extraction buffer (the hot path) into the same
/// [`ExtractionResult`] the JSON path produces.
///
/// Wire format -- see `Aletheia.Main.Binary` (processExtractBin), the canonical
/// source. Byte order is the host's NATIVE order (Haskell `Storable` poke); the
/// kernel and every binding run on one host, so `from_ne_bytes` is the faithful
/// read (identical to little-endian on the supported x86_64 / aarch64 hosts):
///
/// ```text
/// header:  u16 nValues, u16 nErrors, u16 nAbsent, u32 reasonBytes = 10 bytes
/// values:  nValues x (u16 index, i64 numerator, i64 denominator)  = 18 bytes
/// errors:  nErrors x (u16 index, u8 code)                         =  3 bytes
/// offsets: (nErrors + 1) x u32 -- cumulative byte offsets into reasons;
///          always present (the single entry 0 when nErrors == 0), and
///          off[0] == 0, monotone non-decreasing, off[nErrors] == reasonBytes
///          (all three verified before any reason is sliced)
/// reasons: reasonBytes of UTF-8; error i's reason = bytes [off[i], off[i+1])
/// absent:  nAbsent x (u16 index)                                  =  2 bytes
/// ```
///
/// The reason strings are kernel-minted and byte-identical to what the JSON
/// path surfaces for the same error, so [`SignalError::reason`] carries the
/// wire reason verbatim. The u8 code is transported for machine consumption
/// but never surfaced (the public result has no code field -- binary/JSON
/// parity), and an unknown code is not rejected: the reason is authoritative.
///
/// Pure (bytes + names in, result out; no FFI) so the offset arithmetic is unit-
/// and mutation-testable -- the real-FFI happy path is excluded from mutation.
/// A malformed buffer (short header, wrong total length, violated offset
/// invariants, non-UTF-8 reason bytes, non-positive denominator) is rejected
/// rather than panicked-on or silently truncated, matching the Go decoder and
/// the JSON path's strictness.
pub(crate) fn decode_extraction_bin(
    buf: &[u8],
    names: &[String],
) -> Result<ExtractionResult, Error> {
    if buf.len() < 10 {
        return Err(protocol("extraction binary buffer too short for header"));
    }
    let nvals = read_u16_ne(&buf[0..2]) as usize;
    let nerrs = read_u16_ne(&buf[2..4]) as usize;
    let nabss = read_u16_ne(&buf[4..6]) as usize;
    let reason_bytes = read_u32_ne(&buf[6..10]) as usize;

    // Validate the exact total up front: header + all sections must consume the
    // whole buffer, so a truncated OR trailing-byte buffer is rejected before any
    // slicing (no panic, no silent drop). u16 counts x fixed strides plus a u32
    // reason-blob length sum below 2^33, which cannot overflow usize on the
    // supported 64-bit hosts.
    let expected = 10 + 18 * nvals + 3 * nerrs + 4 * (nerrs + 1) + reason_bytes + 2 * nabss;
    if buf.len() != expected {
        return Err(protocol(format!(
            "extraction binary buffer length {} != expected {expected} \
             (nValues={nvals}, nErrors={nerrs}, nAbsent={nabss}, reasonBytes={reason_bytes})",
            buf.len()
        )));
    }

    let (values_bytes, rest) = buf[10..].split_at(18 * nvals);
    let (errors_bytes, rest) = rest.split_at(3 * nerrs);
    let (offsets_bytes, rest) = rest.split_at(4 * (nerrs + 1));
    let (reasons_bytes, absent_bytes) = rest.split_at(reason_bytes);

    let mut values = Vec::with_capacity(nvals);
    for chunk in values_bytes.chunks_exact(18) {
        let idx = read_u16_ne(&chunk[0..2]);
        let num = i64::from_ne_bytes(chunk[2..10].try_into().expect("8-byte slice"));
        let den = i64::from_ne_bytes(chunk[10..18].try_into().expect("8-byte slice"));
        let name = name_by_index(names, idx);
        // A successful extraction never has den <= 0; treat it as a corrupt buffer
        // (mirrors the JSON path's Rational::new rejection and the Go decoder).
        if den <= 0 {
            return Err(protocol(format!(
                "non-positive denominator {den} for extracted signal {name:?} (index {idx})"
            )));
        }
        values.push(SignalValue {
            name,
            value: Rational::new(num, den)?,
        });
    }

    // The offsets table must satisfy all three wire invariants before any
    // reason is sliced; together they make every [off[i], off[i+1]) slice
    // in-bounds, so the reason slicing below cannot panic.
    let offsets: Vec<u32> = offsets_bytes.chunks_exact(4).map(read_u32_ne).collect();
    if offsets[0] != 0 {
        return Err(protocol(format!(
            "extraction binary reason offsets must start at 0, got {}",
            offsets[0]
        )));
    }
    if let Some(w) = offsets.windows(2).find(|w| w[0] > w[1]) {
        return Err(protocol(format!(
            "extraction binary reason offsets not monotone non-decreasing: {} > {}",
            w[0], w[1]
        )));
    }
    if offsets[nerrs] as usize != reason_bytes {
        return Err(protocol(format!(
            "extraction binary reason offsets end {} != reasonBytes {reason_bytes}",
            offsets[nerrs]
        )));
    }

    let mut errors = Vec::with_capacity(nerrs);
    for (chunk, span) in errors_bytes.chunks_exact(3).zip(offsets.windows(2)) {
        let idx = read_u16_ne(&chunk[0..2]);
        // chunk[2] is the u8 error code (kernel SSOT: extractionErrorCodeToℕ in
        // Aletheia.CAN.BatchExtraction) -- transported, never surfaced: the wire
        // reason below is authoritative, so an unknown code is not rejected.
        let name = name_by_index(names, idx);
        let reason = std::str::from_utf8(&reasons_bytes[span[0] as usize..span[1] as usize])
            .map_err(|e| {
                protocol(format!(
                    "extraction binary reason for signal {name:?} (index {idx}) \
                     is not valid UTF-8: {e}"
                ))
            })?
            .to_string();
        errors.push(SignalError { name, reason });
    }

    let mut absent = Vec::with_capacity(nabss);
    for chunk in absent_bytes.chunks_exact(2) {
        absent.push(name_by_index(names, read_u16_ne(chunk)));
    }

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
pub(crate) fn decode_format_text(raw: &str) -> Result<DbcText, Error> {
    let obj = parse_object(raw)?;
    match obj.get("status").and_then(Value::as_str) {
        Some("success") => {
            let text = obj
                .get("text")
                .and_then(Value::as_str)
                .ok_or_else(|| protocol("formatDBCText response missing 'text'"))?
                .to_string();
            // The wfTextIssues diagnostics (warning-severity, advisory).  Absent
            // → empty; a present-but-non-array `issues`, or a non-object element,
            // is a protocol error (not silently dropped to empty).
            let issues = match obj.get("issues") {
                None | Some(Value::Null) => Vec::new(),
                Some(Value::Array(arr)) => arr
                    .iter()
                    .map(decode_issue)
                    .collect::<Result<Vec<_>, _>>()?,
                Some(_) => {
                    return Err(protocol("formatDBCText response 'issues' must be an array"))
                }
            };
            Ok(DbcText { text, issues })
        }
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
        // Display renders the bound triple (covers the Display arm).
        assert!(
            err.to_string()
                .contains("nesting_depth 65 exceeds limit 64"),
            "Display: {err}"
        );
        match err {
            Error::InputBoundExceeded {
                code,
                bound_kind,
                observed,
                limit,
            } => {
                assert_eq!(code, "input_bound_exceeded");
                assert_eq!(bound_kind, "nesting_depth");
                assert_eq!(observed, 65);
                assert_eq!(limit, 64);
            }
            other => panic!("expected Error::InputBoundExceeded, got {other:?}"),
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
}
