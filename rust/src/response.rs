// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed decoding of the JSON responses the core returns.
//!
//! Every reader requires each key the kernel writes and reads each place by
//! kind only, refusing what the kernel never writes there in the one form of
//! `reply_shape`: the ranges and the tags are the kernel's, proven of every
//! reply. An issue's severity and code, an error reply's code, a property
//! result's type and status and a stream warning's kind hold a member of their
//! set or are refused at their place, a word outside it quoted.

use crate::error::{BoundRefusal, Error};
use crate::reply_shape::{
    came, field_bool, field_member, field_natural, field_objects, field_rational, field_status,
    field_string, field_strings, field_word, read_reply, refusal, ReplyPath, ReplyStatus, ROOT,
    STRING,
};
use crate::types::Rational;
use crate::wire_json::{self, Kind, Object};
pub use error_codes::ErrorCode;

mod error_codes;

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

/// The kind of a [`StreamWarning`]: the kernel writes `uncached_atom`, and a
/// reply holding another kind is refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WarningKind {
    /// A property asked about a signal no frame of the stream carried, so its
    /// atom was never cached.
    UncachedAtom,
}

/// A diagnostic warning emitted at `end_stream` (e.g. an atom never cached).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamWarning {
    /// What the warning says of its property.
    pub kind: WarningKind,
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

/// The severity of a validation issue: the kernel writes `error` or `warning`,
/// and a reply holding another word there is refused. Mirrors the Python / Go /
/// C++ typed severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IssueSeverity {
    /// A structural issue that prevents correct operation.
    Error,
    /// A non-fatal advisory.
    Warning,
}

impl IssueSeverity {
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
/// ADT and the Python / Go / C++ vocabularies: a reply holding a code outside
/// them is refused.
///
/// The vocabulary is minted by the kernel and grows with kernel features, so
/// this enum is `#[non_exhaustive]`: matches outside this crate carry a `_`
/// arm, and a new kernel code is not a breaking change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum IssueCode {
    /// A CAN id two or more messages share; one issue names them all.
    DuplicateMessageId,
    /// Two signals in the same message share a name.
    DuplicateSignalName,
    /// A signal's scale factor is zero.
    FactorZero,
    /// A multiplexed signal's multiplexor was not found.
    MultiplexorNotFound,
    /// A multiplexor cycle was detected.
    MultiplexorCycle,
    /// A signal name signals of two or more messages share; one issue names those
    /// messages.
    GlobalNameCollision,
    /// A signal's declared minimum exceeds its maximum.
    MinExceedsMax,
    /// A signal's bit range exceeds the message DLC.
    SignalExceedsDlc,
    /// Two signals overlap in the same message.
    SignalOverlap,
    /// A signal has zero bit length.
    BitLengthZero,
    /// A name two or more messages share; one issue names them all by CAN id.
    DuplicateMessageName,
    /// A signal's offset/scale combination produces values outside its
    /// declared range.
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
    /// A signal's declared minimum or maximum lies beyond the values its bits
    /// carry after scaling.
    RangeExceedsBits,
    /// A value description's key is no raw value of its signal's bits, the
    /// signedness and the bit length deciding.
    ValueDescriptionKeyOutOfRange,
}

impl IssueCode {
    /// The [`IssueCode`] a wire code string names, `None` for a string that
    /// names none.
    #[must_use]
    pub fn from_wire(s: &str) -> Option<Self> {
        Some(match s {
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
            "range_exceeds_bits" => IssueCode::RangeExceedsBits,
            "value_description_key_out_of_range" => IssueCode::ValueDescriptionKeyOutOfRange,
            _ => return None,
        })
    }

    /// The canonical wire string for this code.
    #[must_use]
    pub fn as_str(self) -> &'static str {
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
            IssueCode::RangeExceedsBits => "range_exceeds_bits",
            IssueCode::ValueDescriptionKeyOutOfRange => "value_description_key_out_of_range",
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

// ── The error envelope ──────────────────────────────────────────────────────

/// The keys of a bound refusal's triple.
const BOUND_TRIPLE_KEYS: [&str; 3] = ["bound_kind", "observed", "limit"];

/// The two spellings of an acknowledgement: the kernel writes the compact one
/// and a mock the spaced one.
const ACK_COMPACT: &str = r#"{"status":"ack"}"#;
const ACK_SPACED: &str = r#"{"status": "ack"}"#;

/// Whether `raw` is an acknowledgement in one of its two spellings: almost
/// every answer is, and comparing bytes is cheaper than reading them.
fn is_ack(raw: &str) -> bool {
    raw == ACK_COMPACT || raw == ACK_SPACED
}

/// Read a reply whose status is `want` or `error`, and lift an error into its
/// typed [`Error`]. Every typed decoder opens with it, so a reply that is
/// malformed, an error, or not the answer to the command asked is refused in
/// one place.
pub(crate) fn decode_reply(raw: &str, want: ReplyStatus) -> Result<Object<'_>, Error> {
    let reply = read_reply(raw)?;
    let status = field_status(&reply, ROOT, "status", &[want, ReplyStatus::Error])?;
    if status == ReplyStatus::Error {
        return Err(error_status(&reply));
    }
    Ok(reply)
}

/// The error a binary-output entry's error envelope carries, read as the JSON
/// path reads one: text that is not an envelope, or an envelope that is not an
/// error, is refused in the one form of every reply place.
pub(crate) fn error_envelope(raw: &str) -> Error {
    match read_reply(raw) {
        Ok(reply) => error_status(&reply),
        Err(refused) => refused,
    }
}

/// The error an error envelope carries, always an error: the envelope's
/// status is `error` and its code and message are strings, and where the code
/// carries a payload of its own the typed variant carries it, [`Error::Core`]
/// the code and message otherwise. A place of the envelope holding what the
/// kernel never writes there is refused.
fn error_status(reply: &Object<'_>) -> Error {
    match lift_error(reply) {
        Ok(lifted) | Err(lifted) => lifted,
    }
}

/// The typed error of an error envelope, or the refusal of one of its places.
/// An envelope of any code holding part of a bound refusal's triple holds it
/// whole, with a string `field` if it names one, and a bound refusal holds
/// the triple always; a validation or round-trip refusal holds its
/// `has_errors` flag and its issues whole.
fn lift_error(reply: &Object<'_>) -> Result<Error, Error> {
    field_status(reply, ROOT, "status", &[ReplyStatus::Error])?;
    let code = field_member(reply, ROOT, "code", "an error code", ErrorCode::from_wire)?;
    let message = field_string(reply, ROOT, "message")?.into_owned();
    match read_bound_triple(reply)? {
        Some(triple) => {
            let field = bound_field(reply)?;
            if code == ErrorCode::InputBoundExceeded {
                return Ok(Error::InputBoundExceeded(Box::new(BoundRefusal {
                    code,
                    message,
                    bound_kind: triple.kind,
                    observed: triple.observed,
                    limit: triple.limit,
                    field,
                    located: None,
                })));
            }
        }
        None if code == ErrorCode::InputBoundExceeded => {
            return Err(refusal(
                ROOT.at("bound_kind"),
                STRING,
                came(reply, "bound_kind"),
            ));
        }
        None => {}
    }
    if code == ErrorCode::HandlerValidationFailed {
        let (has_errors, issues) = issues_payload(reply)?;
        return Ok(Error::ValidationFailed {
            code,
            message,
            has_errors,
            issues,
        });
    }
    if code == ErrorCode::HandlerTextRoundtripFailed {
        let (has_errors, issues) = issues_payload(reply)?;
        return Ok(Error::TextRoundtripFailed {
            code,
            message,
            has_errors,
            issues,
        });
    }
    Ok(Error::Core { code, message })
}

/// The bound a refusal says was crossed: its kind, the size observed and the
/// limit.
struct BoundTriple {
    kind: String,
    observed: u128,
    limit: u128,
}

/// A bound refusal's triple, `None` when the envelope holds none of its keys.
/// An envelope holding any of them holds all three, each broken key refused at
/// its place; the kernel proves the observed size and the limit positive, so
/// they are read without a range check, and the kind is read as the string it
/// is.
fn read_bound_triple(reply: &Object<'_>) -> Result<Option<BoundTriple>, Error> {
    if BOUND_TRIPLE_KEYS.iter().all(|key| reply.get(key).is_none()) {
        return Ok(None);
    }
    Ok(Some(BoundTriple {
        kind: field_string(reply, ROOT, "bound_kind")?.into_owned(),
        observed: field_natural(reply, ROOT, "observed")?,
        limit: field_natural(reply, ROOT, "limit")?,
    }))
}

/// The part of the input a bound refusal names, `None` when it names none.
fn bound_field(reply: &Object<'_>) -> Result<Option<String>, Error> {
    if reply.get("field").is_none() {
        return Ok(None);
    }
    field_string(reply, ROOT, "field").map(|field| Some(field.into_owned()))
}

/// The `has_errors` flag and the issues an envelope carries, a validation
/// reply or a DBC refusal, both of which the kernel writes on it.
fn issues_payload(reply: &Object<'_>) -> Result<(bool, Vec<ValidationIssue>), Error> {
    let has_errors = field_bool(reply, ROOT, "has_errors")?;
    let issues = read_issues(reply, "issues")?;
    Ok((has_errors, issues))
}

/// The validation issues at `key` of a reply's root: the validation reply's,
/// the warnings of a parsed DBC and the issues of a DBC refusal.
pub(crate) fn read_issues(reply: &Object<'_>, key: &str) -> Result<Vec<ValidationIssue>, Error> {
    field_objects(reply, ROOT, key, read_issue)
}

/// One validation issue at `path`: its code, one of the [`IssueCode`]s, its
/// detail and its severity, one of the [`IssueSeverity`] words.
fn read_issue(issue: &Object<'_>, path: ReplyPath<'_>) -> Result<ValidationIssue, Error> {
    let code = field_member(issue, path, "code", "an issue code", IssueCode::from_wire)?;
    let detail = field_string(issue, path, "detail")?.into_owned();
    let severity = severity(field_word(issue, path, "severity", &["error", "warning"])?);
    Ok(ValidationIssue {
        severity,
        code,
        detail,
    })
}

/// An issue's severity, `warning` its last arm.
fn severity(word: &str) -> IssueSeverity {
    match word {
        "error" => IssueSeverity::Error,
        _ => IssueSeverity::Warning,
    }
}

// ── Command answers ─────────────────────────────────────────────────────────

/// Decode the answer to a command that carries nothing but its success:
/// `set_properties` and `start_stream`.
pub(crate) fn decode_success(raw: &str) -> Result<(), Error> {
    decode_reply(raw, ReplyStatus::Success).map(drop)
}

/// Decode the answer to an error or remote event: the kernel resolves both to
/// an acknowledgement, the only status either carries.
pub(crate) fn decode_event_ack(raw: &str) -> Result<(), Error> {
    if is_ack(raw) {
        return Ok(());
    }
    decode_reply(raw, ReplyStatus::Ack).map(drop)
}

/// Decode a `send_frame` answer: an acknowledgement when nothing happened, a
/// batch of property events when something did, or a typed error. A batch
/// carries no status of its own, each of its events carrying one, and is told
/// by its type.
pub(crate) fn decode_frame(raw: &str) -> Result<FrameResponse, Error> {
    if is_ack(raw) {
        return Ok(FrameResponse::Ack);
    }
    let reply = read_reply(raw)?;
    if reply.get("status").is_some() {
        let status = field_status(
            &reply,
            ROOT,
            "status",
            &[ReplyStatus::Ack, ReplyStatus::Error],
        )?;
        if status == ReplyStatus::Ack {
            return Ok(FrameResponse::Ack);
        }
        return Err(error_status(&reply));
    }
    field_word(&reply, ROOT, "type", &["property_batch"])?;
    let results = field_objects(&reply, ROOT, "results", read_property_event)?;
    Ok(FrameResponse::Verdicts(results))
}

/// One event of a frame's batch at `path`: its verdict, the timestamp of the
/// frame that broke the property on a failure, and a reason on every verdict
/// but a hold.
fn read_property_event(event: &Object<'_>, path: ReplyPath<'_>) -> Result<PropertyResult, Error> {
    let mut result = read_verdict(event, path)?;
    if result.verdict == Verdict::Fails {
        result.timestamp = Some(field_natural(event, path, "timestamp")?);
    }
    if result.verdict != Verdict::Holds {
        result.reason = field_string(event, path, "reason")?.into_owned();
    }
    Ok(result)
}

/// Decode an `end_stream` answer: one final verdict per property, and the
/// warnings the kernel raised.
pub(crate) fn decode_stream(raw: &str) -> Result<StreamResult, Error> {
    let reply = decode_reply(raw, ReplyStatus::Complete)?;
    let results = field_objects(&reply, ROOT, "results", read_property_result)?;
    let warnings = field_objects(&reply, ROOT, "warnings", read_stream_warning)?;
    Ok(StreamResult { results, warnings })
}

/// One end-of-stream verdict at `path`. A failure carries the timestamp of the
/// frame that broke the property, and an unresolved verdict a timestamp only
/// where its key holds one: an absent or null key is no timestamp. Every
/// verdict but a hold carries a reason.
fn read_property_result(result: &Object<'_>, path: ReplyPath<'_>) -> Result<PropertyResult, Error> {
    let mut read = read_verdict(result, path)?;
    if read.verdict == Verdict::Holds {
        return Ok(read);
    }
    let timestamped = result
        .get("timestamp")
        .is_some_and(|timestamp| wire_json::kind(timestamp) != Kind::Null);
    if read.verdict == Verdict::Fails || timestamped {
        read.timestamp = Some(field_natural(result, path, "timestamp")?);
    }
    read.reason = field_string(result, path, "reason")?.into_owned();
    Ok(read)
}

/// The type, the status and the property index every verdict carries, the
/// index read directly; the reason and the timestamp are the caller's to read.
fn read_verdict(result: &Object<'_>, path: ReplyPath<'_>) -> Result<PropertyResult, Error> {
    field_word(result, path, "type", &["property"])?;
    let status = field_word(result, path, "status", &["fails", "holds", "unresolved"])?;
    let property_index = field_natural(result, path, "property_index")?;
    // Enrichment is not on the wire: the verified core writes only the raw
    // `reason`, and the client computes [`Enrichment`] from the registered
    // formulas and the last-known signal values (see `crate::enrich`).
    Ok(PropertyResult {
        property_index,
        verdict: verdict(status),
        reason: String::new(),
        timestamp: None,
        enrichment: None,
    })
}

/// A verdict's status, `unresolved` its last arm.
fn verdict(word: &str) -> Verdict {
    match word {
        "fails" => Verdict::Fails,
        "holds" => Verdict::Holds,
        _ => Verdict::Unresolved,
    }
}

/// One end-of-stream warning at `path`: its kind, its property's index and
/// its detail.
fn read_stream_warning(warning: &Object<'_>, path: ReplyPath<'_>) -> Result<StreamWarning, Error> {
    field_word(warning, path, "kind", &["uncached_atom"])?;
    Ok(StreamWarning {
        kind: WarningKind::UncachedAtom,
        property_index: field_natural(warning, path, "property_index")?,
        detail: field_string(warning, path, "detail")?.into_owned(),
    })
}

/// Decode an `extract_signals` answer on the JSON path: each extracted value
/// with its signal's name, each extraction error with the kernel's reason,
/// and the names of the signals the frame does not carry.
pub(crate) fn decode_extraction(raw: &str) -> Result<ExtractionResult, Error> {
    let reply = decode_reply(raw, ReplyStatus::Success)?;
    let values = field_objects(&reply, ROOT, "values", read_signal_value)?;
    let errors = field_objects(&reply, ROOT, "errors", read_signal_error)?;
    let absent = field_strings(&reply, ROOT, "absent")?;
    Ok(ExtractionResult {
        values,
        errors,
        absent,
    })
}

/// One extracted value at `path`: the signal's name and its exact value.
fn read_signal_value(value: &Object<'_>, path: ReplyPath<'_>) -> Result<SignalValue, Error> {
    Ok(SignalValue {
        name: field_string(value, path, "name")?.into_owned(),
        value: field_rational(value, path, "value")?,
    })
}

/// One extraction error at `path`: the signal's name and the kernel's reason.
fn read_signal_error(error: &Object<'_>, path: ReplyPath<'_>) -> Result<SignalError, Error> {
    Ok(SignalError {
        name: field_string(error, path, "name")?.into_owned(),
        reason: field_string(error, path, "error")?.into_owned(),
    })
}

/// The name of the signal at `index` of its message's signal table, read
/// directly: the kernel proves every index it writes within the table.
fn signal_name(names: &[String], index: u16) -> String {
    names[usize::from(index)].clone()
}

fn read_u16_le(bytes: &[u8]) -> u16 {
    u16::from_le_bytes(bytes.try_into().expect("caller passes a 2-byte slice"))
}

fn read_u32_le(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes.try_into().expect("caller passes a 4-byte slice"))
}

/// The 128-bit magnitude a 16-byte slice holds: its low `u64`, then its high
/// `u64`, each little-endian, which is the slice read as one little-endian `u128`.
fn read_u128_le(bytes: &[u8]) -> u128 {
    u128::from_le_bytes(bytes.try_into().expect("caller passes a 16-byte slice"))
}

/// Decode the packed binary extraction buffer (the hot path) into the same
/// [`ExtractionResult`] the JSON path produces.
///
/// Wire format -- see `Aletheia.Main.Binary` (processExtractBin), the canonical
/// source. Every multi-byte field is little-endian, as Go's reader reads it:
///
/// ~~~text
/// header:  u16 nValues, u16 nErrors, u16 nAbsent, u32 reasonBytes = 10 bytes
/// values:  nValues x (u16 index, u8 negative, u128 numerator,
///          u128 denominator)                                      = 35 bytes
/// errors:  nErrors x (u16 index, u8 code)                         =  3 bytes
/// offsets: (nErrors + 1) x u32 -- cumulative byte offsets into reasons;
///          always present (the single entry 0 when nErrors == 0), and
///          off[0] == 0, monotone non-decreasing, off[nErrors] == reasonBytes
///          (all three verified before any reason is sliced)
/// reasons: reasonBytes of UTF-8; error i's reason = bytes [off[i], off[i+1])
/// absent:  nAbsent x (u16 index)                                  =  2 bytes
/// ~~~
///
/// Each u128 is its low u64 then its high u64, and any sign byte but 0 is
/// negative. A value is the kernel's rational, reduced over a positive
/// denominator by the kernel's proof, so it is stored as written, a zero
/// unsigned as the JSON path reads it. Each signal index names its signal in
/// `names` directly, the kernel proving it within the message's signal table.
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
/// invariants, non-UTF-8 reason bytes) is rejected rather than panicked-on or
/// silently truncated, matching the Go decoder.
pub(crate) fn decode_extraction_bin(
    buf: &[u8],
    names: &[String],
) -> Result<ExtractionResult, Error> {
    if buf.len() < 10 {
        return Err(protocol("extraction binary buffer too short for header"));
    }
    let nvals = read_u16_le(&buf[0..2]) as usize;
    let nerrs = read_u16_le(&buf[2..4]) as usize;
    let nabss = read_u16_le(&buf[4..6]) as usize;
    let reason_bytes = read_u32_le(&buf[6..10]) as usize;

    // Validate the exact total up front: header + all sections must consume the
    // whole buffer, so a truncated OR trailing-byte buffer is rejected before any
    // slicing (no panic, no silent drop). u16 counts x fixed strides plus a u32
    // reason-blob length sum below 2^33, which cannot overflow usize on the
    // supported 64-bit hosts.
    let expected = 10 + 35 * nvals + 3 * nerrs + 4 * (nerrs + 1) + reason_bytes + 2 * nabss;
    if buf.len() != expected {
        return Err(protocol(format!(
            "extraction binary buffer length {} != expected {expected} \
             (nValues={nvals}, nErrors={nerrs}, nAbsent={nabss}, reasonBytes={reason_bytes})",
            buf.len()
        )));
    }

    let (values_bytes, rest) = buf[10..].split_at(35 * nvals);
    let (errors_bytes, rest) = rest.split_at(3 * nerrs);
    let (offsets_bytes, rest) = rest.split_at(4 * (nerrs + 1));
    let (reasons_bytes, absent_bytes) = rest.split_at(reason_bytes);

    let mut values = Vec::with_capacity(nvals);
    for chunk in values_bytes.as_chunks::<35>().0 {
        values.push(SignalValue {
            name: signal_name(names, read_u16_le(&chunk[0..2])),
            value: Rational::from_kernel(
                chunk[2] != 0,
                read_u128_le(&chunk[3..19]),
                read_u128_le(&chunk[19..35]),
            ),
        });
    }

    // The offsets table must satisfy all three wire invariants before any
    // reason is sliced; together they make every [off[i], off[i+1]) slice
    // in-bounds, so the reason slicing below cannot panic.
    let offsets: Vec<u32> = offsets_bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|chunk| read_u32_le(chunk))
        .collect();
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
    for (chunk, span) in errors_bytes
        .as_chunks::<3>()
        .0
        .iter()
        .zip(offsets.windows(2))
    {
        let idx = read_u16_le(&chunk[0..2]);
        // chunk[2] is the u8 error code (kernel SSOT: extractionErrorCodeToℕ in
        // Aletheia.CAN.BatchExtraction) -- transported, never surfaced: the wire
        // reason below is authoritative, so an unknown code is not rejected.
        let name = signal_name(names, idx);
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
    for chunk in absent_bytes.as_chunks::<2>().0 {
        absent.push(signal_name(names, read_u16_le(chunk)));
    }

    Ok(ExtractionResult {
        values,
        errors,
        absent,
    })
}

/// Decode a `validateDBC` (`status:"validation"`) response.
pub(crate) fn decode_validation(raw: &str) -> Result<ValidationResult, Error> {
    let reply = decode_reply(raw, ReplyStatus::Validation)?;
    let (has_errors, issues) = issues_payload(&reply)?;
    Ok(ValidationResult { has_errors, issues })
}

/// Decode a `formatDBCText` (`status:"success"`) response into the `.dbc` text
/// and its advisory `wfTextIssues` diagnostics.
pub(crate) fn decode_format_text(raw: &str) -> Result<DbcText, Error> {
    let reply = decode_reply(raw, ReplyStatus::Success)?;
    let text = field_string(&reply, ROOT, "text")?.into_owned();
    let issues = read_issues(&reply, "issues")?;
    Ok(DbcText { text, issues })
}

#[cfg(test)]
mod tag_tests;
#[cfg(test)]
mod tests;
