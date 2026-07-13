-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Response → JSON formatting for the streaming protocol.
--
-- Purpose: Serialize Response values to JSON for transmission to clients.
-- Split from Routing.agda (which handles request parsing and dispatch).
module Aletheia.Protocol.ResponseFormat where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map) renaming ()
open import Data.Maybe using ()
open import Data.Rational using (ℚ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Parser.Position using (Position)
-- JSON.Types (not the Protocol.JSON umbrella): this module only BUILDS
-- JSON values; the umbrella re-exports the parser, which would put this
-- serializer inside every parser-combinator change's recheck closure.
open import Aletheia.Protocol.JSON.Types using (JSON; JObject; JArray; JStringS; JNumber; JBool)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Protocol.Message using (Response; Success; Error;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse;
  ParsedDBCResponse; DBCTextResponse)
import Aletheia.Error as Err
open import Aletheia.Limits using (BoundKind; boundKindCode)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData; Warning; WarningKind; UncachedAtom)
open import Aletheia.LTL.Incremental using (formatLTLReason)
open import Aletheia.Trace.Time using (tsValue)
open import Aletheia.DBC.Types using (IssueSeverity; IsError; IsWarning;
  IssueCode; DuplicateMessageId; DuplicateSignalName; FactorZero;
  MultiplexorNotFound; MultiplexorCycle; GlobalNameCollision;
  MinExceedsMax; SignalExceedsDLC; SignalOverlap; BitLengthZero;
  DuplicateMessageName; OffsetScaleRange; EmptyMessage;
  StartBitOutOfRange; BitLengthExcessive; MultiplexorNonUnitScaling;
  DuplicateAttributeName; UnknownCommentTarget; UnknownMessageSender;
  UnknownSignalReceiver; UnknownValueDescriptionTarget;
  TextRoundTripDivergence; MultiValueMuxSelector; MuxMasterIncoherent;
  BigEndianMSBLayout; UnknownAttributeName; AttributeValueTypeMismatch;
  AttributeEnumEmpty; AttributeEnumDefaultUnstable;
  ValidationIssue)
open import Aletheia.DBC.Validator using (hasAnyError)

-- Shared header + variant-specific extras for PropertyResult JSON output.
-- Every PropertyResult variant emits the same `type`/`status`/`property_index`
-- prefix; extras carry per-variant fields (timestamp, reason, …).
mkPropertyResult : String → ℕ → List (String × JSON) → JSON
mkPropertyResult status idx extras =
  JObject (
    ("type" , JStringS "property") ∷
    ("status" , JStringS status) ∷
    ("property_index" , JNumber (ℕtoℚ idx)) ∷
    extras)

-- Format PropertyResult as JSON object
formatPropertyResult : PropertyResult → JSON
formatPropertyResult (PropertyResult.Violation idx counterex) =
  mkPropertyResult "fails" idx
    (("timestamp" , JNumber (ℕtoℚ (tsValue (CounterexampleData.timestamp counterex)))) ∷
     ("reason" , JStringS (formatLTLReason (CounterexampleData.reason counterex))) ∷
     [])
formatPropertyResult (PropertyResult.Satisfaction idx) =
  mkPropertyResult "holds" idx []
formatPropertyResult (PropertyResult.Unresolved idx reason) =
  mkPropertyResult "unresolved" idx
    (("reason" , JStringS (formatLTLReason reason)) ∷ [])

-- Per-warning JSON encoder.
-- Wire shape `{kind: string, property_index: int, detail: string}`.
formatWarningKind : WarningKind → String
formatWarningKind UncachedAtom = "uncached_atom"

formatWarning : Warning → JSON
formatWarning w =
  JObject (
    ("kind"           , JStringS (formatWarningKind (Warning.kind w))) ∷
    ("property_index" , JNumber (ℕtoℚ (Warning.propertyIndex w))) ∷
    ("detail"         , JStringS (Warning.detail w)) ∷
    [])

-- Validation issue → JSON.  Hoisted from `formatResponse (ValidationResponse …)`'s
-- where block so `formatResponse (ParsedDBCResponse …)` can reuse the same shape
-- for the warnings list it carries on success.
formatIssueSeverity : IssueSeverity → String
formatIssueSeverity IsError   = "error"
formatIssueSeverity IsWarning = "warning"

-- Validation issue codes are deliberately NOT prefixed with `validation_`
-- (e.g. `validation_duplicate_message_id`), even though the project's
-- error-code naming convention (`parse_signal_bit_length_zero`,
-- `dbc_text_parse_failure`, etc.) prefixes error codes with a domain tag.
-- Error codes share a flat `("code", JStringS ...)` JSON field with the
-- response envelope (`formatResponse (Error err)` at this module's tail),
-- so they need a domain prefix to disambiguate per Cat 5 (error message
-- consistency).  Validation issue codes live inside `issues[].code` — a
-- STRUCTURALLY NESTED field on `ValidationResponse` / `ParsedDBCResponse`
-- only — and are already namespaced by that container.  Adding a
-- `validation_` prefix would touch 21 codes here + 21 mirrors in each of
-- the three bindings (Python `IssueCode` enum, Go `IssueCode` constants,
-- C++ `IssueCode` enum) for zero disambiguation benefit at the JSON wire.
formatIssueCode : IssueCode → String
formatIssueCode DuplicateMessageId          = "duplicate_message_id"
formatIssueCode DuplicateSignalName         = "duplicate_signal_name"
formatIssueCode FactorZero                  = "factor_zero"
formatIssueCode MultiplexorNotFound         = "multiplexor_not_found"
formatIssueCode MultiplexorCycle            = "multiplexor_cycle"
formatIssueCode GlobalNameCollision         = "global_name_collision"
formatIssueCode MinExceedsMax               = "min_exceeds_max"
formatIssueCode SignalExceedsDLC            = "signal_exceeds_dlc"
formatIssueCode SignalOverlap               = "signal_overlap"
formatIssueCode BitLengthZero               = "bit_length_zero"
formatIssueCode DuplicateMessageName        = "duplicate_message_name"
formatIssueCode OffsetScaleRange            = "offset_scale_range"
formatIssueCode EmptyMessage                = "empty_message"
formatIssueCode StartBitOutOfRange          = "start_bit_out_of_range"
formatIssueCode BitLengthExcessive          = "bit_length_excessive"
formatIssueCode MultiplexorNonUnitScaling   = "multiplexor_non_unit_scaling"
formatIssueCode DuplicateAttributeName      = "duplicate_attribute_name"
formatIssueCode UnknownCommentTarget        = "unknown_comment_target"
formatIssueCode UnknownMessageSender        = "unknown_message_sender"
formatIssueCode UnknownSignalReceiver       = "unknown_signal_receiver"
formatIssueCode UnknownValueDescriptionTarget = "unknown_value_description_target"
-- E.2 route (b) slice 1 (S1.0): wire codes for the text-round-trip checker
-- diagnostics.  Total-function arms kept in lock-step with the IssueCode
-- constructors (Types.agda); wire-inert until slice 3 emits them.
formatIssueCode TextRoundTripDivergence       = "text_roundtrip_divergence"
formatIssueCode MultiValueMuxSelector         = "multi_value_mux_selector"
formatIssueCode MuxMasterIncoherent           = "mux_master_incoherent"
formatIssueCode BigEndianMSBLayout            = "big_endian_msb_layout"
formatIssueCode UnknownAttributeName          = "unknown_attribute_name"
formatIssueCode AttributeValueTypeMismatch    = "attribute_value_type_mismatch"
formatIssueCode AttributeEnumEmpty            = "attribute_enum_empty"
formatIssueCode AttributeEnumDefaultUnstable  = "attribute_enum_default_unstable"

formatValidationIssue : ValidationIssue → JSON
formatValidationIssue issue =
  JObject (
    ("severity" , JStringS (formatIssueSeverity (ValidationIssue.severity issue))) ∷
    ("code"     , JStringS (formatIssueCode (ValidationIssue.code issue))) ∷
    ("detail"   , JStringS (ValidationIssue.detail issue)) ∷
    [])

-- Per-error structured fields appended to the Error JSON envelope:
--   * `DBCTextParseErr (TrailingInput pos)` exposes `line` + `column`.
--   * `Error.InputBoundExceeded kind observed limit` (a top-level error
--     consolidating the bound checks) exposes `bound_kind` + `observed` +
--     `limit` (typed wire-error refinement; the C++ / Go / Python bindings
--     dispatch on `bound_kind` from this structured payload).
-- `WithContext` is transparent so wrappers do not hide structured payloads.
private
  boundInfoFields : BoundKind → ℕ → ℕ → List (String × JSON)
  boundInfoFields kind observed limit =
    ("bound_kind" , JStringS (boundKindCode kind)) ∷
    ("observed"   , JNumber (ℕtoℚ observed)) ∷
    ("limit"      , JNumber (ℕtoℚ limit)) ∷
    []

errorExtras : Err.Error → List (String × JSON)
-- `line`/`column` are the failure watermark (deepest position any parse
-- attempt reached — byte-exact at the first unparseable character);
-- trailing-input additionally reports where the unparseable statement
-- starts, so tools can show both the statement and the exact byte.
errorExtras (Err.DBCTextParseErr (Err.ParseFailure pos)) =
  ("line"   , JNumber (ℕtoℚ (Position.line pos))) ∷
  ("column" , JNumber (ℕtoℚ (Position.column pos))) ∷
  []
errorExtras (Err.DBCTextParseErr (Err.TrailingInput pos stmt)) =
  ("line"             , JNumber (ℕtoℚ (Position.line pos))) ∷
  ("column"           , JNumber (ℕtoℚ (Position.column pos))) ∷
  ("statement_line"   , JNumber (ℕtoℚ (Position.line stmt))) ∷
  ("statement_column" , JNumber (ℕtoℚ (Position.column stmt))) ∷
  []
errorExtras (Err.DispatchErr (Err.InvalidJSON pos)) =
  ("line"   , JNumber (ℕtoℚ (Position.line pos))) ∷
  ("column" , JNumber (ℕtoℚ (Position.column pos))) ∷
  []
errorExtras (Err.InputBoundExceeded k o l) = boundInfoFields k o l
-- A validation rejection carries the FULL issue list (errors AND warnings)
-- structurally — the same element shape as the `validation` response, so
-- bindings reuse one issue decoder. `has_errors` is trivially true on this
-- path but included so the payload is shape-compatible with that response.
errorExtras (Err.HandlerErr (Err.ValidationFailed issues)) =
  ("has_errors" , JBool (hasAnyError issues)) ∷
  ("issues"     , JArray (map formatValidationIssue issues)) ∷
  []
errorExtras (Err.HandlerErr (Err.InContext _ inner)) =
  errorExtras (Err.HandlerErr inner)
errorExtras (Err.WithContext _ inner)      = errorExtras inner
errorExtras _                              = []

-- Format Response as JSON
formatResponse : Response → JSON
formatResponse (Success msg) =
  JObject (
    ("status" , JStringS "success") ∷
    ("message" , JStringS msg) ∷
    [])
formatResponse (Error err) =
  JObject (
    ("status"  , JStringS "error") ∷
    ("code"    , JStringS (Err.errorCode err)) ∷
    ("message" , JStringS (Err.formatError err)) ∷
    errorExtras err)
formatResponse (ExtractionResultsResponse values errors absent) =
  JObject (
    ("status" , JStringS "success") ∷
    ("values" , formatSignalValues values) ∷
    ("errors" , formatErrors errors) ∷
    ("absent" , JArray (map JStringS absent)) ∷
    [])
  where
    formatSignalValues : List (String × ℚ) → JSON
    formatSignalValues vals = JArray (map formatPair vals)
      where
        formatPair : String × ℚ → JSON
        formatPair (name , value) =
          JObject (("name" , JStringS name) ∷ ("value" , JNumber value) ∷ [])

    formatErrors : List (String × String) → JSON
    formatErrors errs = JArray (map formatError errs)
      where
        formatError : String × String → JSON
        formatError (name , msg) =
          JObject (("name" , JStringS name) ∷ ("error" , JStringS msg) ∷ [])
formatResponse (PropertyResponse results) =
  -- Per-frame batch of property events.  Carries one
  -- top-level object that bindings parse as a single response, with the
  -- inner `results` array preserving source order (satisfactions that
  -- completed before a halting violation come first, then the violation).
  -- Single-event frames are still wrapped — the wire is uniformly a
  -- list, so bindings have one code path rather than two.
  JObject (
    ("type"    , JStringS "property_batch") ∷
    ("results" , JArray (map formatPropertyResult results)) ∷
    [])
formatResponse Ack =
  JObject (
    ("status" , JStringS "ack") ∷
    [])
formatResponse (Complete results warnings) =
  JObject (
    ("status"   , JStringS "complete") ∷
    ("results"  , JArray (map formatPropertyResult results)) ∷
    ("warnings" , JArray (map formatWarning warnings)) ∷
    [])
formatResponse (DBCResponse dbcJSON) =
  JObject (
    ("status" , JStringS "success") ∷
    ("dbc" , dbcJSON) ∷
    [])
formatResponse (ValidationResponse issues) =
  JObject (
    ("status"     , JStringS "validation") ∷
    ("has_errors" , JBool (hasAnyError issues)) ∷
    ("issues"     , JArray (map formatValidationIssue issues)) ∷
    [])
formatResponse (ParsedDBCResponse dbcJSON warnings) =
  JObject (
    ("status"   , JStringS "success") ∷
    ("dbc"      , dbcJSON) ∷
    ("warnings" , JArray (map formatValidationIssue warnings)) ∷
    [])
formatResponse (DBCTextResponse text) =
  JObject (
    ("status" , JStringS "success") ∷
    ("text"   , JStringS text) ∷
    [])
