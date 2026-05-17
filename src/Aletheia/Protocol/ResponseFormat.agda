{-# OPTIONS --safe --without-K #-}

-- Response → JSON formatting for the streaming protocol.
--
-- Purpose: Serialize Response values to JSON for transmission to clients.
-- Split from Routing.agda (which handles request parsing and dispatch).
module Aletheia.Protocol.ResponseFormat where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Parser.Combinators using (Position)
open import Aletheia.Protocol.JSON using (JSON; JObject; JArray; JStringS; JNumber; JBool)
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

-- R21 cluster 1 — AGDA-D-12.1 scaffolding: per-warning JSON encoder.
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

-- R5-C2 — DO NOT RE-RAISE IN REVIEW.
--
-- A reviewer may suggest prefixing every code below with `validation_`
-- (e.g. `validation_duplicate_message_id`) for parity with the project's
-- error-code naming convention (`parse_signal_bit_length_zero`,
-- `dbc_text_parse_failure`, etc.).  DO NOT do this.  Error codes share a
-- flat `("code", JStringS ...)` JSON field with the response envelope
-- (`formatResponse (Error err)` at this module's tail), so they need a
-- domain prefix to disambiguate per Cat 5 (error message consistency).
-- Validation issue codes live inside `issues[].code` — a STRUCTURALLY
-- NESTED field on `ValidationResponse` / `ParsedDBCResponse` only — and
-- are already namespaced by that container.  Adding a `validation_`
-- prefix would touch 21 codes here + 21 mirrors in each of the three
-- bindings (Python `IssueCode` enum, Go `IssueCode` constants, C++
-- `IssueCode` enum) for zero disambiguation benefit at the JSON wire.
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

formatValidationIssue : ValidationIssue → JSON
formatValidationIssue issue =
  JObject (
    ("severity" , JStringS (formatIssueSeverity (ValidationIssue.severity issue))) ∷
    ("code"     , JStringS (formatIssueCode (ValidationIssue.code issue))) ∷
    ("detail"   , JStringS (ValidationIssue.detail issue)) ∷
    [])

-- Per-error structured fields appended to the Error JSON envelope:
--   * `DBCTextParseErr (TrailingInput pos)` exposes `line` + `column`.
--   * `Error.InputBoundExceeded kind observed limit` (top-level after
--     R19 cluster 14 / AGDA-C-6.2 consolidation) exposes `bound_kind` +
--     `observed` + `limit` (AGDA-D-13.4 phase 2a/2b typed wire-error
--     refinement; the C++ / Go / Python bindings dispatch on `bound_kind`
--     from this structured payload).
-- `WithContext` is transparent so wrappers do not hide structured payloads.
private
  boundInfoFields : BoundKind → ℕ → ℕ → List (String × JSON)
  boundInfoFields kind observed limit =
    ("bound_kind" , JStringS (boundKindCode kind)) ∷
    ("observed"   , JNumber (ℕtoℚ observed)) ∷
    ("limit"      , JNumber (ℕtoℚ limit)) ∷
    []

errorExtras : Err.Error → List (String × JSON)
errorExtras (Err.DBCTextParseErr (Err.TrailingInput pos)) =
  ("line"   , JNumber (ℕtoℚ (Position.line pos))) ∷
  ("column" , JNumber (ℕtoℚ (Position.column pos))) ∷
  []
errorExtras (Err.InputBoundExceeded k o l) = boundInfoFields k o l
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
formatResponse (PropertyResponse result) =
  formatPropertyResult result
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
