{-# OPTIONS --safe --without-K #-}

-- Response → JSON formatting for the streaming protocol.
--
-- Purpose: Serialize Response values to JSON for transmission to clients.
-- Split from Routing.agda (which handles request parsing and dispatch).
module Aletheia.Protocol.ResponseFormat where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Rational using (ℚ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Protocol.JSON using (JSON; JObject; JArray; JString; JNumber; JBool)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Protocol.Message using (Response; Success; Error;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse)
import Aletheia.Error as Err
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData)
open import Aletheia.LTL.Incremental using (formatLTLReason)
open import Aletheia.Trace.Time using (tsValue)
open import Aletheia.DBC.Types using (IssueSeverity; IsError; IsWarning;
  IssueCode; DuplicateMessageId; DuplicateSignalName; FactorZero;
  MultiplexorNotFound; MultiplexorCycle; GlobalNameCollision;
  MinExceedsMax; SignalExceedsDLC; SignalOverlap; BitLengthZero;
  DuplicateMessageName; OffsetScaleRange; EmptyMessage;
  StartBitOutOfRange; BitLengthExcessive; MultiplexorNonUnitScaling;
  DuplicateAttributeName; UnknownCommentTarget; UnknownMessageSender;
  UnknownSignalReceiver;
  ValidationIssue)
open import Aletheia.DBC.Validator using (hasAnyError)

-- Shared header + variant-specific extras for PropertyResult JSON output.
-- Every PropertyResult variant emits the same `type`/`status`/`property_index`
-- prefix; extras carry per-variant fields (timestamp, reason, …).
mkPropertyResult : String → ℕ → List (String × JSON) → JSON
mkPropertyResult status idx extras =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString status) ∷
    ("property_index" , JNumber (ℕtoℚ idx)) ∷
    extras)

-- Format PropertyResult as JSON object
formatPropertyResult : PropertyResult → JSON
formatPropertyResult (PropertyResult.Violation idx counterex) =
  mkPropertyResult "fails" idx
    (("timestamp" , JNumber (ℕtoℚ (tsValue (CounterexampleData.timestamp counterex)))) ∷
     ("reason" , JString (formatLTLReason (CounterexampleData.reason counterex))) ∷
     [])
formatPropertyResult (PropertyResult.Satisfaction idx) =
  mkPropertyResult "holds" idx []
formatPropertyResult (PropertyResult.Unresolved idx reason) =
  mkPropertyResult "unresolved" idx
    (("reason" , JString (formatLTLReason reason)) ∷ [])

-- Format Response as JSON
formatResponse : Response → JSON
formatResponse (Success msg) =
  JObject (
    ("status" , JString "success") ∷
    ("message" , JString msg) ∷
    [])
formatResponse (Error err) =
  JObject (
    ("status"  , JString "error") ∷
    ("code"    , JString (Err.errorCode err)) ∷
    ("message" , JString (Err.formatError err)) ∷
    [])
formatResponse (ExtractionResultsResponse values errors absent) =
  JObject (
    ("status" , JString "success") ∷
    ("values" , formatSignalValues values) ∷
    ("errors" , formatErrors errors) ∷
    ("absent" , JArray (map JString absent)) ∷
    [])
  where
    formatSignalValues : List (String × ℚ) → JSON
    formatSignalValues vals = JArray (map formatPair vals)
      where
        formatPair : String × ℚ → JSON
        formatPair (name , value) =
          JObject (("name" , JString name) ∷ ("value" , JNumber value) ∷ [])

    formatErrors : List (String × String) → JSON
    formatErrors errs = JArray (map formatError errs)
      where
        formatError : String × String → JSON
        formatError (name , msg) =
          JObject (("name" , JString name) ∷ ("error" , JString msg) ∷ [])
formatResponse (PropertyResponse result) =
  formatPropertyResult result
formatResponse Ack =
  JObject (
    ("status" , JString "ack") ∷
    [])
formatResponse (Complete results) =
  JObject (
    ("status" , JString "complete") ∷
    ("results" , JArray (map formatPropertyResult results)) ∷
    [])
formatResponse (DBCResponse dbcJSON) =
  JObject (
    ("status" , JString "success") ∷
    ("dbc" , dbcJSON) ∷
    [])
formatResponse (ValidationResponse issues) =
  JObject (
    ("status"     , JString "validation") ∷
    ("has_errors" , JBool (hasAnyError issues)) ∷
    ("issues"     , JArray (map formatValidationIssue issues)) ∷
    [])
  where
    formatIssueSeverity : IssueSeverity → String
    formatIssueSeverity IsError   = "error"
    formatIssueSeverity IsWarning = "warning"

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

    formatValidationIssue : ValidationIssue → JSON
    formatValidationIssue issue =
      JObject (
        ("severity" , JString (formatIssueSeverity (ValidationIssue.severity issue))) ∷
        ("code"     , JString (formatIssueCode (ValidationIssue.code issue))) ∷
        ("detail"   , JString (ValidationIssue.detail issue)) ∷
        [])
