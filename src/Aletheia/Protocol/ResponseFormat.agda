{-# OPTIONS --safe --without-K #-}

-- Response → JSON formatting for the streaming protocol.
--
-- Purpose: Serialize Response values to JSON for transmission to clients.
-- Split from Routing.agda (which handles request parsing and dispatch).
module Aletheia.Protocol.ResponseFormat where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Bool using (Bool)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec; toList)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Protocol.JSON using (JSON; JObject; JArray; JString; JNumber; JBool; ℕtoℚ)
open import Aletheia.Protocol.Message using (Response; Success; Error; ByteArray;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse)
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData)
open import Aletheia.DBC.Types using (IssueSeverity; IsError; IsWarning;
  IssueCode; DuplicateMessageId; DuplicateSignalName; FactorZero;
  MultiplexorNotFound; MultiplexorNotAlwaysPresent; GlobalNameCollision;
  MinExceedsMax; SignalExceedsDLC; SignalOverlap; BitLengthZero;
  DuplicateMessageName; DLCOutOfRange; OffsetScaleRange; EmptyMessage;
  StartBitOutOfRange; BitLengthExcessive; ValidationIssue)
open import Aletheia.DBC.Validator using (hasAnyError)

-- Convert Vec Byte n to JSON array
bytesToJSON : ∀ {n} → Vec Byte n → JSON
bytesToJSON bytes = JArray (map (λ n → JNumber (ℕtoℚ n)) (toList bytes))

-- Format PropertyResult as JSON object
formatPropertyResult : PropertyResult → JSON
formatPropertyResult (PropertyResult.Violation idx counterex) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "violation") ∷
    ("property_index" , JNumber (ℕtoℚ idx)) ∷
    ("timestamp" , JNumber (ℕtoℚ (CounterexampleData.timestamp counterex))) ∷
    ("reason" , JString (CounterexampleData.reason counterex)) ∷
    [])
formatPropertyResult (PropertyResult.Satisfaction idx) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "satisfaction") ∷
    ("property_index" , JNumber (ℕtoℚ idx)) ∷
    [])
formatPropertyResult PropertyResult.StreamComplete =
  JObject (
    ("type" , JString "complete") ∷
    ("status" , JString "stream_ended") ∷
    [])

-- Format Response as JSON
formatResponse : Response → JSON
formatResponse (Success msg) =
  JObject (
    ("status" , JString "success") ∷
    ("message" , JString msg) ∷
    [])
formatResponse (Error reason) =
  JObject (
    ("status" , JString "error") ∷
    ("message" , JString reason) ∷
    [])
formatResponse (ByteArray bytes) =
  JObject (
    ("status" , JString "success") ∷
    ("data" , bytesToJSON bytes) ∷
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
    formatIssueCode MultiplexorNotAlwaysPresent = "multiplexor_not_always_present"
    formatIssueCode GlobalNameCollision         = "global_name_collision"
    formatIssueCode MinExceedsMax               = "min_exceeds_max"
    formatIssueCode SignalExceedsDLC            = "signal_exceeds_dlc"
    formatIssueCode SignalOverlap               = "signal_overlap"
    formatIssueCode BitLengthZero               = "bit_length_zero"
    formatIssueCode DuplicateMessageName        = "duplicate_message_name"
    formatIssueCode DLCOutOfRange               = "dlc_out_of_range"
    formatIssueCode OffsetScaleRange            = "offset_scale_range"
    formatIssueCode EmptyMessage                = "empty_message"
    formatIssueCode StartBitOutOfRange          = "start_bit_out_of_range"
    formatIssueCode BitLengthExcessive          = "bit_length_excessive"

    formatValidationIssue : ValidationIssue → JSON
    formatValidationIssue issue =
      JObject (
        ("severity" , JString (formatIssueSeverity (ValidationIssue.severity issue))) ∷
        ("code"     , JString (formatIssueCode (ValidationIssue.code issue))) ∷
        ("detail"   , JString (ValidationIssue.detail issue)) ∷
        [])
