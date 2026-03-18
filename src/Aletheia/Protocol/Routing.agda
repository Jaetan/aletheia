{-# OPTIONS --safe --without-K #-}

-- Request parsing and routing for the streaming protocol.
--
-- Purpose: Parse JSON requests and route to appropriate handlers.
-- Operations: parseRequest (JSON → Request), parseCommand, parseDataFrame.
-- Role: Entry point for all incoming JSON messages, used by Main.processLine.
--
-- Routing: Checks "type" field → "command" (parse command type) or "data" (parse frame).
-- Validation: All required fields checked, descriptive error messages on failure.
module Aletheia.Protocol.Routing where

open import Data.String using (String; _≟_) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ; _/_)
open import Data.Rational.Show as ℚShow using (show)
open import Data.Vec using (Vec; toList)
open import Data.Nat using (ℕ; _%_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (lookupByKey; standard-can-id-max; _>>=ₑ_)
open import Aletheia.Protocol.JSON using (JSON; JObject; JArray; JString; JNumber; JBool; lookupString; lookupNat; lookupArray; getInt)
open import Aletheia.Data.Message using (Request; CommandRequest; DataFrame; Response; Success; Error; ByteArray; ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC)
open import Aletheia.CAN.Frame using (CANFrame; Byte; CANId)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData)
open import Aletheia.DBC.Types using (IssueSeverity; IsError; IsWarning;
  IssueCode; DuplicateMessageId; DuplicateSignalName; FactorZero;
  MultiplexorNotFound; MultiplexorNotAlwaysPresent; GlobalNameCollision;
  MinExceedsMax; SignalExceedsDLC; SignalOverlap; BitLengthZero;
  DuplicateMessageName; DLCOutOfRange; OffsetScaleRange; EmptyMessage;
  StartBitOutOfRange; BitLengthExcessive; ValidationIssue)
open import Aletheia.DBC.Validator using (hasAnyError)

-- ============================================================================
-- JSON → REQUEST PARSING
-- ============================================================================

-- Parse a JSON array as a list of bytes
parseByteArray : List JSON → Maybe (List ℕ)
parseByteArray [] = just []
parseByteArray (jn ∷ rest) = do
  n ← getInt jn  -- Extract integer from JSON (rational must have denominator 1)
  extractNat n rest
  where
    extractNat : ℤ → List JSON → Maybe (List ℕ)
    extractNat (+ nℕ) rest = do
      restParsed ← parseByteArray rest
      just (nℕ ∷ restParsed)
    extractNat -[1+ _ ] _ = nothing  -- Negative number

-- Convert List ℕ to Vec Byte 8 (if length is exactly 8)
listToVec8 : List ℕ → Maybe (Vec Byte 8)
listToVec8 (n₀ ∷ n₁ ∷ n₂ ∷ n₃ ∷ n₄ ∷ n₅ ∷ n₆ ∷ n₇ ∷ []) =
  just (toByte n₀ Data.Vec.∷ toByte n₁ Data.Vec.∷ toByte n₂ Data.Vec.∷ toByte n₃ Data.Vec.∷
        toByte n₄ Data.Vec.∷ toByte n₅ Data.Vec.∷ toByte n₆ Data.Vec.∷ toByte n₇ Data.Vec.∷ Data.Vec.[])
  where
    toByte : ℕ → Byte
    toByte n = n % 256  -- _%_ returns ℕ (O(1) via remInt), not Fin n
listToVec8 _ = nothing  -- Wrong length

-- ============================================================================
-- COMMAND PARSERS
-- ============================================================================

-- Parse ParseDBC command
tryParseDBC : List (String × JSON) → String ⊎ StreamCommand
tryParseDBC obj with lookupByKey "dbc" obj
... | nothing = inj₁ "ParseDBC: missing 'dbc' field"
... | just dbc = inj₂ (ParseDBC dbc)

-- Parse SetProperties command
trySetProperties : List (String × JSON) → String ⊎ StreamCommand
trySetProperties obj with lookupArray "properties" obj
... | nothing = inj₁ "SetProperties: missing 'properties' field"
... | just props = inj₂ (SetProperties props)

-- Parse StartStream command
tryStartStream : List (String × JSON) → String ⊎ StreamCommand
tryStartStream _ = inj₂ StartStream

-- Parse BuildFrame command
tryBuildFrame : List (String × JSON) → String ⊎ StreamCommand
tryBuildFrame obj with lookupByKey "canId" obj
... | nothing = inj₁ "BuildFrame: missing 'canId' field"
... | just canIdJSON with lookupArray "signals" obj
...   | nothing = inj₁ "BuildFrame: missing 'signals' array"
...   | just signals = inj₂ (BuildFrame canIdJSON signals)

-- Parse ExtractAllSignals command
tryExtractAllSignals : List (String × JSON) → String ⊎ StreamCommand
tryExtractAllSignals obj =
  getCanId >>=ₑ λ canIdJSON →
  getDataArray >>=ₑ λ bytesJSON →
  parseBytes bytesJSON >>=ₑ λ byteList →
  convertToVec byteList >>=ₑ λ bytes →
  inj₂ (ExtractAllSignals canIdJSON bytes)
  where
    getCanId : String ⊎ JSON
    getCanId with lookupByKey "canId" obj
    ... | nothing = inj₁ "ExtractAllSignals: missing 'canId' field"
    ... | just x = inj₂ x

    getDataArray : String ⊎ (List JSON)
    getDataArray with lookupArray "data" obj
    ... | nothing = inj₁ "ExtractAllSignals: missing 'data' array"
    ... | just x = inj₂ x

    parseBytes : List JSON → String ⊎ (List ℕ)
    parseBytes bytesJSON with parseByteArray bytesJSON
    ... | nothing = inj₁ "ExtractAllSignals: failed to parse byte array"
    ... | just x = inj₂ x

    convertToVec : List ℕ → String ⊎ (Vec Byte 8)
    convertToVec byteList with listToVec8 byteList
    ... | nothing = inj₁ "ExtractAllSignals: expected 8 bytes"
    ... | just x = inj₂ x

-- Parse UpdateFrame command
tryUpdateFrame : List (String × JSON) → String ⊎ StreamCommand
tryUpdateFrame obj =
  getCanId >>=ₑ λ canIdJSON →
  getDataArray >>=ₑ λ bytesJSON →
  parseBytes bytesJSON >>=ₑ λ byteList →
  convertToVec byteList >>=ₑ λ bytes →
  getSignals >>=ₑ λ signals →
  inj₂ (UpdateFrame canIdJSON bytes signals)
  where
    getCanId : String ⊎ JSON
    getCanId with lookupByKey "canId" obj
    ... | nothing = inj₁ "UpdateFrame: missing 'canId' field"
    ... | just x = inj₂ x

    getDataArray : String ⊎ (List JSON)
    getDataArray with lookupArray "data" obj
    ... | nothing = inj₁ "UpdateFrame: missing 'data' array"
    ... | just x = inj₂ x

    parseBytes : List JSON → String ⊎ (List ℕ)
    parseBytes bytesJSON with parseByteArray bytesJSON
    ... | nothing = inj₁ "UpdateFrame: failed to parse byte array"
    ... | just x = inj₂ x

    convertToVec : List ℕ → String ⊎ (Vec Byte 8)
    convertToVec byteList with listToVec8 byteList
    ... | nothing = inj₁ "UpdateFrame: expected 8 bytes"
    ... | just x = inj₂ x

    getSignals : String ⊎ (List JSON)
    getSignals with lookupArray "signals" obj
    ... | nothing = inj₁ "UpdateFrame: missing 'signals' array"
    ... | just x = inj₂ x

-- Parse EndStream command
tryEndStream : List (String × JSON) → String ⊎ StreamCommand
tryEndStream _ = inj₂ EndStream

-- Parse ValidateDBC command
tryValidateDBC : List (String × JSON) → String ⊎ StreamCommand
tryValidateDBC obj with lookupByKey "dbc" obj
... | nothing = inj₁ "ValidateDBC: missing 'dbc' field"
... | just dbc = inj₂ (ValidateDBC dbc)

-- Dispatch table for command parsers
commandDispatchTable : List (String × (List (String × JSON) → String ⊎ StreamCommand))
commandDispatchTable =
  ("parseDBC" , tryParseDBC) ∷
  ("setProperties" , trySetProperties) ∷
  ("startStream" , tryStartStream) ∷
  ("buildFrame" , tryBuildFrame) ∷
  ("extractAllSignals" , tryExtractAllSignals) ∷
  ("updateFrame" , tryUpdateFrame) ∷
  ("endStream" , tryEndStream) ∷
  ("validateDBC" , tryValidateDBC) ∷
  []

-- Dispatch using table lookup
dispatchCommand : String → List (String × JSON) → String ⊎ StreamCommand
dispatchCommand cmdType obj with lookupByKey cmdType commandDispatchTable
... | nothing = inj₁ ("Unknown command: " ++ₛ cmdType)
... | just parser = parser obj

-- Parse StreamCommand from JSON object (returns error message on failure)
parseCommand : List (String × JSON) → String ⊎ StreamCommand
parseCommand obj with lookupString "command" obj
... | nothing = inj₁ "Missing 'command' field"
... | just cmdType = dispatchCommand cmdType obj

-- Parse data frame from JSON object
-- Returns detailed error messages on failure (inj₁) or parsed frame (inj₂)
parseDataFrame : List (String × JSON) → Maybe (String ⊎ (ℕ × CANFrame))
parseDataFrame obj with lookupNat "timestamp" obj
... | nothing = just (inj₁ "Data frame: missing or invalid 'timestamp' field")
... | just timestamp with lookupNat "id" obj
...   | nothing = just (inj₁ "Data frame: missing or invalid 'id' field")
...   | just canId with lookupArray "data" obj
...     | nothing = just (inj₁ "Data frame: missing 'data' array")
...     | just bytesJSON with parseByteArray bytesJSON
...       | nothing = just (inj₁ "Data frame: failed to parse byte array")
...       | just byteList with listToVec8 byteList
...         | nothing = just (inj₁ "Data frame: expected 8 bytes")
...         | just bytes = buildFrame timestamp canId bytes
  where
    buildFrame : ℕ → ℕ → Vec Byte 8 → Maybe (String ⊎ (ℕ × CANFrame))
    buildFrame timestamp canId bytes =
      let frame = record
            { id = CANId.Standard (canId % standard-can-id-max)
            ; dlc = 8
            ; payload = bytes
            }
      in just (inj₂ (timestamp , frame))

-- Parse Request from JSON
parseRequest : JSON → Maybe Request
parseRequest (JObject obj) with lookupString "type" obj
... | nothing = nothing
... | just msgType = routeByType msgType obj
  where
    tryCommand : List (String × JSON) → Maybe Request
    tryCommand obj with parseCommand obj
    ... | inj₁ _ = nothing
    ... | inj₂ cmd = just (CommandRequest cmd)

    tryDataFrame : List (String × JSON) → Maybe Request
    tryDataFrame obj with parseDataFrame obj
    ... | nothing = nothing
    ... | just (inj₁ _) = nothing
    ... | just (inj₂ (timestamp , frame)) = just (DataFrame timestamp frame)

    routeByType : String → List (String × JSON) → Maybe Request
    routeByType msgType obj =
      if ⌊ msgType ≟ "command" ⌋ then tryCommand obj
      else if ⌊ msgType ≟ "data" ⌋ then tryDataFrame obj
      else nothing
parseRequest _ = nothing  -- Not a JSON object

-- ============================================================================
-- RESPONSE → JSON FORMATTING
-- ============================================================================

-- Convert Vec Byte 8 to JSON array
bytesToJSON : Vec Byte 8 → JSON
bytesToJSON bytes = JArray (map (λ n → JNumber ((Data.Integer.+ n) / 1)) (toList bytes))

-- Format PropertyResult as JSON object
formatPropertyResult : PropertyResult → JSON
formatPropertyResult (PropertyResult.Violation idx counterex) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "violation") ∷
    ("property_index" , JNumber ((Data.Integer.+ idx) / 1)) ∷
    ("timestamp" , JNumber ((Data.Integer.+ (CounterexampleData.timestamp counterex)) / 1)) ∷
    ("reason" , JString (CounterexampleData.reason counterex)) ∷
    [])
formatPropertyResult (PropertyResult.Satisfaction idx) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "satisfaction") ∷
    ("property_index" , JNumber ((Data.Integer.+ idx) / 1)) ∷
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
          JObject (("name" , JString name) ∷ ("value" , JString (ℚShow.show value)) ∷ [])

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
