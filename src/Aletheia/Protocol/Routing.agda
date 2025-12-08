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

open import Data.String using (String; _≟_) renaming (_++_ to _++S_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ)
open import Data.Rational using (ℚ; _/_)
open import Data.Rational.Show as ℚShow using (show)
open import Data.Vec using (Vec; toList)
open import Data.Nat using (ℕ; _≤?_; _<_; s≤s; z≤n; _≤_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Nat.Show as ℕShow using (show)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (lookupByKey; standard-can-id-max)
open import Aletheia.Protocol.JSON
open import Aletheia.Data.Message
open import Aletheia.CAN.Frame using (CANFrame; Byte; CANId)
open import Aletheia.CAN.Endianness using (byteToℕ)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData)

-- ============================================================================
-- JSON → REQUEST PARSING
-- ============================================================================

-- Parse a list of JSON values as strings
parseStringList : List JSON → Maybe (List String)
parseStringList [] = just []
parseStringList (JString s ∷ rest) = do
  restParsed ← parseStringList rest
  just (s ∷ restParsed)
parseStringList (_ ∷ _) = nothing  -- Non-string in list

-- Parse a JSON array as a list of bytes
parseByteArray : List JSON → Maybe (List ℕ)
parseByteArray [] = just []
parseByteArray (jn ∷ rest) = do
  n ← getInt jn  -- Extract integer from JSON (rational must have denominator 1)
  extractNat n rest
  where
    open import Data.Integer using (+_; -[1+_])
    extractNat : ℤ → List JSON → Maybe (List ℕ)
    extractNat (+ nℕ) rest = do
      restParsed ← parseByteArray rest
      just (nℕ ∷ restParsed)
    extractNat -[1+ _ ] _ = nothing  -- Negative number

-- Convert List ℕ to Vec Byte 8 (if length is exactly 8)
listToVec8 : List ℕ → Maybe (Vec Byte 8)
listToVec8 (n₀ ∷ n₁ ∷ n₂ ∷ n₃ ∷ n₄ ∷ n₅ ∷ n₆ ∷ n₇ ∷ []) =
  just (toFin n₀ Data.Vec.∷ toFin n₁ Data.Vec.∷ toFin n₂ Data.Vec.∷ toFin n₃ Data.Vec.∷
        toFin n₄ Data.Vec.∷ toFin n₅ Data.Vec.∷ toFin n₆ Data.Vec.∷ toFin n₇ Data.Vec.∷ Data.Vec.[])
  where
    toFin : ℕ → Byte
    toFin n = n mod 256  -- _mod_ : ℕ → (n : ℕ) {n≢0 : NonZero n} → Fin n
listToVec8 _ = nothing  -- Wrong length

-- Parse StreamCommand from JSON object
parseCommandWithTrace : List (String × JSON) → String ⊎ StreamCommand
parseCommandWithTrace obj with lookupString "command" obj
... | nothing = inj₁ "Missing 'command' field"
... | just cmdType = dispatchCommand cmdType obj
  where
    -- Helper parsers for each command type
    tryParseDBC : List (String × JSON) → String ⊎ StreamCommand
    tryParseDBC obj with lookupByKey "dbc" obj
    ... | nothing = inj₁ "ParseDBC: missing 'dbc' field"
    ... | just dbc = inj₂ (ParseDBC dbc)

    trySetProperties : List (String × JSON) → String ⊎ StreamCommand
    trySetProperties obj with lookupArray "properties" obj
    ... | nothing = inj₁ "SetProperties: missing 'properties' field"
    ... | just props = inj₂ (SetProperties props)

    tryStartStream : List (String × JSON) → String ⊎ StreamCommand
    tryStartStream _ = inj₂ StartStream

    -- BATCH SIGNAL OPERATIONS (Phase 2B.1)

    tryBuildFrame : List (String × JSON) → String ⊎ StreamCommand
    tryBuildFrame obj with lookupByKey "canId" obj
    ... | nothing = inj₁ "BuildFrame: missing 'canId' field"
    ... | just canIdJSON with lookupArray "signals" obj
    ...   | nothing = inj₁ "BuildFrame: missing 'signals' array"
    ...   | just signals = inj₂ (BuildFrame canIdJSON signals)

    tryExtractAllSignals : List (String × JSON) → String ⊎ StreamCommand
    tryExtractAllSignals obj with lookupByKey "canId" obj
    ... | nothing = inj₁ "ExtractAllSignals: missing 'canId' field"
    ... | just canIdJSON with lookupArray "data" obj
    ...   | nothing = inj₁ "ExtractAllSignals: missing 'data' array"
    ...   | just bytesJSON with parseByteArray bytesJSON
    ...     | nothing = inj₁ "ExtractAllSignals: failed to parse byte array"
    ...     | just byteList with listToVec8 byteList
    ...       | nothing = inj₁ "ExtractAllSignals: expected 8 bytes"
    ...       | just bytes = inj₂ (ExtractAllSignals canIdJSON bytes)

    tryUpdateFrame : List (String × JSON) → String ⊎ StreamCommand
    tryUpdateFrame obj with lookupByKey "canId" obj
    ... | nothing = inj₁ "UpdateFrame: missing 'canId' field"
    ... | just canIdJSON with lookupArray "data" obj
    ...   | nothing = inj₁ "UpdateFrame: missing 'data' array"
    ...   | just bytesJSON with parseByteArray bytesJSON
    ...     | nothing = inj₁ "UpdateFrame: failed to parse byte array"
    ...     | just byteList with listToVec8 byteList
    ...       | nothing = inj₁ "UpdateFrame: expected 8 bytes"
    ...       | just bytes with lookupArray "signals" obj
    ...         | nothing = inj₁ "UpdateFrame: missing 'signals' array"
    ...         | just signals = inj₂ (UpdateFrame canIdJSON bytes signals)

    tryEndStream : List (String × JSON) → String ⊎ StreamCommand
    tryEndStream _ = inj₂ EndStream

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
      []

    -- Dispatch using table lookup
    dispatchCommand : String → List (String × JSON) → String ⊎ StreamCommand
    dispatchCommand cmdType obj with lookupByKey cmdType commandDispatchTable
    ... | nothing = inj₁ ("Unknown command: " ++S cmdType)
    ... | just parser = parser obj

-- Parse StreamCommand from JSON object
parseCommand : List (String × JSON) → Maybe StreamCommand
parseCommand obj with parseCommandWithTrace obj
... | inj₁ _ = nothing
... | inj₂ cmd = just cmd

-- Parse data frame from JSON object (returns timestamp and frame)
-- Returns error messages for debugging
parseDataFrameWithTrace : List (String × JSON) → Maybe (String ⊎ (ℕ × CANFrame))
parseDataFrameWithTrace obj with lookupNat "timestamp" obj
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
            { id = CANId.Standard (canId mod standard-can-id-max)
            ; dlc = 8 mod 9  -- DLC = 8 (fixed for now)
            ; payload = bytes
            }
      in just (inj₂ (timestamp , frame))

-- Original parseDataFrame without traces
parseDataFrame : List (String × JSON) → Maybe (ℕ × CANFrame)
parseDataFrame obj = do
  timestamp ← lookupNat "timestamp" obj
  canId ← lookupNat "id" obj
  bytesJSON ← lookupArray "data" obj
  byteList ← parseByteArray bytesJSON
  bytes ← listToVec8 byteList
  let frame = record
        { id = CANId.Standard (canId mod standard-can-id-max)
        ; dlc = 8 mod 9  -- DLC = 8 (fixed for now)
        ; payload = bytes
        }
  just (timestamp , frame)

-- Parse Request from JSON
parseRequest : JSON → Maybe Request
parseRequest (JObject obj) with lookupString "type" obj
... | nothing = nothing
... | just msgType with ⌊ msgType ≟ "command" ⌋
...   | true = do
        cmd ← parseCommand obj
        just (CommandRequest cmd)
...   | false with ⌊ msgType ≟ "data" ⌋
...     | true = do
          (timestamp , frame) ← parseDataFrame obj
          just (DataFrame timestamp frame)
...     | false = nothing  -- Unknown message type
parseRequest _ = nothing  -- Not a JSON object

-- ============================================================================
-- RESPONSE → JSON FORMATTING
-- ============================================================================

-- Convert Vec Byte 8 to JSON array
-- Note: Uses byteToℕ from CAN.Endianness to avoid duplication
bytesToJSON : Vec Byte 8 → JSON
bytesToJSON bytes = JArray (map (λ n → JNumber ((Data.Integer.+ n) / 1)) (map byteToℕ (toList bytes)))

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
formatPropertyResult (PropertyResult.Pending idx result) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "pending") ∷
    ("property_index" , JNumber ((Data.Integer.+ idx) / 1)) ∷
    ("result" , JBool result) ∷
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
formatResponse Complete =
  JObject (
    ("status" , JString "complete") ∷
    [])
