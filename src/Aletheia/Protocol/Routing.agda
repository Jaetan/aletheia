{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Routing where

open import Data.String using (String; _≟_) renaming (_++_ to _++S_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ)
open import Data.Rational using (ℚ)
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
open import Aletheia.Protocol.JSON
open import Aletheia.Data.Message
open import Aletheia.CAN.Frame using (CANFrame; Byte; CANId)
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
parseCommand : List (String × JSON) → Maybe StreamCommand
parseCommand obj with lookupString "command" obj
... | nothing = nothing
... | just cmdType with ⌊ cmdType ≟ "parseDBC" ⌋
...   | true = do
        dbc ← lookup "dbc" obj
        just (ParseDBC dbc)
...   | false with ⌊ cmdType ≟ "setProperties" ⌋
...     | true = do
            props ← lookupArray "properties" obj
            just (SetProperties props)  -- props is already List JSON
...     | false with ⌊ cmdType ≟ "startStream" ⌋
...       | true = just StartStream
...       | false with ⌊ cmdType ≟ "encode" ⌋
...         | true = do
              msgName ← lookupString "message" obj
              sigName ← lookupString "signal" obj
              value ← lookupInt "value" obj
              just (Encode msgName sigName value)
...         | false with ⌊ cmdType ≟ "decode" ⌋
...           | true = do
                msgName ← lookupString "message" obj
                sigName ← lookupString "signal" obj
                bytesJSON ← lookupArray "bytes" obj
                byteList ← parseByteArray bytesJSON
                bytes ← listToVec8 byteList
                just (Decode msgName sigName bytes)
...           | false with ⌊ cmdType ≟ "endStream" ⌋
...             | true = just EndStream
...             | false = nothing  -- Unknown command

-- Parse data frame from JSON object (returns timestamp and frame)
-- Returns Maybe String for error messages during debugging
parseDataFrameWithTrace : List (String × JSON) → Maybe (String ⊎ (ℕ × CANFrame))
parseDataFrameWithTrace obj with lookup "timestamp" obj
... | nothing = just (inj₁ "TRACE_DF1a: timestamp field not found")
... | just timestampJSON with getRational timestampJSON
...   | nothing = just (inj₁ "TRACE_DF1b: timestamp field is not a rational")
...   | just timestampRat with getIntDebug timestampJSON
...     | nothing = just (inj₁ ("TRACE_DF1c_DEBUG: getIntDebug returned nothing (impossible!)"))
...     | just debugMsg with getInt timestampJSON
...       | nothing = just (inj₁ ("TRACE_DF1c: getInt failed: " ++S debugMsg))
...       | just timestampInt with getNat timestampJSON
...         | nothing = just (inj₁ ("TRACE_DF1d: getNat returned nothing but getInt succeeded: " ++S debugMsg))
...         | just timestamp with lookupNat "id" obj
...           | nothing = just (inj₁ "TRACE_DF2: missing id")
...       | just canId with lookupArray "data" obj
...         | nothing = just (inj₁ "TRACE_DF3: missing data array")
...         | just bytesJSON with parseByteArray bytesJSON
...           | nothing = just (inj₁ "TRACE_DF4: parseByteArray failed")
...           | just byteList with listToVec8 byteList
...             | nothing = just (inj₁ "TRACE_DF5: listToVec8 failed (wrong length)")
...             | just bytes = buildFrame timestamp canId bytes
  where
    buildFrame : ℕ → ℕ → Vec Byte 8 → Maybe (String ⊎ (ℕ × CANFrame))
    buildFrame timestamp canId bytes =
      let frame = record
            { id = CANId.Standard (canId mod 2048)
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
        { id = CANId.Standard (canId mod 2048)
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

-- Convert byte to natural
byteToNat : Byte → ℕ
byteToNat b = toℕ b

-- Convert Vec Byte 8 to JSON array
bytesToJSON : Vec Byte 8 → JSON
bytesToJSON bytes = JArray (map (λ n → JNumber ((Data.Integer.+ n) / 1)) (map byteToNat (toList bytes)))
  where open import Data.Rational using (_/_)

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
  where open import Data.Rational using (_/_)
formatPropertyResult (PropertyResult.Satisfaction idx) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "satisfaction") ∷
    ("property_index" , JNumber ((Data.Integer.+ idx) / 1)) ∷
    [])
  where open import Data.Rational using (_/_)
formatPropertyResult (PropertyResult.Pending idx result) =
  JObject (
    ("type" , JString "property") ∷
    ("status" , JString "pending") ∷
    ("property_index" , JNumber ((Data.Integer.+ idx) / 1)) ∷
    ("result" , JBool result) ∷
    [])
  where open import Data.Rational using (_/_)
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
formatResponse (SignalValue val) =
  JObject (
    ("status" , JString "success") ∷
    ("value" , JString (ℚShow.show val)) ∷
    [])
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
