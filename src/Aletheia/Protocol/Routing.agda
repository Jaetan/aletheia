{-# OPTIONS --safe --without-K #-}

-- Command parsing for the streaming protocol.
--
-- Purpose: Parse JSON commands and dispatch to appropriate handlers.
-- Operations: parseCommand (JSON → StreamCommand).
-- Role: Parses the "command" field from JSON objects, used by Main.processJSONLine.
-- Validation: All required fields checked, descriptive error messages on failure.
module Aletheia.Protocol.Routing where

open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc; _%_; _<ᵇ_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Aletheia.Prelude using (lookupByKey; standard-can-id-max; extended-can-id-max; _>>=ₑ_)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupBool; lookupNat; lookupArray; getInt)
open import Aletheia.Protocol.Message using (StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC; FormatDBC)
open import Aletheia.CAN.Frame using (CANFrame; Byte; CANId; Standard; Extended)
open import Aletheia.CAN.DLC using (dlcToBytes)

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

-- Convert List ℕ to Vec Byte n (if length is exactly n)
listToVec : (n : ℕ) → List ℕ → Maybe (Vec Byte n)
listToVec zero    []       = just Data.Vec.[]
listToVec zero    (_ ∷ _)  = nothing
listToVec (suc n) []       = nothing
listToVec (suc n) (x ∷ xs) =
  listToVec n xs >>= λ rest →
  just ((x % 256) Data.Vec.∷ rest)

-- ============================================================================
-- COMMAND PARSERS
-- ============================================================================

private
  -- Lift Maybe to String ⊎ A with an error message on Nothing
  require : ∀ {A : Set} → String → Maybe A → String ⊎ A
  require msg nothing  = inj₁ msg
  require _   (just x) = inj₂ x

  -- Validate DLC ≤ 15 (max CAN-FD DLC code)
  requireValidDLC : String → ℕ → String ⊎ ℕ
  requireValidDLC ctx dlc with dlc ≤? 15
  ... | yes _ = inj₂ dlc
  ... | no  _ = inj₁ (ctx ++ₛ ": DLC exceeds maximum value of 15")

  -- Parse CAN ID from a named ℕ field and optional "extended" (Bool) field
  parseCANIdField : String → String → List (String × JSON) → String ⊎ CANId
  parseCANIdField ctx key obj =
    require (ctx ++ₛ ": missing '" ++ₛ key ++ₛ "' field") (lookupNat key obj) >>=ₑ λ rawId →
    parseCANIdFromNat ctx rawId obj
    where
    parseCANIdFromNat : String → ℕ → List (String × JSON) → String ⊎ CANId
    parseCANIdFromNat ctx' rawId obj' with lookupBool "extended" obj'
    ... | just true  = if rawId <ᵇ extended-can-id-max
                        then inj₂ (Extended (rawId % extended-can-id-max))
                        else inj₁ (ctx' ++ₛ ": extended CAN ID out of range")
    ... | just false = if rawId <ᵇ standard-can-id-max
                        then inj₂ (Standard (rawId % standard-can-id-max))
                        else inj₁ (ctx' ++ₛ ": standard CAN ID out of range")
    ... | nothing    = if rawId <ᵇ standard-can-id-max
                        then inj₂ (Standard (rawId % standard-can-id-max))
                        else inj₁ (ctx' ++ₛ ": CAN ID out of range for standard ID")

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
tryBuildFrame obj =
  parseCANIdField "BuildFrame" "canId" obj >>=ₑ λ canId →
  require "BuildFrame: missing 'dlc' field" (lookupNat "dlc" obj) >>=ₑ λ dlc →
  requireValidDLC "BuildFrame" dlc >>=ₑ λ _ →
  require "BuildFrame: missing 'signals' array" (lookupArray "signals" obj) >>=ₑ λ signals →
  inj₂ (BuildFrame canId dlc signals)

-- Parse ExtractAllSignals command
tryExtractAllSignals : List (String × JSON) → String ⊎ StreamCommand
tryExtractAllSignals obj =
  parseCANIdField "ExtractAllSignals" "canId" obj >>=ₑ λ canId →
  require "ExtractAllSignals: missing 'dlc' field" (lookupNat "dlc" obj) >>=ₑ λ dlc →
  requireValidDLC "ExtractAllSignals" dlc >>=ₑ λ _ →
  require "ExtractAllSignals: missing 'data' array" (lookupArray "data" obj) >>=ₑ λ bytesJSON →
  require "ExtractAllSignals: failed to parse byte array" (parseByteArray bytesJSON) >>=ₑ λ byteList →
  require "ExtractAllSignals: byte count doesn't match DLC" (listToVec (dlcToBytes dlc) byteList) >>=ₑ λ bytes →
  inj₂ (ExtractAllSignals canId dlc bytes)

-- Parse UpdateFrame command
tryUpdateFrame : List (String × JSON) → String ⊎ StreamCommand
tryUpdateFrame obj =
  parseCANIdField "UpdateFrame" "canId" obj >>=ₑ λ canId →
  require "UpdateFrame: missing 'dlc' field" (lookupNat "dlc" obj) >>=ₑ λ dlc →
  requireValidDLC "UpdateFrame" dlc >>=ₑ λ _ →
  require "UpdateFrame: missing 'data' array" (lookupArray "data" obj) >>=ₑ λ bytesJSON →
  require "UpdateFrame: failed to parse byte array" (parseByteArray bytesJSON) >>=ₑ λ byteList →
  require "UpdateFrame: byte count doesn't match DLC" (listToVec (dlcToBytes dlc) byteList) >>=ₑ λ bytes →
  require "UpdateFrame: missing 'signals' array" (lookupArray "signals" obj) >>=ₑ λ signals →
  inj₂ (UpdateFrame canId dlc bytes signals)

-- Parse EndStream command
tryEndStream : List (String × JSON) → String ⊎ StreamCommand
tryEndStream _ = inj₂ EndStream

-- Parse ValidateDBC command
tryValidateDBC : List (String × JSON) → String ⊎ StreamCommand
tryValidateDBC obj with lookupByKey "dbc" obj
... | nothing = inj₁ "ValidateDBC: missing 'dbc' field"
... | just dbc = inj₂ (ValidateDBC dbc)

-- Parse FormatDBC command (no arguments needed)
tryFormatDBC : List (String × JSON) → String ⊎ StreamCommand
tryFormatDBC _ = inj₂ FormatDBC

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
  ("formatDBC" , tryFormatDBC) ∷
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



