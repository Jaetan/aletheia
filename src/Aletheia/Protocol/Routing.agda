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
open import Data.Bool using (Bool; T; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Aletheia.Prelude using (lookupByKey; require; _>>=ₑ_; ifᵀ_then_else_)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupNat; lookupArray; getInt)
open import Aletheia.DBC.JSONParser using (parseCANId)
open import Aletheia.Protocol.Message using (StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC; FormatDBC)
open import Aletheia.CAN.Frame using (CANFrame; Byte; CANId)
open import Aletheia.CAN.DLC using (DLC; mkDLC; dlcBytes)

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

private
  -- Maximum DLC code (CAN-FD)
  max-dlc-code : ℕ
  max-dlc-code = 15

  -- Byte upper bound (exclusive): values must be < 256
  byte-bound : ℕ
  byte-bound = 256

  -- Require a named field, producing a standardized "missing 'X'" error
  requireNat : String → String → List (String × JSON) → String ⊎ ℕ
  requireNat cmd name obj = require (cmd ++ₛ ": missing '" ++ₛ name ++ₛ "' field") (lookupNat name obj)

  requireArray : String → String → List (String × JSON) → String ⊎ List JSON
  requireArray cmd name obj = require (cmd ++ₛ ": missing '" ++ₛ name ++ₛ "' array") (lookupArray name obj)

  -- Validate DLC code (0–15) and construct validated DLC record.
  requireValidDLC : String → ℕ → String ⊎ DLC
  requireValidDLC ctx n =
    ifᵀ (n <ᵇ 16) then (λ p → inj₂ (mkDLC n p)) else inj₁ (ctx ++ₛ ": DLC exceeds maximum value")

  -- Parse CAN ID from a named ℕ field and optional "extended" (Bool) field
  parseCANIdField : String → String → List (String × JSON) → String ⊎ CANId
  parseCANIdField ctx key obj =
    requireNat ctx key obj >>=ₑ λ rawId →
    parseCANId ctx rawId obj

  -- Parse a JSON array as a list of bytes
  parseByteArray : List JSON → Maybe (List ℕ)
  parseByteArray [] = just []
  parseByteArray (jn ∷ rest) = do
    n ← getInt jn
    extractNat n rest
    where
      extractNat : ℤ → List JSON → Maybe (List ℕ)
      extractNat (+ nℕ) rest = do
        restParsed ← parseByteArray rest
        just (nℕ ∷ restParsed)
      extractNat -[1+ _ ] _ = nothing

  -- Convert List ℕ to Vec Byte n (if length matches and all values < 256)
  listToVec : (n : ℕ) → List ℕ → Maybe (Vec Byte n)
  listToVec zero    []       = just Data.Vec.[]
  listToVec zero    (_ ∷ _)  = nothing
  listToVec (suc n) []       = nothing
  listToVec (suc n) (x ∷ xs) with suc x ≤? byte-bound
  ... | no  _ = nothing
  ... | yes _ = listToVec n xs >>= λ rest → just (x Data.Vec.∷ rest)

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
    requireNat "BuildFrame" "dlc" obj >>=ₑ λ rawDlc →
    requireValidDLC "BuildFrame" rawDlc >>=ₑ λ dlc →
    requireArray "BuildFrame" "signals" obj >>=ₑ λ signals →
    inj₂ (BuildFrame canId dlc signals)

  -- Parse ExtractAllSignals command
  tryExtractAllSignals : List (String × JSON) → String ⊎ StreamCommand
  tryExtractAllSignals obj =
    parseCANIdField "ExtractAllSignals" "canId" obj >>=ₑ λ canId →
    requireNat "ExtractAllSignals" "dlc" obj >>=ₑ λ rawDlc →
    requireValidDLC "ExtractAllSignals" rawDlc >>=ₑ λ dlc →
    requireArray "ExtractAllSignals" "data" obj >>=ₑ λ bytesJSON →
    require "ExtractAllSignals: failed to parse byte array" (parseByteArray bytesJSON) >>=ₑ λ byteList →
    require "ExtractAllSignals: byte count doesn't match DLC" (listToVec (dlcBytes dlc) byteList) >>=ₑ λ bytes →
    inj₂ (ExtractAllSignals canId dlc bytes)

  -- Parse UpdateFrame command
  tryUpdateFrame : List (String × JSON) → String ⊎ StreamCommand
  tryUpdateFrame obj =
    parseCANIdField "UpdateFrame" "canId" obj >>=ₑ λ canId →
    requireNat "UpdateFrame" "dlc" obj >>=ₑ λ rawDlc →
    requireValidDLC "UpdateFrame" rawDlc >>=ₑ λ dlc →
    requireArray "UpdateFrame" "data" obj >>=ₑ λ bytesJSON →
    require "UpdateFrame: failed to parse byte array" (parseByteArray bytesJSON) >>=ₑ λ byteList →
    require "UpdateFrame: byte count doesn't match DLC" (listToVec (dlcBytes dlc) byteList) >>=ₑ λ bytes →
    requireArray "UpdateFrame" "signals" obj >>=ₑ λ signals →
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
... | nothing = inj₁ "ParseCommand: missing 'command' field"
... | just cmdType = dispatchCommand cmdType obj



