{-# OPTIONS --safe --without-K #-}

-- Command parsing for the streaming protocol.
--
-- Purpose: Parse JSON commands and dispatch to appropriate handlers.
-- Operations: parseCommand (JSON → RouteError ⊎ StreamCommand).
-- Role: Parses the "command" field from JSON objects, used by Main.processJSONLine.
-- Validation: All required fields checked, typed RouteError on failure.
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
open import Aletheia.Prelude using (lookupByKey; require; _>>=ₑ_; mapₑ; ifᵀ_then_else_)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupNat; lookupArray; getInt)
open import Aletheia.DBC.JSONParser using (parseCANId)
open import Aletheia.Protocol.Message using (StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC; FormatDBC)
open import Aletheia.CAN.Frame using (CANFrame; Byte; CANId)
open import Aletheia.CAN.DLC using (DLC; mkDLC; dlcBytes; maxDLC-FD)
open import Aletheia.Error using
  ( RouteError; RouteMissingField; RouteMissingArray; UnknownCommand
  ; MissingCommandField; DLCExceedsMax; ByteArrayParseFailed
  ; ByteCountMismatch; MissingDBCField; MissingPropsField; WrappedParseError
  )

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

private
  -- Byte upper bound (exclusive): values must be < 256
  byte-bound : ℕ
  byte-bound = 256

  -- Require a named field, producing a standardized "missing 'X'" error
  requireNat : String → String → List (String × JSON) → RouteError ⊎ ℕ
  requireNat cmd name obj = require (RouteMissingField cmd name) (lookupNat name obj)

  requireArray : String → String → List (String × JSON) → RouteError ⊎ List JSON
  requireArray cmd name obj = require (RouteMissingArray cmd name) (lookupArray name obj)

  -- Validate DLC code (0–15) and construct validated DLC record.
  requireValidDLC : String → ℕ → RouteError ⊎ DLC
  requireValidDLC ctx n =
    ifᵀ (n <ᵇ suc maxDLC-FD) then (λ p → inj₂ (mkDLC n p)) else inj₁ (DLCExceedsMax ctx)

  -- Parse CAN ID from a named ℕ field and optional "extended" (Bool) field
  parseCANIdField : String → String → List (String × JSON) → RouteError ⊎ CANId
  parseCANIdField ctx key obj =
    requireNat ctx key obj >>=ₑ λ rawId →
    mapₑ WrappedParseError (parseCANId ctx rawId obj)

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
  tryParseDBC : List (String × JSON) → RouteError ⊎ StreamCommand
  tryParseDBC obj with lookupByKey "dbc" obj
  ... | nothing = inj₁ (MissingDBCField "ParseDBC")
  ... | just dbc = inj₂ (ParseDBC dbc)

  -- Parse SetProperties command
  trySetProperties : List (String × JSON) → RouteError ⊎ StreamCommand
  trySetProperties obj with lookupArray "properties" obj
  ... | nothing = inj₁ MissingPropsField
  ... | just props = inj₂ (SetProperties props)

  -- Parse StartStream command
  tryStartStream : List (String × JSON) → RouteError ⊎ StreamCommand
  tryStartStream _ = inj₂ StartStream

  -- Shared prefix: parse CAN ID + validated DLC from command fields.
  parseCanIdDlc : String → List (String × JSON) → RouteError ⊎ (CANId × DLC)
  parseCanIdDlc ctx obj =
    parseCANIdField ctx "canId" obj >>=ₑ λ canId →
    requireNat ctx "dlc" obj >>=ₑ λ rawDlc →
    requireValidDLC ctx rawDlc >>=ₑ λ dlc →
    inj₂ (canId , dlc)

  -- Shared prefix: parse byte payload from "data" array with DLC-based length check.
  parseBytePayload : String → (dlc : DLC) → List (String × JSON) → RouteError ⊎ Vec Byte (dlcBytes dlc)
  parseBytePayload ctx dlc obj =
    requireArray ctx "data" obj >>=ₑ λ bytesJSON →
    require (ByteArrayParseFailed ctx) (parseByteArray bytesJSON) >>=ₑ λ byteList →
    require (ByteCountMismatch ctx) (listToVec (dlcBytes dlc) byteList)

  -- Parse BuildFrame command
  tryBuildFrame : List (String × JSON) → RouteError ⊎ StreamCommand
  tryBuildFrame obj =
    parseCanIdDlc "BuildFrame" obj >>=ₑ λ (canId , dlc) →
    requireArray "BuildFrame" "signals" obj >>=ₑ λ signals →
    inj₂ (BuildFrame canId dlc signals)

  -- Parse ExtractAllSignals command
  tryExtractAllSignals : List (String × JSON) → RouteError ⊎ StreamCommand
  tryExtractAllSignals obj =
    parseCanIdDlc "ExtractAllSignals" obj >>=ₑ λ (canId , dlc) →
    parseBytePayload "ExtractAllSignals" dlc obj >>=ₑ λ bytes →
    inj₂ (ExtractAllSignals canId dlc bytes)

  -- Parse UpdateFrame command
  tryUpdateFrame : List (String × JSON) → RouteError ⊎ StreamCommand
  tryUpdateFrame obj =
    parseCanIdDlc "UpdateFrame" obj >>=ₑ λ (canId , dlc) →
    parseBytePayload "UpdateFrame" dlc obj >>=ₑ λ bytes →
    requireArray "UpdateFrame" "signals" obj >>=ₑ λ signals →
    inj₂ (UpdateFrame canId dlc bytes signals)

  -- Parse EndStream command
  tryEndStream : List (String × JSON) → RouteError ⊎ StreamCommand
  tryEndStream _ = inj₂ EndStream

  -- Parse ValidateDBC command
  tryValidateDBC : List (String × JSON) → RouteError ⊎ StreamCommand
  tryValidateDBC obj with lookupByKey "dbc" obj
  ... | nothing = inj₁ (MissingDBCField "ValidateDBC")
  ... | just dbc = inj₂ (ValidateDBC dbc)

  -- Parse FormatDBC command (no arguments needed)
  tryFormatDBC : List (String × JSON) → RouteError ⊎ StreamCommand
  tryFormatDBC _ = inj₂ FormatDBC

  -- Dispatch table for command parsers
  commandDispatchTable : List (String × (List (String × JSON) → RouteError ⊎ StreamCommand))
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
  dispatchCommand : String → List (String × JSON) → RouteError ⊎ StreamCommand
  dispatchCommand cmdType obj with lookupByKey cmdType commandDispatchTable
  ... | nothing = inj₁ (UnknownCommand cmdType)
  ... | just parser = parser obj

-- Parse StreamCommand from JSON object (returns RouteError on failure)
parseCommand : List (String × JSON) → RouteError ⊎ StreamCommand
parseCommand obj with lookupString "command" obj
... | nothing = inj₁ MissingCommandField
... | just cmdType = dispatchCommand cmdType obj
