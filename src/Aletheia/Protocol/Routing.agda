-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Command parsing for the streaming protocol.
--
-- Purpose: Parse JSON commands and dispatch to appropriate handlers.
-- Operations: parseCommand (JSON → RouteError ⊎ StreamCommand).
-- Role: Parses the "command" field from JSON objects, used by Main.processJSONLine.
-- Validation: All required fields checked, typed RouteError on failure.
module Aletheia.Protocol.Routing where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Aletheia.Prelude using (lookupByKey; require; _>>=ₑ_; mapₑ; ifᵀ_then_else_)
open import Aletheia.Protocol.JSON using (JSON; lookupString; lookupNat; lookupArray; lookupBool; getInt)
open import Aletheia.DBC.JSONParser using (parseCANId)
open import Aletheia.Protocol.Message using (StreamCommand; ParseDBC; SetProperties; StartStream; SendFrame; EndStream; ExtractAllSignals; ValidateDBC; FormatDBC; ParseDBCText; FormatDBCText)
open import Aletheia.CAN.Frame using (Byte; CANId)
open import Aletheia.CAN.DLC using (DLC; mkDLC; dlcBytes; maxDLC-FD)
open import Aletheia.Error using
  ( Error; RouteErr; InputBoundExceeded
  ; RouteError; RouteMissingField; RouteMissingArray; UnknownCommand
  ; MissingCommandField; DLCExceedsMax; ByteArrayParseFailed
  ; ByteCountMismatch; MissingDBCField; MissingPropsField
  ; InContext
  )
open import Aletheia.Limits using (FrameByteCount; max-frame-byte-count)

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

private
  -- Byte upper bound (exclusive): values must be < 256
  byte-bound : ℕ
  byte-bound = 256

  -- Require a named field, producing a standardized "missing 'X'" error
  -- wrapped in the command-level context (`InContext cmd ...`).
  requireNat : String → String → List (String × JSON) → RouteError ⊎ ℕ
  requireNat cmd name obj = require (InContext cmd (RouteMissingField name)) (lookupNat name obj)

  requireArray : String → String → List (String × JSON) → RouteError ⊎ List JSON
  requireArray cmd name obj = require (InContext cmd (RouteMissingArray name)) (lookupArray name obj)

  -- Validate DLC code (0–15) and construct validated DLC record.
  requireValidDLC : String → ℕ → RouteError ⊎ DLC
  requireValidDLC ctx n =
    ifᵀ (n <ᵇ suc maxDLC-FD) then (λ p → inj₂ (mkDLC n p)) else inj₁ (InContext ctx DLCExceedsMax)

  -- Parse CAN ID from a named ℕ field and optional "extended" (Bool) field.
  -- Returns top-level `Error` (R20 cluster I — AGDA-D-32.1 lifted
  -- `parseCANId`'s return type to `Error ⊎ CANId`); the legacy ParseError
  -- envelopes arrive pre-wrapped via `ParseErr`, the `requireNat`
  -- RouteError stays RouteError-wrapped via `mapₑ RouteErr`.  Dropping
  -- the prior `WrappedParse` wrap loses no information — the wire code
  -- and `errorExtras` payload now route through `Error.errorCode` /
  -- `errorExtras` directly.
  parseCANIdField : String → String → List (String × JSON) → Error ⊎ CANId
  parseCANIdField ctx key obj =
    mapₑ RouteErr (requireNat ctx key obj) >>=ₑ λ rawId →
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
  tryParseDBC : List (String × JSON) → Error ⊎ StreamCommand
  tryParseDBC obj with lookupByKey "dbc" obj
  ... | nothing = inj₁ (RouteErr (InContext "ParseDBC" MissingDBCField))
  ... | just dbc = inj₂ (ParseDBC dbc)

  -- Parse SetProperties command
  trySetProperties : List (String × JSON) → Error ⊎ StreamCommand
  trySetProperties obj with lookupArray "properties" obj
  ... | nothing = inj₁ (RouteErr MissingPropsField)
  ... | just props = inj₂ (SetProperties props)

  -- Parse StartStream command
  tryStartStream : List (String × JSON) → Error ⊎ StreamCommand
  tryStartStream _ = inj₂ StartStream

  -- Shared prefix: parse CAN ID + validated DLC from command fields.
  -- Return type lifts to `Error` per the R20 cluster I cascade described
  -- on `parseCANIdField`.  `requireNat` and `requireValidDLC` stay
  -- RouteError-typed and are bridged via `mapₑ RouteErr` at the bind
  -- point.
  parseCanIdDlc : String → List (String × JSON) → Error ⊎ (CANId × DLC)
  parseCanIdDlc ctx obj =
    parseCANIdField ctx "canId" obj >>=ₑ λ canId →
    mapₑ RouteErr (requireNat ctx "dlc" obj) >>=ₑ λ rawDlc →
    mapₑ RouteErr (requireValidDLC ctx rawDlc) >>=ₑ λ dlc →
    inj₂ (canId , dlc)

  -- Shared prefix: parse byte payload from "data" array with DLC-based length check.
  --
  -- R20 cluster I — AGDA-D-32.3.  The `data` array's length is bounded by
  -- `max-frame-byte-count` (64 — CAN-FD maximum payload).  We pre-check
  -- the byte-array length before delegating to `listToVec`: an array
  -- exceeding 64 bytes is surfaced as a typed
  -- `Error.InputBoundExceeded FrameByteCount observed limit` rather than
  -- as the looser `ByteCountMismatch` (which fires for any length
  -- disagreement with `dlcBytes dlc`, both shorter and longer).  Per
  -- AGENTS.md universal rule "Adversarial-input bounds at parser
  -- surfaces", rejection over the bound is a typed error carrying the
  -- offending kind.  Return type lifts to top-level `Error ⊎ ...` so the
  -- bound emit composes; the internal `RouteError` helpers are bridged
  -- via `mapₑ RouteErr`.
  parseBytePayload : String → (dlc : DLC) → List (String × JSON) → Error ⊎ Vec Byte (dlcBytes dlc)
  parseBytePayload ctx dlc obj =
    mapₑ RouteErr (requireArray ctx "data" obj) >>=ₑ λ bytesJSON →
    mapₑ RouteErr (require (InContext ctx ByteArrayParseFailed) (parseByteArray bytesJSON)) >>=ₑ λ byteList →
    if (length byteList <ᵇ suc max-frame-byte-count)
      then mapₑ RouteErr (require (InContext ctx ByteCountMismatch) (listToVec (dlcBytes dlc) byteList))
      else inj₁ (InputBoundExceeded FrameByteCount (length byteList) max-frame-byte-count)

  -- Parse ExtractAllSignals command
  tryExtractAllSignals : List (String × JSON) → Error ⊎ StreamCommand
  tryExtractAllSignals obj =
    parseCanIdDlc "ExtractAllSignals" obj >>=ₑ λ (canId , dlc) →
    parseBytePayload "ExtractAllSignals" dlc obj >>=ₑ λ bytes →
    inj₂ (ExtractAllSignals canId dlc bytes)

  -- Parse SendFrame command — JSON mirror of the binary FFI
  -- `aletheia_send_frame` entry point.  Required fields: `timestamp`
  -- (ℕ µs), `canId`, `dlc`, `data` (byte array).  Optional fields:
  -- `extended` (Bool, handled by `parseCANId`), `brs` (Bool, CAN-FD),
  -- `esi` (Bool, CAN-FD).  Missing brs / esi are treated as Nothing
  -- (CAN 2.0B frame).  R19 Phase 2 cluster 18 — AGDA-D-10.1 closure.
  trySendFrame : List (String × JSON) → Error ⊎ StreamCommand
  trySendFrame obj =
    mapₑ RouteErr (requireNat "SendFrame" "timestamp" obj) >>=ₑ λ ts →
    parseCanIdDlc "SendFrame" obj >>=ₑ λ (canId , dlc) →
    parseBytePayload "SendFrame" dlc obj >>=ₑ λ bytes →
    inj₂ (SendFrame ts canId dlc bytes (lookupBool "brs" obj) (lookupBool "esi" obj))

  -- Parse EndStream command
  tryEndStream : List (String × JSON) → Error ⊎ StreamCommand
  tryEndStream _ = inj₂ EndStream

  -- Parse ValidateDBC command
  tryValidateDBC : List (String × JSON) → Error ⊎ StreamCommand
  tryValidateDBC obj with lookupByKey "dbc" obj
  ... | nothing = inj₁ (RouteErr (InContext "ValidateDBC" MissingDBCField))
  ... | just dbc = inj₂ (ValidateDBC dbc)

  -- Parse FormatDBC command (no arguments needed)
  tryFormatDBC : List (String × JSON) → Error ⊎ StreamCommand
  tryFormatDBC _ = inj₂ FormatDBC

  -- Parse ParseDBCText command (raw DBC text image)
  tryParseDBCText : List (String × JSON) → Error ⊎ StreamCommand
  tryParseDBCText obj with lookupString "text" obj
  ... | nothing   = inj₁ (RouteErr (InContext "ParseDBCText" (RouteMissingField "text")))
  ... | just text = inj₂ (ParseDBCText text)

  -- Parse FormatDBCText command (DBC JSON structure → DBC text)
  tryFormatDBCText : List (String × JSON) → Error ⊎ StreamCommand
  tryFormatDBCText obj with lookupByKey "dbc" obj
  ... | nothing  = inj₁ (RouteErr (InContext "FormatDBCText" MissingDBCField))
  ... | just dbc = inj₂ (FormatDBCText dbc)

  -- Dispatch table for command parsers
  commandDispatchTable : List (String × (List (String × JSON) → Error ⊎ StreamCommand))
  commandDispatchTable =
    ("parseDBC" , tryParseDBC) ∷
    ("setProperties" , trySetProperties) ∷
    ("startStream" , tryStartStream) ∷
    ("sendFrame" , trySendFrame) ∷
    ("extractAllSignals" , tryExtractAllSignals) ∷
    ("endStream" , tryEndStream) ∷
    ("validateDBC" , tryValidateDBC) ∷
    ("formatDBC" , tryFormatDBC) ∷
    ("parseDBCText" , tryParseDBCText) ∷
    ("formatDBCText" , tryFormatDBCText) ∷
    []

  -- Dispatch using table lookup
  dispatchCommand : String → List (String × JSON) → Error ⊎ StreamCommand
  dispatchCommand cmdType obj with lookupByKey cmdType commandDispatchTable
  ... | nothing = inj₁ (RouteErr (UnknownCommand cmdType))
  ... | just parser = parser obj

-- Parse StreamCommand from JSON object (returns Error on failure).  Return
-- type lifted from `RouteError ⊎ _` to `Error ⊎ _` to accommodate the
-- typed `InputBoundExceeded FrameByteCount …` emit at `parseBytePayload`
-- (R20 cluster I — AGDA-D-32.3); RouteError emits compose via `RouteErr`.
parseCommand : List (String × JSON) → Error ⊎ StreamCommand
parseCommand obj with lookupString "command" obj
... | nothing = inj₁ (RouteErr MissingCommandField)
... | just cmdType = dispatchCommand cmdType obj
