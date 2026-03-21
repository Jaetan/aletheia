{-# OPTIONS --safe --without-K #-}

-- DBC JSON parser for the streaming protocol (Phase 2B).
--
-- Purpose: Parse DBC structures from JSON format sent by Python client.
-- Handles: Complete DBC JSON objects (messages, signals, all metadata).
-- Role: Used by Protocol.StreamState to process parseDBC commands.
--
-- Design: Parses JSON → DBC.Types, validates all required fields, bounded types.
-- Returns detailed error messages on parse failures.
-- Current protocol: Python converts .dbc → JSON, Agda parses JSON → DBC types.
module Aletheia.DBC.JSONParser where

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupBool; lookupNat; lookupRational; lookupArray)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _≟_) renaming (_++_ to _++ₛ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _%_; _≤ᵇ_; _+_; _<ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max; _>>=ₑ_)

-- ============================================================================
-- ERROR-RETURNING PARSER COMBINATORS
-- ============================================================================

-- Require a Maybe field, with context for error message
require : ∀ {A : Set} → String → Maybe A → String ⊎ A
require fieldName nothing = inj₁ ("missing field '" ++ₛ fieldName ++ₛ "'")
require _ (just x) = inj₂ x

-- ============================================================================
-- JSON → DBC PARSERS (with error messages)
-- ============================================================================

-- Parse ByteOrder from string
parseByteOrder : String → String ⊎ ByteOrder
parseByteOrder s =
  if ⌊ s ≟ "little_endian" ⌋ then inj₂ LittleEndian
  else if ⌊ s ≟ "big_endian" ⌋ then inj₂ BigEndian
  else inj₁ ("invalid byte order '" ++ₛ s ++ₛ "' (expected 'little_endian' or 'big_endian')")

-- Parse SignalPresence from JSON object
-- Can be: {"presence": "always"} or {"multiplexor": "...", "multiplex_value": N}
parseSignalPresence : List (String × JSON) → String ⊎ SignalPresence
parseSignalPresence obj = tryMux
  where
    -- Try explicit "presence" field, default to Always
    tryPresence : String ⊎ SignalPresence
    tryPresence with lookupString "presence" obj
    ... | nothing = inj₂ Always  -- Default to Always
    ... | just presenceStr =
      if ⌊ presenceStr ≟ "always" ⌋ then inj₂ Always
      else inj₁ ("invalid presence value '" ++ₛ presenceStr ++ₛ "'")

    -- Try to parse multiplexor and multiplex_value fields
    tryMux : String ⊎ SignalPresence
    tryMux with lookupString "multiplexor" obj
    ... | nothing = tryPresence  -- No multiplexor, try explicit presence field
    ... | just muxName with lookupNat "multiplex_value" obj
    ...   | nothing = tryPresence  -- Have multiplexor but no value, fall back
    ...   | just muxVal = inj₂ (When muxName muxVal)

-- Parse signed field (can be boolean or string "signed"/"unsigned")
parseSigned : List (String × JSON) → String ⊎ Bool
parseSigned obj with lookupBool "signed" obj
... | just b = inj₂ b  -- Found boolean field
... | nothing with lookupString "signed" obj
...   | nothing = inj₁ "missing field 'signed'"
...   | just signedStr =
    if ⌊ signedStr ≟ "signed" ⌋ then inj₂ true
    else if ⌊ signedStr ≟ "unsigned" ⌋ then inj₂ false
    else inj₁ ("invalid signed value '" ++ₛ signedStr ++ₛ "' (expected 'signed' or 'unsigned')")

-- Context wrapper for signal parse errors (module-level for proof visibility)
addSignalContext : String → String ⊎ DBCSignal → String ⊎ DBCSignal
addSignalContext ctx (inj₁ err) = inj₁ (ctx ++ₛ ": " ++ₛ err)
addSignalContext _ (inj₂ x) = inj₂ x

-- Parse signal fields from JSON (module-level for proof visibility)
parseSignalFields : String → String → List (String × JSON) → String ⊎ DBCSignal
parseSignalFields ctx name obj =
  addSignalContext ctx (
    require "startBit" (lookupNat "startBit" obj) >>=ₑ λ startBit →
    require "length" (lookupNat "length" obj) >>=ₑ λ bitLength →
    require "byteOrder" (lookupString "byteOrder" obj) >>=ₑ λ byteOrderStr →
    parseByteOrder byteOrderStr >>=ₑ λ byteOrder →
    parseSigned obj >>=ₑ λ isSigned →
    require "factor" (lookupRational "factor" obj) >>=ₑ λ factor →
    require "offset" (lookupRational "offset" obj) >>=ₑ λ offset →
    require "minimum" (lookupRational "minimum" obj) >>=ₑ λ minimum →
    require "maximum" (lookupRational "maximum" obj) >>=ₑ λ maximum →
    require "unit" (lookupString "unit" obj) >>=ₑ λ unit →
    parseSignalPresence obj >>=ₑ λ presence →
    inj₂ (record
      { name = name
      ; signalDef = record
          { startBit = startBit % 64
          ; bitLength = bitLength % 65
          ; isSigned = isSigned
          ; factor = factor
          ; offset = offset
          ; minimum = minimum
          ; maximum = maximum
          }
      ; byteOrder = byteOrder
      ; unit = unit
      ; presence = presence
      }))

-- Parse a single signal from JSON object
parseSignal : String → List (String × JSON) → String ⊎ DBCSignal
parseSignal context obj =
  require "name" (lookupString "name" obj) >>=ₑ λ name →
  let ctx = context ++ₛ ", signal '" ++ₛ name ++ₛ "'"
  in parseSignalFields ctx name obj

-- Parse a list of signals from JSON array
parseSignalList : String → List JSON → ℕ → String ⊎ (List DBCSignal)
parseSignalList context [] _ = inj₂ []
parseSignalList context (JObject sigObj ∷ rest) idx =
  parseSignal context sigObj >>=ₑ λ sig →
  parseSignalList context rest (idx + 1) >>=ₑ λ restParsed →
  inj₂ (sig ∷ restParsed)
parseSignalList context (_ ∷ _) idx =
  inj₁ (context ++ₛ ": signal at index " ++ₛ showℕ idx ++ₛ " is not a JSON object")

-- Parse CAN ID from natural and optional "extended" field
parseCANId : String → ℕ → List (String × JSON) → String ⊎ CANId
parseCANId context rawId obj with lookupBool "extended" obj
... | just true = if rawId <ᵇ extended-can-id-max
                   then inj₂ (Extended (rawId % extended-can-id-max))
                   else inj₁ (context ++ₛ ": extended CAN ID " ++ₛ showℕ rawId ++ₛ " out of range (max 536870911)")
... | just false = if rawId <ᵇ standard-can-id-max
                    then inj₂ (Standard (rawId % standard-can-id-max))
                    else inj₁ (context ++ₛ ": standard CAN ID " ++ₛ showℕ rawId ++ₛ " out of range (max 2047)")
... | nothing = if rawId <ᵇ standard-can-id-max
                 then inj₂ (Standard (rawId % standard-can-id-max))
                 else inj₁ (context ++ₛ ": CAN ID " ++ₛ showℕ rawId ++ₛ " out of range for standard ID (max 2047)")

-- Stage 1: Parse id + CAN ID from message fields.
-- Split out for compositional roundtrip proofs (keeps normalization bounded).
parseMessageId : String → List (String × JSON) → String ⊎ CANId
parseMessageId context obj =
  require "id" (lookupNat "id" obj) >>=ₑ λ rawId →
  parseCANId context rawId obj

-- Stage 2: Parse remaining message fields given a resolved CAN ID.
-- Split out for compositional roundtrip proofs (keeps normalization bounded).
parseMessageBody : String → String → CANId → List (String × JSON) → String ⊎ DBCMessage
parseMessageBody context name canId obj =
  require "dlc" (lookupNat "dlc" obj) >>=ₑ λ rawDlc →
  require "sender" (lookupString "sender" obj) >>=ₑ λ sender →
  require "signals" (lookupArray "signals" obj) >>=ₑ λ signalsJSON →
  parseSignalList context signalsJSON 0 >>=ₑ λ signals →
  if rawDlc ≤ᵇ 8
    then inj₂ (record
      { id = canId
      ; name = name
      ; dlc = rawDlc % 9
      ; sender = sender
      ; signals = signals
      })
    else inj₁ (context ++ₛ ": DLC " ++ₛ showℕ rawDlc ++ₛ " out of range (max 8)")

-- Compose stages into full message field parser.
-- Exposed at top level for compositional roundtrip proofs.
parseMessageFields : String → String → List (String × JSON) → String ⊎ DBCMessage
parseMessageFields context name obj =
  parseMessageId context obj >>=ₑ λ canId →
  parseMessageBody context name canId obj

-- Parse a single message from JSON object
parseMessage : List (String × JSON) → String ⊎ DBCMessage
parseMessage obj =
  require "name" (lookupString "name" obj) >>=ₑ λ name →
  let context = "message '" ++ₛ name ++ₛ "'"
  in parseMessageFields context name obj

-- Parse a list of messages from JSON array
parseMessageList : List JSON → ℕ → String ⊎ (List DBCMessage)
parseMessageList [] _ = inj₂ []
parseMessageList (JObject msgObj ∷ rest) idx =
  parseMessage msgObj >>=ₑ λ msg →
  parseMessageList rest (idx + 1) >>=ₑ λ restParsed →
  inj₂ (msg ∷ restParsed)
parseMessageList (_ ∷ _) idx =
  inj₁ ("message at index " ++ₛ showℕ idx ++ₛ " is not a JSON object")

-- Parse top-level DBC structure from JSON object (with error messages)
parseDBCWithErrors : JSON → String ⊎ DBC
parseDBCWithErrors (JObject obj) =
  require "version" (lookupString "version" obj) >>=ₑ λ version →
  require "messages" (lookupArray "messages" obj) >>=ₑ λ messagesJSON →
  parseMessageList messagesJSON 0 >>=ₑ λ messages →
  inj₂ (record
    { version = version
    ; messages = messages
    })
parseDBCWithErrors _ = inj₁ "DBC root must be a JSON object"
