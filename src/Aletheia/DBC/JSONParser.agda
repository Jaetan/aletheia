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

open import Aletheia.DBC.Types
open import Aletheia.Protocol.JSON
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.List using (List; []; _∷_; map; length)
open import Data.String using (String; _≟_) renaming (_++_ to _++ₛ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Nat.DivMod using (_mod_)
open import Data.Rational using (ℚ)
open import Data.Integer using (ℤ; +_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max)

-- ============================================================================
-- ERROR-RETURNING PARSER COMBINATORS
-- ============================================================================

-- Bind for Either monad
_>>=ₑ_ : ∀ {A B : Set} → String ⊎ A → (A → String ⊎ B) → String ⊎ B
inj₁ err >>=ₑ _ = inj₁ err
inj₂ x >>=ₑ f = f x

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

-- Parse a single signal from JSON object
parseSignal : String → List (String × JSON) → String ⊎ DBCSignal
parseSignal context obj =
  require "name" (lookupString "name" obj) >>=ₑ λ name →
  let ctx = context ++ₛ ", signal '" ++ₛ name ++ₛ "'"
  in parseSignalFields ctx name obj
  where
    addContext : String → String ⊎ DBCSignal → String ⊎ DBCSignal
    addContext ctx (inj₁ err) = inj₁ (ctx ++ₛ ": " ++ₛ err)
    addContext _ (inj₂ x) = inj₂ x

    parseSignalFields : String → String → List (String × JSON) → String ⊎ DBCSignal
    parseSignalFields ctx name obj =
      addContext ctx (
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
              { startBit = startBit mod 64
              ; bitLength = bitLength mod 65
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

-- Parse a list of signals from JSON array
parseSignalList : String → List JSON → ℕ → String ⊎ (List DBCSignal)
parseSignalList context [] _ = inj₂ []
parseSignalList context (JObject sigObj ∷ rest) idx =
  parseSignal context sigObj >>=ₑ λ sig →
  parseSignalList context rest (idx Data.Nat.+ 1) >>=ₑ λ restParsed →
  inj₂ (sig ∷ restParsed)
parseSignalList context (_ ∷ _) idx =
  inj₁ (context ++ₛ ": signal at index " ++ₛ showℕ idx ++ₛ " is not a JSON object")

-- Parse CAN ID from natural and optional "extended" field
parseCANId : String → ℕ → List (String × JSON) → String ⊎ CANId
parseCANId context rawId obj with lookupBool "extended" obj
... | just true = if rawId Data.Nat.<ᵇ extended-can-id-max
                   then inj₂ (Extended (rawId mod extended-can-id-max))
                   else inj₁ (context ++ₛ ": extended CAN ID " ++ₛ showℕ rawId ++ₛ " out of range (max 536870911)")
... | just false = if rawId Data.Nat.<ᵇ standard-can-id-max
                    then inj₂ (Standard (rawId mod standard-can-id-max))
                    else inj₁ (context ++ₛ ": standard CAN ID " ++ₛ showℕ rawId ++ₛ " out of range (max 2047)")
... | nothing = if rawId Data.Nat.<ᵇ standard-can-id-max
                 then inj₂ (Standard (rawId mod standard-can-id-max))
                 else inj₁ (context ++ₛ ": CAN ID " ++ₛ showℕ rawId ++ₛ " out of range for standard ID (max 2047)")
  where
    open import Data.Nat using (_<ᵇ_)

-- Parse a single message from JSON object
parseMessage : List (String × JSON) → String ⊎ DBCMessage
parseMessage obj =
  require "name" (lookupString "name" obj) >>=ₑ λ name →
  let context = "message '" ++ₛ name ++ₛ "'"
  in parseMessageFields context name obj
  where
    open import Data.Nat using (_≤ᵇ_)

    parseMessageFields : String → String → List (String × JSON) → String ⊎ DBCMessage
    parseMessageFields context name obj =
      require "id" (lookupNat "id" obj) >>=ₑ λ rawId →
      parseCANId context rawId obj >>=ₑ λ msgId →
      require "dlc" (lookupNat "dlc" obj) >>=ₑ λ rawDlc →
      require "sender" (lookupString "sender" obj) >>=ₑ λ sender →
      require "signals" (lookupArray "signals" obj) >>=ₑ λ signalsJSON →
      parseSignalList context signalsJSON 0 >>=ₑ λ signals →
      if rawDlc ≤ᵇ 8
        then inj₂ (record
          { id = msgId
          ; name = name
          ; dlc = rawDlc mod 9
          ; sender = sender
          ; signals = signals
          })
        else inj₁ (context ++ₛ ": DLC " ++ₛ showℕ rawDlc ++ₛ " out of range (max 8)")

-- Parse a list of messages from JSON array
parseMessageList : List JSON → ℕ → String ⊎ (List DBCMessage)
parseMessageList [] _ = inj₂ []
parseMessageList (JObject msgObj ∷ rest) idx =
  parseMessage msgObj >>=ₑ λ msg →
  parseMessageList rest (idx Data.Nat.+ 1) >>=ₑ λ restParsed →
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

-- Original Maybe-based interface for backwards compatibility
parseDBC : JSON → Maybe DBC
parseDBC json with parseDBCWithErrors json
... | inj₁ _ = nothing
... | inj₂ dbc = just dbc
