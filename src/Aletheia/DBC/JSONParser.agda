{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.JSONParser where

open import Aletheia.DBC.Types
open import Aletheia.Protocol.JSON
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String; _≟_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Nat.DivMod using (_mod_)
open import Data.Rational using (ℚ)
open import Data.Integer using (ℤ; +_)
open import Data.Fin using (Fin)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- ============================================================================
-- JSON → DBC PARSERS
-- ============================================================================

-- Parse ByteOrder from string
parseByteOrder : String → Maybe ByteOrder
parseByteOrder s =
  if ⌊ s ≟ "little_endian" ⌋ then just LittleEndian
  else if ⌊ s ≟ "big_endian" ⌋ then just BigEndian
  else nothing

-- Parse SignalPresence from JSON object
-- Can be: {"presence": "always"} or {"multiplexor": "...", "multiplex_value": N}
parseSignalPresence : List (String × JSON) → Maybe SignalPresence
parseSignalPresence obj = tryMux
  where
    -- Try explicit "presence" field, default to Always
    tryPresence : Maybe SignalPresence
    tryPresence with lookupString "presence" obj
    ... | nothing = just Always  -- Default to Always
    ... | just presenceStr =
      if ⌊ presenceStr ≟ "always" ⌋ then just Always else nothing

    -- Try to parse multiplexor and multiplex_value fields
    tryMux : Maybe SignalPresence
    tryMux with lookupString "multiplexor" obj
    ... | nothing = tryPresence  -- No multiplexor, try explicit presence field
    ... | just muxName with lookupNat "multiplex_value" obj
    ...   | nothing = tryPresence  -- Have multiplexor but no value
    ...   | just muxVal = just (When muxName muxVal)

-- Parse a single signal from JSON object
parseSignal : List (String × JSON) → Maybe DBCSignal
parseSignal obj = do
  name ← lookupString "name" obj
  startBit ← lookupNat "startBit" obj
  bitLength ← lookupNat "length" obj
  byteOrderStr ← lookupString "byteOrder" obj
  byteOrder ← parseByteOrder byteOrderStr

  -- Parse "signed" field (can be boolean or string)
  isSigned ← parseSigned obj

  -- Get rational fields using getRational helper
  factorJSON ← lookup "factor" obj
  factor ← getRational factorJSON

  offsetJSON ← lookup "offset" obj
  offset ← getRational offsetJSON

  minimumJSON ← lookup "minimum" obj
  minimum ← getRational minimumJSON

  maximumJSON ← lookup "maximum" obj
  maximum ← getRational maximumJSON

  unit ← lookupString "unit" obj
  presence ← parseSignalPresence obj

  just (record
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
    })
  where
    -- Parse signed field (can be boolean or string "signed"/"unsigned")
    parseSigned : List (String × JSON) → Maybe Bool
    parseSigned obj with lookupBool "signed" obj
    ... | just b = just b  -- Found boolean field
    ... | nothing with lookupString "signed" obj
    ...   | nothing = nothing  -- No "signed" field at all
    ...   | just signedStr =
      if ⌊ signedStr ≟ "signed" ⌋ then just true
      else if ⌊ signedStr ≟ "unsigned" ⌋ then just false
      else nothing

-- Parse a list of signals from JSON array
parseSignalList : List JSON → Maybe (List DBCSignal)
parseSignalList [] = just []
parseSignalList (JObject sigObj ∷ rest) = do
  sig ← parseSignal sigObj
  restParsed ← parseSignalList rest
  just (sig ∷ restParsed)
parseSignalList (_ ∷ _) = nothing  -- Non-object in array

-- Parse CAN ID from natural and optional "extended" field
parseCANId : ℕ → List (String × JSON) → Maybe CANId
parseCANId rawId obj with lookupBool "extended" obj
... | just true = just (Extended (rawId mod 536870912))
... | just false = just (Standard (rawId mod 2048))
... | nothing = just (Standard (rawId mod 2048))  -- Default to standard

-- Parse a single message from JSON object
parseMessage : List (String × JSON) → Maybe DBCMessage
parseMessage obj = do
  rawId ← lookupNat "id" obj
  msgId ← parseCANId rawId obj
  name ← lookupString "name" obj
  dlc ← lookupNat "dlc" obj
  sender ← lookupString "sender" obj
  signalsJSON ← lookupArray "signals" obj
  signals ← parseSignalList signalsJSON

  just (record
    { id = msgId
    ; name = name
    ; dlc = dlc mod 9
    ; sender = sender
    ; signals = signals
    })

-- Parse a list of messages from JSON array
parseMessageList : List JSON → Maybe (List DBCMessage)
parseMessageList [] = just []
parseMessageList (JObject msgObj ∷ rest) = do
  msg ← parseMessage msgObj
  restParsed ← parseMessageList rest
  just (msg ∷ restParsed)
parseMessageList (_ ∷ _) = nothing  -- Non-object in array

-- Parse top-level DBC structure from JSON object
parseDBC : JSON → Maybe DBC
parseDBC (JObject obj) = do
  version ← lookupString "version" obj
  messagesJSON ← lookupArray "messages" obj
  messages ← parseMessageList messagesJSON

  just (record
    { version = version
    ; messages = messages
    })
parseDBC _ = nothing  -- Not a JSON object
