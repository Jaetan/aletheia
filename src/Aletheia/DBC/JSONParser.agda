{-# OPTIONS --safe --without-K #-}

-- DBC JSON parser for the streaming protocol (Phase 2B).
--
-- Purpose: Parse DBC structures from JSON format sent by Python client.
-- Handles: Complete DBC JSON objects (messages, signals, all metadata).
-- Role: Used by Protocol.StreamState to process parseDBC commands.
--
-- Design: Parses JSON → DBC.Types, validates all required fields, bounded types.
-- Returns typed ParseError values on parse failures.
-- Current protocol: Python converts .dbc → JSON, Agda parses JSON → DBC types.
module Aletheia.DBC.JSONParser where

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupBool; lookupNat; lookupRational; lookupArray)
open import Aletheia.CAN.DLC using (bytesToValidDLC)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; convertStartBit)
open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _%_; _≤ᵇ_; _+_; _<ᵇ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.String.Properties using (_≟_)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max; max-physical-bits; require; _>>=ₑ_; ifᵀ_then_else_)
open import Aletheia.Error using
  ( ParseError; MissingField; InvalidByteOrder; InvalidPresence
  ; MissingSigned; InvalidSigned; NotAnObject; ExtCANIdOutOfRange
  ; StdCANIdOutOfRange; DefaultCANIdOutOfRange; InvalidDLCBytes
  ; RootNotObject; MissingSignalName; InContext
  )

-- ============================================================================
-- JSON → DBC PARSERS (with typed ParseError)
-- ============================================================================

-- Parse ByteOrder from string
parseByteOrder : String → ParseError ⊎ ByteOrder
parseByteOrder s =
  if ⌊ s ≟ "little_endian" ⌋ then inj₂ LittleEndian
  else if ⌊ s ≟ "big_endian" ⌋ then inj₂ BigEndian
  else inj₁ (InvalidByteOrder s)

-- Parse SignalPresence from JSON object
-- Can be: {"presence": "always"} or {"multiplexor": "...", "multiplex_value": N}
parseSignalPresence : List (String × JSON) → ParseError ⊎ SignalPresence
parseSignalPresence obj = tryMux
  where
    -- Try explicit "presence" field, default to Always
    tryPresence : ParseError ⊎ SignalPresence
    tryPresence with lookupString "presence" obj
    ... | nothing = inj₂ Always  -- Default to Always
    ... | just presenceStr =
      if ⌊ presenceStr ≟ "always" ⌋ then inj₂ Always
      else inj₁ (InvalidPresence presenceStr)

    -- Try to parse multiplexor and multiplex_value fields
    tryMux : ParseError ⊎ SignalPresence
    tryMux with lookupString "multiplexor" obj
    ... | nothing = tryPresence  -- No multiplexor, try explicit presence field
    ... | just muxName with lookupNat "multiplex_value" obj
    ...   | nothing = tryPresence  -- Have multiplexor but no value, fall back
    ...   | just muxVal = inj₂ (When muxName muxVal)

-- Parse signed field (can be boolean or string "signed"/"unsigned")
parseSigned : List (String × JSON) → ParseError ⊎ Bool
parseSigned obj with lookupBool "signed" obj
... | just b = inj₂ b  -- Found boolean field
... | nothing with lookupString "signed" obj
...   | nothing = inj₁ MissingSigned
...   | just signedStr =
    if ⌊ signedStr ≟ "signed" ⌋ then inj₂ true
    else if ⌊ signedStr ≟ "unsigned" ⌋ then inj₂ false
    else inj₁ (InvalidSigned signedStr)

-- Context wrapper for signal parse errors (extracted from parseSignal where-block so proofs can case-split)
private
  addSignalContext : String → ParseError ⊎ DBCSignal → ParseError ⊎ DBCSignal
  addSignalContext ctx (inj₁ err) = inj₁ (InContext ctx err)
  addSignalContext _ (inj₂ x) = inj₂ x

-- Parse signal fields from JSON (extracted from parseSignal where-block so proofs can case-split).
-- frameBytes: the message's DLC byte count, used for convertStartBit on BE signals.
parseSignalFields : ℕ → String → String → List (String × JSON) → ParseError ⊎ DBCSignal
parseSignalFields frameBytes ctx name obj =
  addSignalContext ctx (
    require (MissingField "startBit") (lookupNat "startBit" obj) >>=ₑ λ startBit →
    require (MissingField "length") (lookupNat "length" obj) >>=ₑ λ bitLength →
    require (MissingField "byteOrder") (lookupString "byteOrder" obj) >>=ₑ λ byteOrderStr →
    parseByteOrder byteOrderStr >>=ₑ λ byteOrder →
    parseSigned obj >>=ₑ λ isSigned →
    require (MissingField "factor") (lookupRational "factor" obj) >>=ₑ λ factor →
    require (MissingField "offset") (lookupRational "offset" obj) >>=ₑ λ offset →
    require (MissingField "minimum") (lookupRational "minimum" obj) >>=ₑ λ minimum →
    require (MissingField "maximum") (lookupRational "maximum" obj) >>=ₑ λ maximum →
    require (MissingField "unit") (lookupString "unit" obj) >>=ₑ λ unit →
    parseSignalPresence obj >>=ₑ λ presence →
    let sb = startBit % max-physical-bits
        bl = bitLength % (1 + max-physical-bits)
    in inj₂ (record
      { name = name
      ; signalDef = record
          { startBit = convertStartBit frameBytes byteOrder sb bl
          ; bitLength = bl
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

-- Parse a single signal from JSON object.
-- frameBytes: the message's DLC byte count, used for convertStartBit on BE signals.
parseSignal : ℕ → String → List (String × JSON) → ParseError ⊎ DBCSignal
parseSignal frameBytes context obj =
  require (InContext context MissingSignalName) (lookupString "name" obj) >>=ₑ λ name →
  let ctx = context ++ₛ ", signal '" ++ₛ name ++ₛ "'"
  in parseSignalFields frameBytes ctx name obj

-- Parse a list of signals from JSON array.
-- frameBytes: the message's DLC byte count, used for convertStartBit on BE signals.
parseSignalList : ℕ → String → List JSON → ℕ → ParseError ⊎ (List DBCSignal)
parseSignalList frameBytes context [] _ = inj₂ []
parseSignalList frameBytes context (JObject sigObj ∷ rest) idx =
  parseSignal frameBytes context sigObj >>=ₑ λ sig →
  parseSignalList frameBytes context rest (idx + 1) >>=ₑ λ restParsed →
  inj₂ (sig ∷ restParsed)
parseSignalList frameBytes context (_ ∷ _) idx =
  inj₁ (InContext context (NotAnObject "signal" idx))

-- Parse CAN ID from natural and optional "extended" field.
-- Bounds are embedded in the CANId type via T (n <ᵇ max).
-- Uses ifᵀ (regular function, not with) so that rewrite works in roundtrip proofs.
parseCANId : String → ℕ → List (String × JSON) → ParseError ⊎ CANId
parseCANId context rawId obj with lookupBool "extended" obj
... | just true  = ifᵀ rawId <ᵇ extended-can-id-max
                    then (λ pf → inj₂ (Extended rawId pf))
                    else inj₁ (InContext context (ExtCANIdOutOfRange rawId))
... | just false = ifᵀ rawId <ᵇ standard-can-id-max
                    then (λ pf → inj₂ (Standard rawId pf))
                    else inj₁ (InContext context (StdCANIdOutOfRange rawId))
... | nothing    = ifᵀ rawId <ᵇ standard-can-id-max
                    then (λ pf → inj₂ (Standard rawId pf))
                    else inj₁ (InContext context (DefaultCANIdOutOfRange rawId))

-- Stage 1: Parse id + CAN ID from message fields.
-- Split out for compositional roundtrip proofs (keeps normalization bounded).
parseMessageId : String → List (String × JSON) → ParseError ⊎ CANId
parseMessageId context obj =
  require (InContext context (MissingField "id")) (lookupNat "id" obj) >>=ₑ λ rawId →
  parseCANId context rawId obj

-- Stage 2: Parse remaining message fields given a resolved CAN ID.
-- Split out for compositional roundtrip proofs (keeps normalization bounded).
parseMessageBody : String → String → CANId → List (String × JSON) → ParseError ⊎ DBCMessage
parseMessageBody context name canId obj =
  require (InContext context (MissingField "dlc")) (lookupNat "dlc" obj) >>=ₑ λ rawDlc →
  require (InContext context (InvalidDLCBytes rawDlc))
          (bytesToValidDLC rawDlc) >>=ₑ λ dlc →
  require (InContext context (MissingField "sender")) (lookupString "sender" obj) >>=ₑ λ sender →
  require (InContext context (MissingField "signals")) (lookupArray "signals" obj) >>=ₑ λ signalsJSON →
  parseSignalList rawDlc context signalsJSON 0 >>=ₑ λ signals →
  inj₂ (record
    { id = canId
    ; name = name
    ; dlc = dlc
    ; sender = sender
    ; signals = signals
    })

-- Compose stages into full message field parser.
-- Exposed at top level for compositional roundtrip proofs.
parseMessageFields : String → String → List (String × JSON) → ParseError ⊎ DBCMessage
parseMessageFields context name obj =
  parseMessageId context obj >>=ₑ λ canId →
  parseMessageBody context name canId obj

-- Parse a single message from JSON object
parseMessage : List (String × JSON) → ParseError ⊎ DBCMessage
parseMessage obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  let context = "message '" ++ₛ name ++ₛ "'"
  in parseMessageFields context name obj

-- Parse a list of messages from JSON array
parseMessageList : List JSON → ℕ → ParseError ⊎ (List DBCMessage)
parseMessageList [] _ = inj₂ []
parseMessageList (JObject msgObj ∷ rest) idx =
  parseMessage msgObj >>=ₑ λ msg →
  parseMessageList rest (idx + 1) >>=ₑ λ restParsed →
  inj₂ (msg ∷ restParsed)
parseMessageList (_ ∷ _) idx =
  inj₁ (NotAnObject "message" idx)

-- Parse top-level DBC structure from JSON object (with typed errors)
parseDBCWithErrors : JSON → ParseError ⊎ DBC
parseDBCWithErrors (JObject obj) =
  require (MissingField "version") (lookupString "version" obj) >>=ₑ λ version →
  require (MissingField "messages") (lookupArray "messages" obj) >>=ₑ λ messagesJSON →
  parseMessageList messagesJSON 0 >>=ₑ λ messages →
  inj₂ (record
    { version = version
    ; messages = messages
    ; signalGroups = []
    ; environmentVars = []
    ; valueTables = []
    })
parseDBCWithErrors _ = inj₁ RootNotObject
