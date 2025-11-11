{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Handlers where

open import Aletheia.Protocol.Command
open import Aletheia.Protocol.Response
open import Aletheia.DBC.Types
open import Aletheia.DBC.Parser
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.CAN.Endianness
open import Aletheia.Parser.Combinators
open import Data.String using (String; _++_; toList; _≟_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec)
open import Data.Rational using (ℚ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Simple find function for lists
find : ∀ {A : Set} → (A → Bool) → List A → Maybe A
find pred [] = nothing
find pred (x ∷ xs) = if pred x then just x else find pred xs

-- Find a message by name in a DBC
findMessage : String → DBC → Maybe DBCMessage
findMessage msgName dbc = find matchName (DBC.messages dbc)
  where
    matchName : DBCMessage → Bool
    matchName msg = ⌊ DBCMessage.name msg ≟ msgName ⌋

-- Find a signal by name in a message
findSignal : String → DBCMessage → Maybe DBCSignal
findSignal sigName msg = find matchName (DBCMessage.signals msg)
  where
    matchName : DBCSignal → Bool
    matchName sig = ⌊ DBCSignal.name sig ≟ sigName ⌋

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Handle ParseDBC command
{-# NOINLINE handleParseDBC #-}
handleParseDBC : String → Response
handleParseDBC yaml = parseHelper (runParser parseDBC (toList yaml))
  where
    parseHelper : Maybe DBC → Response
    parseHelper nothing = errorResponse "Failed to parse DBC YAML"
    parseHelper (just dbc) = successResponse "DBC parsed successfully" (DBCData dbc)

-- Handle ExtractSignal command
{-# NOINLINE handleExtractSignal #-}
handleExtractSignal : String → String → String → Vec Byte 8 → Response
handleExtractSignal dbcYAML msgName sigName frameBytes =
  parseDBCHelper (runParser parseDBC (toList dbcYAML))
  where
    parseDBCHelper : Maybe DBC → Response
    parseDBCHelper nothing = errorResponse "Failed to parse DBC YAML"
    parseDBCHelper (just dbc) = findMessageHelper (findMessage msgName dbc)
      where
        findMessageHelper : Maybe DBCMessage → Response
        findMessageHelper nothing = errorResponse ("Message not found: " ++ msgName)
        findMessageHelper (just msg) = findSignalHelper (findSignal sigName msg)
          where
            findSignalHelper : Maybe DBCSignal → Response
            findSignalHelper nothing = errorResponse ("Signal not found: " ++ sigName)
            findSignalHelper (just sig) =
              let frame = record { id = DBCMessage.id msg ; dlc = DBCMessage.dlc msg ; payload = frameBytes }
                  sigDef = DBCSignal.signalDef sig
                  byteOrd = DBCSignal.byteOrder sig
              in extractHelper (extractSignal frame sigDef byteOrd)
              where
                extractHelper : Maybe SignalValue → Response
                extractHelper nothing = errorResponse "Failed to extract signal value"
                extractHelper (just val) = successResponse "Signal extracted successfully" (SignalValueData val)

-- Handle InjectSignal command
{-# NOINLINE handleInjectSignal #-}
handleInjectSignal : String → String → String → ℚ → Vec Byte 8 → Response
handleInjectSignal dbcYAML msgName sigName value frameBytes =
  parseDBCHelper (runParser parseDBC (toList dbcYAML))
  where
    parseDBCHelper : Maybe DBC → Response
    parseDBCHelper nothing = errorResponse "Failed to parse DBC YAML"
    parseDBCHelper (just dbc) = findMessageHelper (findMessage msgName dbc)
      where
        findMessageHelper : Maybe DBCMessage → Response
        findMessageHelper nothing = errorResponse ("Message not found: " ++ msgName)
        findMessageHelper (just msg) = findSignalHelper (findSignal sigName msg)
          where
            findSignalHelper : Maybe DBCSignal → Response
            findSignalHelper nothing = errorResponse ("Signal not found: " ++ sigName)
            findSignalHelper (just sig) =
              let frame = record { id = DBCMessage.id msg ; dlc = DBCMessage.dlc msg ; payload = frameBytes }
                  sigDef = DBCSignal.signalDef sig
                  byteOrd = DBCSignal.byteOrder sig
              in injectHelper (injectSignal value sigDef byteOrd frame)
              where
                injectHelper : Maybe CANFrame → Response
                injectHelper nothing = errorResponse "Failed to inject signal value"
                injectHelper (just newFrame) = successResponse "Signal injected successfully" (FrameData (CANFrame.payload newFrame))
