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
open import Data.Nat using (ℕ)
open import Aletheia.Trace.Parser using (parseTrace)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.DSL.Parser using (parsePythonLTL; DSLParseResult; DSLSuccess; DSLError)
open import Aletheia.LTL.DSL.Translate using (translate)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; checkProperty)

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
    -- DEBUG: Show first byte value to diagnose parsing issue
    debugFirstByte : String
    debugFirstByte = showℕ (toℕ (head frameBytes))
      where
        open import Data.Vec using (head)
        open import Data.Fin using (toℕ)
        open import Data.Nat.Show using (show)
        showℕ = show

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
              checkPresence (DBCSignal.presence sig)
              where
                open import Data.Fin using (toℕ)
                open import Data.Nat using (ℕ)
                open import Data.Nat.Show using (show)
                open import Data.Rational as Rat using (ℚ)
                open import Relation.Nullary.Decidable using (⌊_⌋)
                open import Data.Integer using (+_)

                frame : CANFrame
                frame = record { id = DBCMessage.id msg ; dlc = DBCMessage.dlc msg ; payload = frameBytes }

                -- Helper to extract signal and format response
                extractHelper : SignalDef → Maybe SignalValue → Response
                extractHelper sigDef nothing = errorResponse ("Failed to extract signal value")
                extractHelper sigDef (just val) =
                  let startBitStr = show (toℕ (SignalDef.startBit sigDef))
                      bitLenStr = show (toℕ (SignalDef.bitLength sigDef))
                  in successResponse ("Extracted (byte=" ++ debugFirstByte ++ " start=" ++ startBitStr ++ " len=" ++ bitLenStr ++ ")") (SignalValueData val)

                -- Check if signal is present based on multiplexing
                checkPresence : SignalPresence → Response
                checkPresence Always =
                  -- Signal is always present, extract directly
                  let sigDef = DBCSignal.signalDef sig
                      byteOrd = DBCSignal.byteOrder sig
                  in extractHelper sigDef (extractSignal frame sigDef byteOrd)

                checkPresence (When muxName muxVal) =
                  -- Signal is conditional, check multiplexor first
                  findMuxHelper (findSignal muxName msg)
                  where
                    findMuxHelper : Maybe DBCSignal → Response
                    findMuxHelper nothing = errorResponse ("Multiplexor signal not found: " ++ muxName)
                    findMuxHelper (just muxSig) =
                      checkMuxValue (extractSignal frame (DBCSignal.signalDef muxSig) (DBCSignal.byteOrder muxSig))
                      where
                        open import Data.Rational using (_/_)

                        checkMuxValue : Maybe SignalValue → Response
                        checkMuxValue nothing = errorResponse ("Failed to extract multiplexor signal: " ++ muxName)
                        checkMuxValue (just muxValue) =
                          -- Check if multiplexor value matches expected value
                          let expectedℚ = (+ muxVal) / 1
                          in if ⌊ muxValue Rat.≟ expectedℚ ⌋
                             then extractHelper (DBCSignal.signalDef sig) (extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig))
                             else errorResponse ("Signal not present (multiplexor " ++ muxName ++ " value mismatch)")

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
              checkPresence (DBCSignal.presence sig)
              where
                open import Data.Rational as Rat using (ℚ)
                open import Relation.Nullary.Decidable using (⌊_⌋)
                open import Data.Nat using (ℕ)
                open import Data.Integer using (+_)

                frame : CANFrame
                frame = record { id = DBCMessage.id msg ; dlc = DBCMessage.dlc msg ; payload = frameBytes }

                -- Helper to inject signal and format response
                injectHelper : Maybe CANFrame → Response
                injectHelper nothing = errorResponse "Failed to inject signal value"
                injectHelper (just newFrame) = successResponse "Signal injected successfully" (FrameData (CANFrame.payload newFrame))

                -- Check if signal is present based on multiplexing
                checkPresence : SignalPresence → Response
                checkPresence Always =
                  -- Signal is always present, inject directly
                  let sigDef = DBCSignal.signalDef sig
                      byteOrd = DBCSignal.byteOrder sig
                  in injectHelper (injectSignal value sigDef byteOrd frame)

                checkPresence (When muxName muxVal) =
                  -- Signal is conditional, check multiplexor first
                  findMuxHelper (findSignal muxName msg)
                  where
                    findMuxHelper : Maybe DBCSignal → Response
                    findMuxHelper nothing = errorResponse ("Multiplexor signal not found: " ++ muxName)
                    findMuxHelper (just muxSig) =
                      checkMuxValue (extractSignal frame (DBCSignal.signalDef muxSig) (DBCSignal.byteOrder muxSig))
                      where
                        open import Data.Rational using (_/_)

                        checkMuxValue : Maybe SignalValue → Response
                        checkMuxValue nothing = errorResponse ("Failed to extract multiplexor signal: " ++ muxName)
                        checkMuxValue (just muxValue) =
                          -- Check if multiplexor value matches expected value
                          let expectedℚ = (+ muxVal) / 1
                          in if ⌊ muxValue Rat.≟ expectedℚ ⌋
                             then injectHelper (injectSignal value (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame)
                             else errorResponse ("Signal not present (multiplexor " ++ muxName ++ " value mismatch)")

-- Handle CheckLTL command
{-# NOINLINE handleCheckLTL #-}
handleCheckLTL : String → String → String → Response
handleCheckLTL dbcYAML traceYAML propertyYAML =
  parseDBCHelper (runParser parseDBC (toList dbcYAML))
  where
    parseDBCHelper : Maybe DBC → Response
    parseDBCHelper nothing = errorResponse "Failed to parse DBC YAML"
    parseDBCHelper (just dbc) = parseTraceHelper (parseTrace traceYAML)
      where
        parseTraceHelper : Maybe (List TimedFrame) → Response
        parseTraceHelper nothing = errorResponse "Failed to parse trace YAML"
        parseTraceHelper (just frames) = parsePropHelper (parsePythonLTL propertyYAML)
          where
            parsePropHelper : DSLParseResult → Response
            parsePropHelper (DSLError msg) = errorResponse ("Failed to parse property: " ++ msg)
            parsePropHelper (DSLSuccess pythonLTL) = translateHelper (translate pythonLTL)
              where
                translateHelper : Maybe (LTL SignalPredicate) → Response
                translateHelper nothing = errorResponse "Failed to translate property to core LTL"
                translateHelper (just ltlFormula) =
                  let result = checkProperty dbc frames ltlFormula
                  in if result
                     then successResponse "Property holds on trace" (LTLResultData true nothing)
                     else successResponse "Property violated" (LTLResultData false nothing)
