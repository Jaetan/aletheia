{-# OPTIONS --safe --without-K #-}

-- High-level signal extraction using DBC context.
--
-- Purpose: Extract signals from frames by name using DBC definitions.
-- Operations: extractSignalWithContext (DBC + frame + signal name → ExtractionResult).
-- Role: User-facing API combining DBC lookup with CAN.Encoding.
--
-- Workflow: Lookup signal definition in DBC → validate frame ID → extract bits → scale.
module Aletheia.CAN.SignalExtraction where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (extractSignal; extractSignalCore; scaleExtracted; extractionBytes)
open import Aletheia.CAN.Encoding.Arithmetic using (inBounds)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds)
open import Aletheia.CAN.DBCHelpers using (findMessageById; findSignalByName)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; Always; When)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ; _/_)
import Data.Rational.Properties as ℚ-Props
open import Data.Integer using (+_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- ============================================================================
-- SIGNAL EXTRACTION WITH MULTIPLEXING
-- ============================================================================

-- Check if multiplexor signal matches expected value
-- Returns: nothing if match, just reason if mismatch or error
checkMultiplexor : ∀ {n} → CANFrame n → DBCMessage → String → ℕ → Maybe String
checkMultiplexor frame msg muxName muxValue with findSignalByName muxName msg
... | nothing = just ("multiplexor signal '" ++ₛ muxName ++ₛ "' not found in message")
... | just muxSig with extractSignal frame (DBCSignal.signalDef muxSig) (DBCSignal.byteOrder muxSig)
...   | nothing = just ("failed to extract multiplexor signal '" ++ₛ muxName ++ₛ "'")
...   | just muxVal =
      -- Check if multiplexor value matches expected value
      -- Note: We compare to rational directly since muxValue is ℕ
      let expectedVal = (+ muxValue) / 1
          matches = ⌊ ℚ-Props._≟_ muxVal expectedVal ⌋
      in if matches
         then nothing  -- Match! Signal is present
         else just ("multiplexor value mismatch (expected " ++ₛ showℕ muxValue ++ₛ ")")

-- Check if signal is present in frame (handles multiplexing)
-- Returns: nothing if present, just reason if not present
checkSignalPresence : ∀ {n} → CANFrame n → DBCMessage → DBCSignal → Maybe String
checkSignalPresence frame msg sig with DBCSignal.presence sig
... | Always = nothing  -- Signal always present, no error
... | When muxName muxValue = checkMultiplexor frame msg muxName muxValue

-- Extract signal value from frame with full error reporting
-- This is the primary interface for signal extraction
extractSignalWithContext : ∀ {n} → DBC → CANFrame n → String → ExtractionResult
extractSignalWithContext dbc frame signalName with findMessageById (CANFrame.id frame) dbc
... | nothing = SignalNotInDBC signalName
... | just msg with findSignalByName signalName msg
...   | nothing = SignalNotInDBC signalName
...   | just sig with checkSignalPresence frame msg sig
...     | just reason = SignalNotPresent signalName reason
...     | nothing =
            -- Use core extraction functions to get detailed error info
            let sigDef = DBCSignal.signalDef sig
                bo = DBCSignal.byteOrder sig
                bytes = extractionBytes frame bo
                raw = extractSignalCore bytes sigDef
                value = scaleExtracted raw sigDef
                minVal = SignalDef.minimum sigDef
                maxVal = SignalDef.maximum sigDef
            in if inBounds value minVal maxVal
               then Success value
               else ValueOutOfBounds signalName value minVal maxVal

