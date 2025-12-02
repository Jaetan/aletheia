{-# OPTIONS --safe --without-K #-}

-- High-level signal extraction using DBC context.
--
-- Purpose: Extract signals from frames by name using DBC definitions.
-- Operations: extractSignalByName (DBC + frame + signal name → value).
-- Role: User-facing API combining DBC lookup with CAN.Encoding.
--
-- Workflow: Lookup signal definition in DBC → validate frame ID → extract bits → scale.
module Aletheia.CAN.SignalExtraction where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.CAN.ExtractionResult
open import Aletheia.DBC.Types
open import Data.String using (String; _++_)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Data.Rational using (ℚ; _/_)
open import Data.Rational.Properties renaming (_≟_ to _≟ᵣ_)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (toℕ)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

canIdEquals : CANId → CANId → Bool
canIdEquals (Standard x) (Standard y) = toℕ x ≡ᵇ toℕ y
canIdEquals (Extended x) (Extended y) = toℕ x ≡ᵇ toℕ y
canIdEquals _ _ = false

findInList : ∀ {A : Set} → (A → Bool) → List A → Maybe A
findInList pred [] = nothing
findInList pred (x ∷ xs) = if pred x then just x else findInList pred xs

findMessageById : CANId → DBC → Maybe DBCMessage
findMessageById msgId dbc = findInList matchesId (DBC.messages dbc)
  where
    matchesId : DBCMessage → Bool
    matchesId msg = canIdEquals msgId (DBCMessage.id msg)

findSignalByName : String → DBCMessage → Maybe DBCSignal
findSignalByName name msg = findInList matchesName (DBCMessage.signals msg)
  where
    matchesName : DBCSignal → Bool
    matchesName sig = ⌊ DBCSignal.name sig ≟ₛ name ⌋

-- ============================================================================
-- SIGNAL EXTRACTION WITH MULTIPLEXING
-- ============================================================================

-- Check if signal is present in frame (handles multiplexing)
-- Returns: nothing if present, just reason if not present
checkSignalPresence : CANFrame → DBCMessage → DBCSignal → Maybe String
checkSignalPresence frame msg sig with DBCSignal.presence sig
... | Always = nothing  -- Signal always present, no error
... | When muxName muxValue with findSignalByName muxName msg
...   | nothing = just ("multiplexor signal '" ++ muxName ++ "' not found in message")
...   | just muxSig with extractSignal frame (DBCSignal.signalDef muxSig) (DBCSignal.byteOrder muxSig)
...     | nothing = just ("failed to extract multiplexor signal '" ++ muxName ++ "'")
...     | just muxVal =
          -- Check if multiplexor value matches
          -- Note: We compare to rational directly since muxValue is ℕ
          let expectedVal = (+ muxValue) / 1
              matches = ⌊ muxVal ≟ᵣ expectedVal ⌋
          in if matches
             then nothing  -- Match! Signal is present
             else just ("multiplexor value mismatch (expected " ++ showℕ muxValue ++ ")")

-- Extract signal value from frame with full error reporting
-- This is the primary interface for signal extraction
extractSignalWithContext : DBC → CANFrame → String → ExtractionResult
extractSignalWithContext dbc frame signalName with findMessageById (CANFrame.id frame) dbc
... | nothing = SignalNotInDBC signalName
... | just msg with findSignalByName signalName msg
...   | nothing = SignalNotInDBC signalName
...   | just sig with checkSignalPresence frame msg sig
...     | just reason = SignalNotPresent signalName reason
...     | nothing with extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
...       | nothing =
            -- Extraction failed - could be out of bounds or bit extraction failure
            -- TODO Phase 3: Distinguish these two cases in extractSignal
            ExtractionFailed signalName ("value out of bounds or extraction error")
...       | just value = Success value

-- Backward compatibility: Maybe interface
extractSignalMaybe : DBC → CANFrame → String → Maybe ℚ
extractSignalMaybe dbc frame sigName = getValue (extractSignalWithContext dbc frame sigName)
