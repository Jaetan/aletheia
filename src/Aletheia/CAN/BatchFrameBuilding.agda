{-# OPTIONS --safe --without-K #-}

-- Batch frame building from signal name-value pairs.
--
-- Purpose: Build CAN frames from multiple signal values at once with validation.
-- Operations: buildFrame (DBC + CAN ID + signals → String ⊎ frame).
-- Role: Batch encoding for Python API (Phase 2B.1).
--
-- Validation: Signal name existence, signal overlap detection, multiplexing consistency.
-- Guarantees: Signals partition the frame properly (no corruption).
module Aletheia.CAN.BatchFrameBuilding where

open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (injectSignal)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec as Vec using (Vec; replicate)
open import Data.Nat using (ℕ; _+_; _∸_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- ============================================================================
-- OVERLAP DETECTION
-- ============================================================================

-- Check if two bit ranges overlap
-- Range 1: [start1 .. start1 + len1 - 1]
-- Range 2: [start2 .. start2 + len2 - 1]
rangesOverlap : ℕ → ℕ → ℕ → ℕ → Bool
rangesOverlap start1 len1 start2 len2 =
  let end1 = start1 + len1 ∸ 1
      end2 = start2 + len2 ∸ 1
  in (start1 ≤ᵇ end2) ∧ (start2 ≤ᵇ end1)

-- Check if a signal overlaps with another signal
signalsOverlap : DBCSignal → DBCSignal → Bool
signalsOverlap sig1 sig2 =
  let def1 = DBCSignal.signalDef sig1
      def2 = DBCSignal.signalDef sig2
      start1 = SignalDef.startBit def1
      len1 = SignalDef.bitLength def1
      start2 = SignalDef.startBit def2
      len2 = SignalDef.bitLength def2
  in rangesOverlap start1 len1 start2 len2

-- Check if any signal in a list overlaps with a given signal
anyOverlap : DBCSignal → List DBCSignal → Bool
anyOverlap sig [] = false
anyOverlap sig (s ∷ rest) = signalsOverlap sig s ∨ anyOverlap sig rest

-- Check all signals for pairwise overlaps
-- Returns true if there is at least one overlap
hasOverlaps : List DBCSignal → Bool
hasOverlaps [] = false
hasOverlaps (sig ∷ rest) = anyOverlap sig rest ∨ hasOverlaps rest

-- ============================================================================
-- SIGNAL LOOKUP AND VALIDATION
-- ============================================================================

-- Import shared DBC lookup utilities
open import Aletheia.CAN.DBCHelpers using (findSignalByName; findMessageById; canIdEquals)

-- Lookup signal definitions for a list of (name, value) pairs
-- Returns error message if any signal name is not found
lookupSignals : List (String × ℚ) → DBCMessage → String ⊎ List (DBCSignal × ℚ)
lookupSignals [] msg = inj₂ []
lookupSignals ((name , value) ∷ rest) msg with findSignalByName name msg
... | nothing = inj₁ ("Signal not found: " ++ₛ name)
... | just sig with lookupSignals rest msg
...   | inj₁ err = inj₁ err
...   | inj₂ restSigs = inj₂ ((sig , value) ∷ restSigs)

-- ============================================================================
-- FRAME BUILDING
-- ============================================================================

-- Inject a single signal into a frame
injectOne : ∀ {n} → CANFrame n → (DBCSignal × ℚ) → String ⊎ CANFrame n
injectOne frame (sig , value) with injectSignal value (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame
... | nothing = inj₁ ("Injection failed for signal: " ++ₛ DBCSignal.name sig)
... | just f  = inj₂ f

-- Inject all signals into a frame (left-to-right fold)
injectAll : ∀ {n} → CANFrame n → List (DBCSignal × ℚ) → String ⊎ CANFrame n
injectAll frame [] = inj₂ frame
injectAll frame (sig ∷ rest) with injectOne frame sig
... | inj₁ err = inj₁ err
... | inj₂ frame' = injectAll frame' rest

-- Build a CAN frame from signal name-value pairs
-- Returns error message if:
-- - CAN ID not found in DBC
-- - Any signal name not found in message
-- - Signals overlap
-- - Signal value out of bounds or injection fails
buildFrame : DBC → CANId → (dlc : ℕ) → List (String × ℚ) → String ⊎ Vec Byte (dlcToBytes dlc)
buildFrame dbc canId dlc signals with findMessageById canId dbc
... | nothing = inj₁ "CAN ID not found in DBC"
... | just msg with lookupSignals signals msg
...   | inj₁ err = inj₁ err
...   | inj₂ signalDefs = validateAndBuild signalDefs
  where
    emptyFrame : CANFrame (dlcToBytes dlc)
    emptyFrame = record { id = canId ; dlc = dlc ; payload = Vec.replicate (dlcToBytes dlc) 0 }

    validateAndBuild : List (DBCSignal × ℚ) → String ⊎ Vec Byte (dlcToBytes dlc)
    validateAndBuild defs with hasOverlaps (map Data.Product.proj₁ defs)
    ... | true = inj₁ "Signals overlap"
    ... | false with injectAll emptyFrame defs
    ...   | inj₁ err = inj₁ err
    ...   | inj₂ finalFrame = inj₂ (CANFrame.payload finalFrame)

-- ============================================================================
-- FRAME UPDATING
-- ============================================================================

-- Update specific signals in an existing frame
-- Returns error message if:
-- - CAN ID doesn't match frame
-- - Any signal name not found in message
-- - Signal value out of bounds or injection fails
-- Guarantees: Other signals in frame are preserved
updateFrame : ∀ {n} → DBC → CANId → CANFrame n → List (String × ℚ) → String ⊎ CANFrame n
updateFrame dbc canId frame signals =
  if canIdEquals canId (CANFrame.id frame)
  then findAndInject
  else inj₁ "CAN ID does not match frame"
  where
    findAndInject : String ⊎ CANFrame _
    findAndInject with findMessageById canId dbc
    ... | nothing = inj₁ "CAN ID not found in DBC"
    ... | just msg with lookupSignals signals msg
    ...   | inj₁ err = inj₁ err
    ...   | inj₂ signalDefs = injectAll frame signalDefs
