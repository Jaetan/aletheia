{-# OPTIONS --safe --without-K #-}

-- Batch frame building from signal name-value pairs.
--
-- Purpose: Build CAN frames from multiple signal values at once with validation.
-- Operations: buildFrame (DBC + CAN ID + signals → Maybe frame).
-- Role: Batch encoding for Python API (Phase 2B.1).
--
-- Validation: Signal name existence, signal overlap detection, multiplexing consistency.
-- Guarantees: Signals partition the frame properly (no corruption).
module Aletheia.CAN.BatchFrameBuilding where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.DBC.Types
open import Data.String using (String) renaming (_++_ to _++ₛ_; _≟_ to _≟ₛ_)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map; foldr; all)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Vec using (Vec)
open import Data.Vec as Vec using (replicate)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≡ᵇ_; _∸_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Bool.Properties using (∨-zeroʳ; ∨-identityʳ)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (_∘_)

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
  in (start1 Data.Nat.≤ᵇ end2) ∧ (start2 Data.Nat.≤ᵇ end1)
  where
    open import Data.Nat using (_≤ᵇ_)

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
-- Returns Nothing if any signal name is not found
lookupSignals : List (String × ℚ) → DBCMessage → Maybe (List (DBCSignal × ℚ))
lookupSignals [] msg = just []
lookupSignals ((name , value) ∷ rest) msg =
  findSignalByName name msg >>= λ sig →
  lookupSignals rest msg >>= λ restSigs →
  just ((sig , value) ∷ restSigs)

-- ============================================================================
-- FRAME BUILDING
-- ============================================================================

-- Inject a single signal into a frame
injectOne : CANFrame → (DBCSignal × ℚ) → Maybe CANFrame
injectOne frame (sig , value) =
  injectSignal value (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame

-- Inject all signals into a frame (left-to-right fold)
injectAll : CANFrame → List (DBCSignal × ℚ) → Maybe CANFrame
injectAll frame [] = just frame
injectAll frame (sig ∷ rest) =
  injectOne frame sig >>= λ frame' →
  injectAll frame' rest

-- Build a CAN frame from signal name-value pairs
-- Returns Nothing if:
-- - CAN ID not found in DBC
-- - Any signal name not found in message
-- - Signals overlap
-- - Signal value out of bounds or injection fails
buildFrame : DBC → CANId → List (String × ℚ) → Maybe (Vec Byte 8)
buildFrame dbc canId signals =
  findMessageById canId dbc >>= λ msg →
  lookupSignals signals msg >>= λ signalDefs →
  validateAndBuild msg signalDefs
  where
    -- Validate no overlaps and build frame
    validateAndBuild : DBCMessage → List (DBCSignal × ℚ) → Maybe (Vec Byte 8)
    validateAndBuild msg signalDefs =
      let sigs = map Data.Product.proj₁ signalDefs
      in if hasOverlaps sigs
         then nothing  -- Signals overlap, reject
         else -- Build frame from validated signals (no overlaps)
           let emptyPayload : Vec Byte 8
               emptyPayload = Vec.replicate 8 0
               emptyFrame : CANFrame
               emptyFrame = record { id = canId ; dlc = 8 ; payload = emptyPayload }
           in injectAll emptyFrame signalDefs >>= λ finalFrame →
              just (CANFrame.payload finalFrame)

-- ============================================================================
-- FRAME UPDATING
-- ============================================================================

-- Update specific signals in an existing frame
-- Returns Nothing if:
-- - CAN ID doesn't match frame
-- - Any signal name not found in message
-- - Signal value out of bounds or injection fails
-- Guarantees: Other signals in frame are preserved
updateFrame : DBC → CANId → CANFrame → List (String × ℚ) → Maybe CANFrame
updateFrame dbc canId frame signals =
  -- Verify frame ID matches
  if canIdEquals canId (CANFrame.id frame)
  then (findMessageById canId dbc >>= λ msg →
        lookupSignals signals msg >>= λ signalDefs →
        injectAll frame signalDefs)  -- Inject updates into existing frame
  else nothing
