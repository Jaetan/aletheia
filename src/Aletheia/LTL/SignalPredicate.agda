{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.SignalPredicate where

open import Aletheia.Prelude
open import Data.Rational as Rat using (_/_; _-_; ∣_∣; _≤?_; _<?_)
open import Data.Maybe using (_>>=_)

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.CAN.SignalExtraction
open import Aletheia.CAN.ExtractionResult
open import Aletheia.DBC.Types
open import Aletheia.LTL.Syntax using (LTL; mapLTL)
open import Aletheia.LTL.Incremental using (checkListStreaming; checkWithCounterexample; CheckResult; Pass; Fail; Counterexample)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- ============================================================================
-- SIGNAL PREDICATES
-- ============================================================================

-- Predicates that can be evaluated over signal values
data SignalPredicate : Set where
  Equals      : (signalName : String) → (value : ℚ) → SignalPredicate
  LessThan    : (signalName : String) → (value : ℚ) → SignalPredicate
  GreaterThan : (signalName : String) → (value : ℚ) → SignalPredicate
  Between     : (signalName : String) → (min : ℚ) → (max : ℚ) → SignalPredicate
  ChangedBy   : (signalName : String) → (delta : ℚ) → SignalPredicate

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Extract signal value using new extraction with multiplexing support
-- Returns Maybe ℚ for backward compatibility, but uses rich error types internally
extractSignalValue : String → DBC → CANFrame → Maybe ℚ
extractSignalValue sigName dbc frame = getValue (extractSignalWithContext dbc frame sigName)

-- ============================================================================
-- COMPARISON HELPERS
-- ============================================================================

-- Efficient Boolean comparison operators
-- These are wrappers around decidable comparisons for runtime checking.
-- Phase 3 can use the decidable versions (_≤?_, _≟_, etc.) for proofs.

_==ℚ_ : ℚ → ℚ → Bool
x ==ℚ y = ⌊ x Rat.≟ y ⌋

_≤ℚ_ : ℚ → ℚ → Bool
x ≤ℚ y = ⌊ x Rat.≤? y ⌋

-- Efficient strict comparison (single check, not double)
_<ℚ_ : ℚ → ℚ → Bool
x <ℚ y = ⌊ x Rat.<? y ⌋

_>ℚ_ : ℚ → ℚ → Bool
x >ℚ y = y <ℚ x

_≥ℚ_ : ℚ → ℚ → Bool
x ≥ℚ y = y ≤ℚ x

-- ============================================================================
-- PREDICATE EVALUATION
-- ============================================================================

evalPredicate : SignalPredicate → DBC → CANFrame → Maybe Bool
evalPredicate (Equals sigName value) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (sigVal ==ℚ value)

evalPredicate (LessThan sigName value) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (sigVal <ℚ value)

evalPredicate (GreaterThan sigName value) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (sigVal >ℚ value)

evalPredicate (Between sigName minVal maxVal) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (minVal ≤ℚ sigVal ∧ sigVal ≤ℚ maxVal)

evalPredicate (ChangedBy sigName delta) dbc frame = nothing

evalPredicatePair : SignalPredicate → DBC → CANFrame → CANFrame → Maybe Bool
evalPredicatePair (ChangedBy sigName delta) dbc prevFrame currFrame =
  extractSignalValue sigName dbc prevFrame >>= λ prevVal →
  extractSignalValue sigName dbc currFrame >>= λ currVal →
  let diff = ∣ currVal Rat.- prevVal ∣
  in just ⌊ diff Rat.≤? delta ⌋

evalPredicatePair pred dbc _ currFrame = evalPredicate pred dbc currFrame

-- ============================================================================
-- MODEL CHECKER INTEGRATION
-- ============================================================================

-- Find the previous frame in a trace (by matching timestamp)
-- Returns nothing if this is the first frame or not found
findPrevFrame : TimedFrame → List TimedFrame → Maybe TimedFrame
findPrevFrame _ [] = nothing
findPrevFrame _ (_ ∷ []) = nothing
findPrevFrame curr (prev ∷ next ∷ rest) =
  if TimedFrame.timestamp next ≡ᵇ TimedFrame.timestamp curr
  then just prev
  else findPrevFrame curr (next ∷ rest)

-- Evaluate predicate on a TimedFrame with access to previous frame for ChangedBy
-- For ChangedBy: looks up previous frame in trace
-- For other predicates: uses single-frame evaluation
evalOnFrameWithTrace : DBC → List TimedFrame → SignalPredicate → TimedFrame → Bool
evalOnFrameWithTrace dbc trace pred@(ChangedBy _ _) currFrame
  with findPrevFrame currFrame trace
... | nothing = true  -- No previous frame (first in trace) - vacuously true
... | just prevTF
  with evalPredicatePair pred dbc (TimedFrame.frame prevTF) (TimedFrame.frame currFrame)
... | nothing = false
... | just b = b

evalOnFrameWithTrace dbc _ pred timedFrame
  with evalPredicate pred dbc (TimedFrame.frame timedFrame)
... | nothing = false  -- Signal extraction failed
... | just b = b

-- Check if a trace satisfies an LTL formula
-- Transforms LTL SignalPredicate → LTL (TimedFrame → Bool) and evaluates
-- Uses incremental checker with early termination for large traces
-- ChangedBy predicates use previous frame lookup
checkProperty : DBC → List TimedFrame → LTL SignalPredicate → Bool
checkProperty dbc frames formula =
  let -- Transform each SignalPredicate to a predicate on TimedFrame
      -- Captures trace for ChangedBy previous frame lookup
      predToFunc : SignalPredicate → (TimedFrame → Bool)
      predToFunc pred = evalOnFrameWithTrace dbc frames pred

      -- Transform the formula
      transformedFormula : LTL (TimedFrame → Bool)
      transformedFormula = mapLTL predToFunc formula

  -- Use incremental checker with early termination
  in checkListStreaming frames transformedFormula

-- Check property and return counterexample on failure
-- Returns CheckResult with violating frame and reason
checkPropertyWithCounterexample : DBC → List TimedFrame → LTL SignalPredicate → CheckResult
checkPropertyWithCounterexample dbc frames formula =
  let predToFunc : SignalPredicate → (TimedFrame → Bool)
      predToFunc pred = evalOnFrameWithTrace dbc frames pred

      transformedFormula : LTL (TimedFrame → Bool)
      transformedFormula = mapLTL predToFunc formula

  in checkWithCounterexample frames transformedFormula
