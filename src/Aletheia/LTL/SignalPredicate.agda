{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.SignalPredicate where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.CAN.SignalExtraction
open import Aletheia.CAN.ExtractionResult
open import Aletheia.DBC.Types
open import Data.String using (String; _≟_)
open import Data.Rational as Rat using (ℚ; _/_; _-_; ∣_∣; _≤?_; _<?_)
open import Data.Integer using (+_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Fin using (toℕ)
open import Data.Nat using (_≡ᵇ_)

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
  in just ⌊ delta Rat.≤? diff ⌋

evalPredicatePair pred dbc _ currFrame = evalPredicate pred dbc currFrame

-- ============================================================================
-- MODEL CHECKER INTEGRATION
-- ============================================================================

open import Aletheia.LTL.Syntax using (LTL; mapLTL)
open import Aletheia.LTL.Semantics using (satisfiesAt)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Data.List using (List; map)

-- Evaluate predicate on a TimedFrame, defaulting to false on extraction failure
evalOnFrame : DBC → SignalPredicate → TimedFrame → Bool
evalOnFrame dbc pred timedFrame =
  let frame = TimedFrame.frame timedFrame
  in case evalPredicate pred dbc frame of λ where
       nothing → false  -- Signal extraction failed
       (just b) → b
  where
    open import Function using (case_of_)

-- Check if a trace satisfies an LTL formula
-- Transforms LTL SignalPredicate → LTL (TimedFrame → Bool) and evaluates
checkProperty : DBC → List TimedFrame → LTL SignalPredicate → Bool
checkProperty dbc frames formula =
  let -- Transform each SignalPredicate to a predicate on TimedFrame
      predToFunc : SignalPredicate → (TimedFrame → Bool)
      predToFunc pred = evalOnFrame dbc pred

      -- Transform the formula
      transformedFormula : LTL (TimedFrame → Bool)
      transformedFormula = mapLTL predToFunc formula

  in satisfiesAt frames transformedFormula
