{-# OPTIONS --safe --without-K #-}

-- Signal predicate evaluation with cache fallback.
--
-- Purpose: Evaluate signal predicates against CAN frames with last-known-value
-- semantics via SignalCache.
-- Exports: evalPredicateTV, extractTruthValue, getTruthValue,
--   evalValuePredicateTV, evalDeltaPredicateTV, comparison helpers.
-- Role: Called by StreamState.Internals during incremental LTL checking.
module Aletheia.LTL.SignalPredicate.Evaluation where

open import Aletheia.Prelude
open import Data.Rational as Rat using (_-_; ∣_∣; _≤?_; _<?_; 0ℚ)
open import Data.Maybe as M using (map)
open import Function using (case_of_)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.SignalExtraction using (extractSignalWithContext)
open import Aletheia.CAN.ExtractionResult using (getValue)
open import Aletheia.DBC.Types using (DBC)

open import Aletheia.LTL.SignalPredicate.Types
open import Aletheia.LTL.SignalPredicate.Cache

-- ============================================================================
-- COMPARISON HELPERS
-- ============================================================================

_==ℚ_ : ℚ → ℚ → Bool
x ==ℚ y = ⌊ x Rat.≟ y ⌋

_≤ℚ_ : ℚ → ℚ → Bool
x ≤ℚ y = ⌊ x Rat.≤? y ⌋

_<ℚ_ : ℚ → ℚ → Bool
x <ℚ y = ⌊ x Rat.<? y ⌋

_>ℚ_ : ℚ → ℚ → Bool
x >ℚ y = y <ℚ x

_≥ℚ_ : ℚ → ℚ → Bool
x ≥ℚ y = y ≤ℚ x

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Extract signal value using extraction with multiplexing support
extractTruthValue : ∀ {n} → String → DBC → CANFrame n → Maybe ℚ
extractTruthValue sigName dbc frame = getValue (extractSignalWithContext dbc frame sigName)

-- ============================================================================
-- PURE PREDICATE EVALUATION (internal)
-- ============================================================================

private
  evalValuePredicate : ValuePredicate → ℚ → Bool
  evalValuePredicate (Equals _ v) x             = x ==ℚ v
  evalValuePredicate (LessThan _ v) x           = x <ℚ v
  evalValuePredicate (GreaterThan _ v) x        = x >ℚ v
  evalValuePredicate (LessThanOrEqual _ v) x    = x ≤ℚ v
  evalValuePredicate (GreaterThanOrEqual _ v) x = x ≥ℚ v
  evalValuePredicate (Between _ lo hi) x        = lo ≤ℚ x ∧ x ≤ℚ hi

  evalDeltaPredicate : DeltaPredicate → ℚ → ℚ → Bool
  evalDeltaPredicate (ChangedBy _ delta) prev curr =
    let diff = curr Rat.- prev
    in  if 0ℚ ≤ℚ delta then delta ≤ℚ diff else diff ≤ℚ delta
  evalDeltaPredicate (StableWithin _ tol) prev curr = ⌊ ∣ curr Rat.- prev ∣ Rat.≤? tol ⌋

-- ============================================================================
-- THREE-VALUED PREDICATE EVALUATION
-- ============================================================================

-- Get signal value: try frame first, then cache
getTruthValue : ∀ {n} → String → DBC → SignalCache → CANFrame n → Maybe ℚ
getTruthValue sigName dbc cache frame =
  case extractTruthValue sigName dbc frame of λ where
    (just v) → just v
    nothing  → M.map CachedSignal.value (lookupCache sigName cache)

-- Evaluate value predicate with cache fallback
evalValuePredicateTV : ∀ {n} → DBC → SignalCache → ValuePredicate → CANFrame n → TruthVal
evalValuePredicateTV dbc cache vp frame =
  case getTruthValue (valuePredicateSignal vp) dbc cache frame of λ where
    (just v) → fromBool (evalValuePredicate vp v)
    nothing  → Unknown

-- Evaluate delta predicate with cache
evalDeltaPredicateTV : ∀ {n} → DBC → SignalCache → DeltaPredicate → CANFrame n → TruthVal
evalDeltaPredicateTV dbc cache dp frame =
  let sigName = deltaPredicateSignal dp
      currVal = getTruthValue sigName dbc cache frame
      prevVal = M.map CachedSignal.value (lookupCache sigName cache)
  in case currVal of λ where
    nothing   → Unknown
    (just cv) → case prevVal of λ where
      nothing   → Pending
      (just pv) → fromBool (evalDeltaPredicate dp pv cv)

-- Evaluate any signal predicate with cache
evalPredicateTV : ∀ {n} → DBC → SignalCache → SignalPredicate → CANFrame n → TruthVal
evalPredicateTV dbc cache (ValueP vp) frame = evalValuePredicateTV dbc cache vp frame
evalPredicateTV dbc cache (DeltaP dp) frame = evalDeltaPredicateTV dbc cache dp frame
