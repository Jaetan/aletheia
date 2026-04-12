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
open import Data.Rational as Rat using (_-_; ∣_∣; 0ℚ; _≤ᵇ_)
open import Data.Maybe using (_<∣>_) renaming (map to mapₘ)
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

-- Bool-valued comparisons via `Rat._≤ᵇ_`, which compiles to a direct ℤ
-- comparison without allocating a `Dec` proof term per call. Replacing the
-- previous `⌊ _≟ _ ⌋` / `⌊ _≤? _ ⌋` / `⌊ _<? _ ⌋` forms is a MAlonzo hot-path
-- win of the same class as the 2026-04-07 `signalsPhysicallyOverlapᵇ` fix.
-- See `feedback_hot_path_refactor_benchmark.md` and the equivalence proofs in
-- `DBC/Properties/Disjointness.agda` for the template.

_==ℚ_ : ℚ → ℚ → Bool
x ==ℚ y = (x ≤ᵇ y) ∧ (y ≤ᵇ x)

_≤ℚ_ : ℚ → ℚ → Bool
x ≤ℚ y = x ≤ᵇ y

_<ℚ_ : ℚ → ℚ → Bool
x <ℚ y = (x ≤ᵇ y) ∧ not (y ≤ᵇ x)

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
-- PURE PREDICATE EVALUATION
-- ============================================================================
--
-- These are exposed (no longer private) so that Evaluation/Properties.agda can
-- state definiteness lemmas by case-splitting on their Bool outputs. They
-- characterize the raw predicate semantics over definite (already extracted)
-- values; the *TV wrappers below add cache fallback and Unknown/Pending.

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
evalDeltaPredicate (StableWithin _ tol) prev curr = ∣ curr Rat.- prev ∣ ≤ℚ tol

-- ============================================================================
-- THREE-VALUED PREDICATE EVALUATION
-- ============================================================================

-- Get signal value: try frame first, then cache (via Maybe's _<∣>_ alternative).
getTruthValue : ∀ {n} → String → DBC → SignalCache → CANFrame n → Maybe ℚ
getTruthValue sigName dbc cache frame =
  extractTruthValue sigName dbc frame <∣> mapₘ CachedSignal.value (lookupCache sigName cache)

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
      prevVal = mapₘ CachedSignal.value (lookupCache sigName cache)
  in case currVal of λ where
    nothing   → Unknown
    (just cv) → case prevVal of λ where
      nothing   → Pending
      (just pv) → fromBool (evalDeltaPredicate dp pv cv)

-- Evaluate any signal predicate with cache
evalPredicateTV : ∀ {n} → DBC → SignalCache → SignalPredicate → CANFrame n → TruthVal
evalPredicateTV dbc cache (ValueP vp) frame = evalValuePredicateTV dbc cache vp frame
evalPredicateTV dbc cache (DeltaP dp) frame = evalDeltaPredicateTV dbc cache dp frame
