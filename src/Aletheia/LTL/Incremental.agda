{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.Incremental where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_)
open import Aletheia.LTL.Syntax
open import Aletheia.Trace.Context using (TimedFrame; timestamp)

-- ============================================================================
-- INCREMENTAL LTL CHECKING
-- ============================================================================

-- Process frames one at a time with early termination.
-- Key features:
-- 1. Early termination: stops when result is known
-- 2. Short-circuit evaluation for And/Or
-- 3. Structurally recursive on formula tree

-- ============================================================================
-- EVALUATE NON-TEMPORAL FORMULAS
-- ============================================================================

-- Evaluate formula at a single frame (handles Atomic, Not, And, Or)
-- Temporal operators return false (they need the full trace)
-- Structurally recursive on the formula
evalAtFrame : ∀ {A : Set} → A → LTL (A → Bool) → Bool
evalAtFrame frame (Atomic pred) = pred frame
evalAtFrame frame (Not φ) = not (evalAtFrame frame φ)
evalAtFrame frame (And φ ψ) = evalAtFrame frame φ ∧ evalAtFrame frame ψ
evalAtFrame frame (Or φ ψ) = evalAtFrame frame φ ∨ evalAtFrame frame ψ
evalAtFrame _ (Next _) = false
evalAtFrame _ (Always _) = false  -- Needs all frames
evalAtFrame _ (Eventually _) = false  -- Needs future frames
evalAtFrame _ (Until _ _) = false
evalAtFrame _ (EventuallyWithin _ _) = false
evalAtFrame _ (AlwaysWithin _ _) = false


-- ============================================================================
-- MAIN INCREMENTAL CHECKER
-- ============================================================================

-- Check a formula on a list with early termination
-- Structurally recursive on both formula and list
checkIncremental : List TimedFrame → LTL (TimedFrame → Bool) → Bool
checkIncremental [] _ = true  -- Empty trace: vacuously true
checkIncremental frames@(first ∷ _) φ = checkFormula frames φ
  where
    start = timestamp first

    -- Main recursive checker (structural on formula)
    checkFormula : List TimedFrame → LTL (TimedFrame → Bool) → Bool

    -- Atomic: check first frame
    checkFormula [] (Atomic _) = true  -- Empty = vacuous
    checkFormula (tf ∷ _) (Atomic pred) = pred tf

    -- Not: invert
    checkFormula trace (Not ψ) = not (checkFormula trace ψ)

    -- And: both must hold (short-circuit on failure)
    checkFormula trace (And ψ₁ ψ₂) =
      if checkFormula trace ψ₁
      then checkFormula trace ψ₂
      else false

    -- Or: either must hold (short-circuit on success)
    checkFormula trace (Or ψ₁ ψ₂) =
      if checkFormula trace ψ₁
      then true
      else checkFormula trace ψ₂

    -- Next: check second frame
    checkFormula [] (Next _) = true
    checkFormula (_ ∷ []) (Next _) = true
    checkFormula (_ ∷ rest) (Next ψ) = checkFormula rest ψ

    -- Always: must hold on all frames (early termination on violation)
    checkFormula trace (Always ψ) = goAlways trace
      where
        goAlways : List TimedFrame → Bool
        goAlways [] = true
        goAlways (tf ∷ rest) =
          if evalAtFrame tf ψ
          then goAlways rest  -- Continue checking
          else false          -- Violated! Early termination

    -- Eventually: must hold somewhere (early termination on satisfaction)
    checkFormula trace (Eventually ψ) = goEventually trace
      where
        goEventually : List TimedFrame → Bool
        goEventually [] = false  -- Never satisfied
        goEventually (tf ∷ rest) =
          if evalAtFrame tf ψ
          then true               -- Found! Early termination
          else goEventually rest  -- Keep looking

    -- Until: φ until ψ
    checkFormula trace (Until ψ₁ ψ₂) = goUntil trace
      where
        goUntil : List TimedFrame → Bool
        goUntil [] = false  -- ψ₂ never held
        goUntil (tf ∷ rest) =
          if evalAtFrame tf ψ₂
          then true  -- ψ₂ holds, satisfied
          else if evalAtFrame tf ψ₁
               then goUntil rest  -- ψ₁ holds, keep waiting
               else false         -- Neither holds, violated

    -- EventuallyWithin: must hold within time window
    checkFormula trace (EventuallyWithin windowMicros ψ) = goEW trace
      where
        goEW : List TimedFrame → Bool
        goEW [] = false
        goEW (tf ∷ rest) =
          -- Check time window FIRST
          if (timestamp tf ∸ start) ≤ᵇ windowMicros
          then if evalAtFrame tf ψ
               then true           -- Found within window!
               else goEW rest      -- Keep looking
          else false               -- Window expired

    -- AlwaysWithin: must hold throughout time window
    checkFormula trace (AlwaysWithin windowMicros ψ) = goAW trace
      where
        goAW : List TimedFrame → Bool
        goAW [] = true
        goAW (tf ∷ rest) =
          -- Check time window FIRST
          if (timestamp tf ∸ start) ≤ᵇ windowMicros
          then if evalAtFrame tf ψ
               then goAW rest      -- Still in window, keep checking
               else false          -- Violated within window!
          else true                -- Window complete, done checking

-- ============================================================================
-- MULTI-PROPERTY CHECKING
-- ============================================================================

-- Check multiple properties on the same trace
-- Each property uses early termination independently
-- Returns list of results in same order as input properties
checkMultiple : List TimedFrame → List (LTL (TimedFrame → Bool)) → List Bool
checkMultiple trace [] = []
checkMultiple trace (φ ∷ rest) = checkIncremental trace φ ∷ checkMultiple trace rest

-- Primary interface for streaming check
checkListStreaming : List TimedFrame → LTL (TimedFrame → Bool) → Bool
checkListStreaming = checkIncremental

-- ============================================================================
-- COUNTEREXAMPLE GENERATION
-- ============================================================================

-- Counterexample: evidence of why a property failed
record Counterexample : Set where
  constructor mkCounterexample
  field
    violatingFrame : TimedFrame    -- The frame where violation occurred
    reason : String                -- Human-readable explanation

-- Result of checking with counterexample support
data CheckResult : Set where
  Pass : CheckResult
  Fail : Counterexample → CheckResult

-- Check formula and return counterexample on failure
checkWithCounterexample : List TimedFrame → LTL (TimedFrame → Bool) → CheckResult
checkWithCounterexample [] _ = Pass  -- Empty trace: vacuously true
checkWithCounterexample frames@(first ∷ _) φ = checkFormulaCE frames φ
  where
    start = timestamp first

    -- Main recursive checker returning counterexamples
    checkFormulaCE : List TimedFrame → LTL (TimedFrame → Bool) → CheckResult

    -- Atomic: check first frame
    checkFormulaCE [] (Atomic _) = Pass
    checkFormulaCE (tf ∷ _) (Atomic pred) =
      if pred tf then Pass
      else Fail (mkCounterexample tf "atomic predicate failed")

    -- Not: invert (counterexample from inner becoming pass means outer fails)
    checkFormulaCE trace (Not ψ) with checkFormulaCE trace ψ
    ... | Pass = Fail (mkCounterexample first "negation failed (inner property held)")
    ... | Fail _ = Pass

    -- And: both must hold
    checkFormulaCE trace (And ψ₁ ψ₂) with checkFormulaCE trace ψ₁
    ... | Fail ce = Fail ce
    ... | Pass = checkFormulaCE trace ψ₂

    -- Or: either must hold
    checkFormulaCE trace (Or ψ₁ ψ₂) with checkFormulaCE trace ψ₁
    ... | Pass = Pass
    ... | Fail ce₁ with checkFormulaCE trace ψ₂
    ...   | Pass = Pass
    ...   | Fail ce₂ = Fail ce₂  -- Return second counterexample

    -- Next: check second frame
    checkFormulaCE [] (Next _) = Pass
    checkFormulaCE (_ ∷ []) (Next _) = Pass
    checkFormulaCE (_ ∷ rest) (Next ψ) = checkFormulaCE rest ψ

    -- Always: must hold on all frames
    checkFormulaCE trace (Always ψ) = goAlwaysCE trace
      where
        goAlwaysCE : List TimedFrame → CheckResult
        goAlwaysCE [] = Pass
        goAlwaysCE (tf ∷ rest) =
          if evalAtFrame tf ψ
          then goAlwaysCE rest
          else Fail (mkCounterexample tf "Always violated")

    -- Eventually: must hold somewhere
    checkFormulaCE trace (Eventually ψ) = goEventuallyCE trace
      where
        goEventuallyCE : List TimedFrame → CheckResult
        goEventuallyCE [] = Fail (mkCounterexample first "Eventually never satisfied")
        goEventuallyCE (tf ∷ rest) =
          if evalAtFrame tf ψ
          then Pass
          else goEventuallyCE rest

    -- Until: φ until ψ
    checkFormulaCE trace (Until ψ₁ ψ₂) = goUntilCE trace
      where
        goUntilCE : List TimedFrame → CheckResult
        goUntilCE [] = Fail (mkCounterexample first "Until: second condition never held")
        goUntilCE (tf ∷ rest) =
          if evalAtFrame tf ψ₂
          then Pass
          else if evalAtFrame tf ψ₁
               then goUntilCE rest
               else Fail (mkCounterexample tf "Until: first condition failed before second held")

    -- EventuallyWithin: must hold within time window
    checkFormulaCE trace (EventuallyWithin windowMicros ψ) = goEWCE trace
      where
        goEWCE : List TimedFrame → CheckResult
        goEWCE [] = Fail (mkCounterexample first "EventuallyWithin: never satisfied")
        goEWCE (tf ∷ rest) =
          if (timestamp tf ∸ start) ≤ᵇ windowMicros
          then if evalAtFrame tf ψ
               then Pass
               else goEWCE rest
          else Fail (mkCounterexample tf "EventuallyWithin: window expired")

    -- AlwaysWithin: must hold throughout time window
    checkFormulaCE trace (AlwaysWithin windowMicros ψ) = goAWCE trace
      where
        goAWCE : List TimedFrame → CheckResult
        goAWCE [] = Pass
        goAWCE (tf ∷ rest) =
          if (timestamp tf ∸ start) ≤ᵇ windowMicros
          then if evalAtFrame tf ψ
               then goAWCE rest
               else Fail (mkCounterexample tf "AlwaysWithin: violated within window")
          else Pass

-- Helper to extract counterexample if present
getCounterexample : CheckResult → Maybe Counterexample
getCounterexample Pass = nothing
getCounterexample (Fail ce) = just ce

-- Helper to check if result is pass
isPass : CheckResult → Bool
isPass Pass = true
isPass (Fail _) = false
