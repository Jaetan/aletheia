{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.Incremental where

open import Aletheia.Prelude
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
