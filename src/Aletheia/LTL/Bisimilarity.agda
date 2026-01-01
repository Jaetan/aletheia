{-# OPTIONS --safe --without-K #-}

-- Bisimilarity proof between monitor and defunctionalized LTL
--
-- Purpose: Prove that the incremental state machine (stepEval) and
-- the defunctionalized LTL coalgebra (stepL) produce bisimilar observations.
--
-- Strategy: Start with Always (Atomic p) as base case, then extend to other operators.
--
-- Key insight: We prove behavioral equivalence, not propositional equality!
-- This avoids all extended lambda problems.

module Aletheia.LTL.Bisimilarity where

open import Aletheia.Prelude
open import Aletheia.LTL.Syntax using (LTL; Atomic; Always)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; LTLEvalState; AtomicState; AlwaysState; stepEval; initState)
open import Aletheia.LTL.Coalgebra using (LTLProc; stepL)
open import Aletheia.LTL.StepResultBisim using (StepResultBisim; violated-bisim; satisfied-bisim; continue-bisim; CounterexampleEquiv; mkCEEquiv)
open import Aletheia.LTL.CoalgebraBisim using (CoalgebraBisim)
open import Aletheia.Trace.Context using (TimedFrame)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- RELATE RELATION: When are states behaviorally equivalent?
-- ============================================================================

-- Two states are related if they will produce the same observations on all future frames.
--
-- For Always (Atomic p):
-- - Monitor state: AlwaysState AtomicState
-- - Defunctionalized: Always (Atomic p)
-- These are related because they both check p at each frame and continue if it holds.

data Relate : LTLEvalState → LTLProc → Set where
  -- Atomic predicate states are related
  atomic-relate : ∀ {p : TimedFrame → Bool}
    → Relate AtomicState (Atomic p)

  -- Always states are related if their inner states are related
  always-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (AlwaysState st) (Always φ)

-- ============================================================================
-- STEP BISIMILARITY: Related states produce bisimilar observations
-- ============================================================================

-- Helper: Predicate evaluator for the monitor (needed for stepEval)
evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → Bool) → Bool
evalAtomicPred prev curr p = p curr

-- Prove that related states produce bisimilar observations when stepped with the same frame
step-bisim : ∀ {st : LTLEvalState} {proc : LTLProc}
  → Relate st proc
  → ∀ (prev : Maybe TimedFrame) (curr : TimedFrame)
  → StepResultBisim Relate
      (stepEval proc evalAtomicPred st prev curr)
      (stepL proc prev curr)

-- Base case: Atomic predicates
-- Both evaluate p at current frame, return Satisfied or Violated
step-bisim (atomic-relate {p}) prev curr
  with p curr
... | true = satisfied-bisim
... | false = violated-bisim (mkCEEquiv refl refl)

-- Inductive case: Always
-- This is the key case!
--
-- stepEval (Always φ) ... (AlwaysState st) prev curr:
--   with stepEval φ ... st prev curr
--   | Violated ce → Violated ce
--   | Satisfied → Continue (AlwaysState st)
--   | Continue st' → Continue (AlwaysState st')
--
-- stepL (Always φ) prev curr:
--   with stepL φ prev curr
--   | Violated ce → Violated ce
--   | Satisfied → Continue (Always φ)
--   | Continue φ' → Continue (Always φ')
--
-- We need to show these are bisimilar given that st and φ are related.

step-bisim (always-relate {st} {φ} rel) prev curr
  with stepEval φ evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr

-- Case 1: Inner formula violates
-- Both return Violated with same counterexample
... | Violated ce₁ | Violated ce₂ | violated-bisim ceq
  = violated-bisim ceq

-- Case 2: Inner formula satisfied
-- stepEval returns: Continue (AlwaysState st)
-- stepL returns: Continue (Always φ)
-- These are related by: always-relate rel (original relation preserved!)
... | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (always-relate rel)

-- Case 3: Inner formula continues
-- stepEval returns: Continue (AlwaysState st')
-- stepL returns: Continue (Always φ')
-- These are related by: always-relate rel' (where rel' relates st' and φ')
... | Continue st' | Continue φ' | continue-bisim rel'
  = continue-bisim (always-relate rel')

-- Impossible cases (where observations don't match)
-- Agda can prove these are impossible via unification!
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ | ()
... | Continue _ | Violated _ | ()
... | Continue _ | Satisfied | ()

-- ============================================================================
-- 🎉 SUCCESS! This proof type-checks!
-- ============================================================================

-- What we proved:
-- - For Always (Atomic p), the monitor and defunctionalized LTL produce bisimilar observations
-- - This is WITHOUT any postulates for extended lambda equality!
-- - Pure coalgebraic reasoning with behavioral equivalence
--
-- Key insights from this proof:
-- 1. Defunctionalization works! No extended lambdas needed.
-- 2. The impossible cases are automatically proven by Agda via unification
-- 3. The three valid cases (Violated, Satisfied, Continue) all work smoothly
--
-- Next steps:
-- 1. Generalize to Always φ for ANY LTL formula φ (not just Atomic p)
-- 2. Prove bisimilarity for other operators (Eventually, Not, And, Or, etc.)
-- 3. Build up the full CoalgebraBisim instance

-- ============================================================================
-- TODO: Generalize to Always φ
-- ============================================================================

-- The current proof works for Always (Atomic p).
-- To generalize to Always φ for any φ, we need:
-- 1. Extend Relate to handle all LTL formulas (not just Atomic and Always)
-- 2. Prove step-bisim for all formula cases
-- 3. Then the Always case will work for any φ by induction
--
-- This requires proving bisimilarity for:
-- - Atomic (done above)
-- - Not φ (should be straightforward)
-- - And φ ψ (should be straightforward)
-- - Or φ ψ (should be straightforward)
-- - Next φ (needs state extension for "have we skipped?")
-- - Eventually φ (similar to Always)
-- - Until φ ψ (more complex, but same pattern)
-- - EventuallyWithin, AlwaysWithin (need state extension for time tracking)
