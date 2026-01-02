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
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Always)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; LTLEvalState; AtomicState; NotState; AndState; OrState; AlwaysState; stepEval; initState)
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

  -- Not states are related if their inner states are related
  not-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (NotState st) (Not φ)

  -- And states are related if both inner states are related
  and-relate : ∀ {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (AndState st1 st2) (And φ ψ)

  -- Or states are related if both inner states are related
  or-relate : ∀ {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (OrState st1 st2) (Or φ ψ)

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

-- Propositional operators: Not
-- stepEval (Not φ) ... (NotState st) inverts the result
-- stepL (Not φ) also inverts the result
-- If inner results are bisimilar, inverted results are also bisimilar
step-bisim (not-relate {st} {φ} rel) prev curr
  with stepEval φ evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr
-- Inner violates → Not returns Satisfied
... | Violated _ | Violated _ | violated-bisim _
  = satisfied-bisim
-- Inner satisfied → Not returns Violated
... | Satisfied | Satisfied | satisfied-bisim
  = violated-bisim (mkCEEquiv refl refl)
-- Inner continues → Not continues with negated inner
... | Continue st' | Continue φ' | continue-bisim rel'
  = continue-bisim (not-relate rel')
-- Impossible cases
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ | ()
... | Continue _ | Violated _ | ()
... | Continue _ | Satisfied | ()

-- Propositional operators: And
-- This is more complex - need to handle all combinations
step-bisim (and-relate {st1} {st2} {φ} {ψ} rel1 rel2) prev curr
  with stepEval φ evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval ψ evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
-- Left violated → And violated
... | Violated ce1 | Violated ce2 | violated-bisim ceq | _ | _ | _
  = violated-bisim ceq
-- Right violated (left continues) → And violated
... | Continue st1' | Continue φ' | continue-bisim rel1' | Violated ce1 | Violated ce2 | violated-bisim ceq
  = violated-bisim ceq
-- Both continue → And continues
... | Continue st1' | Continue φ' | continue-bisim rel1' | Continue st2' | Continue ψ' | continue-bisim rel2'
  = continue-bisim (and-relate rel1' rel2')
-- Right satisfied, left continues → And continues
-- Monitor returns: AndState st1' st2 (preserves original right state!)
... | Continue st1' | Continue φ' | continue-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (and-relate rel1' rel2)
-- Left satisfied, right violated → And violated
... | Satisfied | Satisfied | satisfied-bisim | Violated ce1 | Violated ce2 | violated-bisim ceq
  = violated-bisim ceq
-- Left satisfied, right continues → And continues with right
... | Satisfied | Satisfied | satisfied-bisim | Continue st2' | Continue ψ' | continue-bisim rel2'
  = continue-bisim (and-relate rel1 rel2')
-- Both satisfied → And satisfied
... | Satisfied | Satisfied | satisfied-bisim | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
-- Left violated, right satisfied → And violated
... | Violated ce1 | Violated ce2 | violated-bisim ceq | Satisfied | Satisfied | satisfied-bisim
  = violated-bisim ceq
-- Left violated, right continues → And violated
... | Violated ce1 | Violated ce2 | violated-bisim ceq | Continue _ | Continue _ | continue-bisim _
  = violated-bisim ceq
-- Impossible cases: left results don't match
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ | () | _ | _ | _
... | Continue _ | Violated _ | () | _ | _ | _
... | Continue _ | Satisfied | () | _ | _ | _
-- Impossible cases: right results don't match
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ | ()
... | _ | _ | _ | Continue _ | Violated _ | ()
... | _ | _ | _ | Continue _ | Satisfied | ()

-- Propositional operators: Or
-- Similar structure to And
step-bisim (or-relate {st1} {st2} {φ} {ψ} rel1 rel2) prev curr
  with stepEval φ evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval ψ evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
-- Left satisfied → Or satisfied
... | Satisfied | Satisfied | satisfied-bisim | _ | _ | _
  = satisfied-bisim
-- Right satisfied (left continues) → Or satisfied
... | Continue st1' | Continue φ' | continue-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
-- Both continue → Or continues
... | Continue st1' | Continue φ' | continue-bisim rel1' | Continue st2' | Continue ψ' | continue-bisim rel2'
  = continue-bisim (or-relate rel1' rel2')
-- Right violated, left continues → Or continues with left
... | Continue st1' | Continue φ' | continue-bisim rel1' | Violated _ | Violated _ | violated-bisim _
  = continue-bisim (or-relate rel1' rel2)
-- Left violated, right satisfied → Or satisfied
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
-- Left violated, right continues → Or continues with right
... | Violated _ | Violated _ | violated-bisim _ | Continue st2' | Continue ψ' | continue-bisim rel2'
  = continue-bisim (or-relate rel1 rel2')
-- Both violated → Or violated (uses right's counterexample)
... | Violated _ | Violated _ | violated-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq
-- Impossible cases: left results don't match
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ | () | _ | _ | _
... | Continue _ | Violated _ | () | _ | _ | _
... | Continue _ | Satisfied | () | _ | _ | _
-- Impossible cases: right results don't match
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ | ()
... | _ | _ | _ | Continue _ | Violated _ | ()
... | _ | _ | _ | Continue _ | Satisfied | ()

-- Temporal operators: Always
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
