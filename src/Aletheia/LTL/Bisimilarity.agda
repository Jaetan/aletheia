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
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Always; Eventually)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; LTLEvalState; AtomicState; NotState; AndState; OrState; AlwaysState; EventuallyState; stepEval; initState)
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

  -- Eventually states are related if their inner states are related
  eventually-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (EventuallyState st) (Eventually φ)

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

-- Temporal operators: Eventually
-- Eventually φ means "φ holds at some future point"
--
-- stepEval (Eventually φ) ... (EventuallyState st) prev curr:
--   with stepEval φ ... st prev curr
--   | Satisfied → Satisfied  -- Found it!
--   | Violated _ → Continue (EventuallyState st)  -- Not yet, keep looking
--   | Continue st' → Continue (EventuallyState st')  -- Still checking
--
-- stepL (Eventually φ) prev curr:
--   with stepL φ prev curr
--   | Satisfied → Satisfied  -- Found it!
--   | Violated _ → Continue (Eventually φ)  -- Not yet, keep looking
--   | Continue φ' → Continue (Eventually φ')  -- Still checking

step-bisim (eventually-relate {st} {φ} rel) prev curr
  with stepEval φ evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr

-- Case 1: Inner formula satisfied
-- Both return Satisfied (found!)
... | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim

-- Case 2: Inner formula violated
-- stepEval returns: Continue (EventuallyState st)
-- stepL returns: Continue (Eventually φ)
-- These are related by: eventually-relate rel (original relation preserved!)
... | Violated _ | Violated _ | violated-bisim _
  = continue-bisim (eventually-relate rel)

-- Case 3: Inner formula continues
-- stepEval returns: Continue (EventuallyState st')
-- stepL returns: Continue (Eventually φ')
-- These are related by: eventually-relate rel' (where rel' relates st' and φ')
... | Continue st' | Continue φ' | continue-bisim rel'
  = continue-bisim (eventually-relate rel')

-- Impossible cases
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ | ()
... | Continue _ | Violated _ | ()
... | Continue _ | Satisfied | ()

-- ============================================================================
-- 🎉 SUCCESS! Bisimilarity proven for core LTL operators!
-- ============================================================================

-- What we proved:
-- - Behavioral equivalence between monitor state machine and defunctionalized coalgebra
-- - WITHOUT any postulates for extended lambda equality!
-- - Pure coalgebraic reasoning with behavioral bisimilarity
--
-- Operators proven:
-- ✅ Atomic p - base case (evaluates predicate at current frame)
-- ✅ Not φ - inverts inner result (3 cases)
-- ✅ And φ ψ - both must hold (9 valid combinations)
-- ✅ Or φ ψ - either must hold (9 valid combinations)
-- ✅ Always φ - must hold at all frames (3 cases, preserves φ when satisfied)
-- ✅ Eventually φ - must hold at some frame (3 cases, preserves φ when violated)
--
-- Key insight: The proof is GENERIC over inner formulas!
-- - always-relate and eventually-relate take ANY relation rel : Relate st φ
-- - By structural induction, this covers ALL formulas built from these operators
-- - Example: Always (Not (And (Atomic p) (Atomic q))) proven via composition
--
-- What this means:
-- For any formula φ built from {Atomic, Not, And, Or, Always, Eventually},
-- we can construct a bisimilarity proof by structural recursion on φ.
--
-- Remaining operators (require state extensions):
-- - Next φ: needs "have we skipped?" flag in LTLProc
-- - Until φ ψ: straightforward extension
-- - EventuallyWithin/AlwaysWithin: need startTime tracking in LTLProc

-- ============================================================================
-- VERIFICATION: Complex nested formulas work!
-- ============================================================================

-- Example: Always (Not (Eventually (And (Atomic p) (Atomic q))))
-- This demonstrates that the proof composes for arbitrarily nested formulas.
--
-- Given predicates p and q, we can construct the initial states:
--   monitor state: AlwaysState (NotState (EventuallyState (AndState AtomicState AtomicState)))
--   coalgebra proc: Always (Not (Eventually (And (Atomic p) (Atomic q))))
--
-- And the Relate proof:
--   always-relate (not-relate (eventually-relate (and-relate atomic-relate atomic-relate)))
--
-- This shows that for ANY formula built from {Atomic, Not, And, Or, Always, Eventually},
-- we can mechanically construct both the initial state and the bisimilarity relation!

