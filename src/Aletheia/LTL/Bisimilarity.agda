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
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; EventuallyWithin; AlwaysWithin)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; LTLEvalState; AtomicState; NotState; AndState; OrState; NextState; NextActive; AlwaysState; EventuallyState; UntilState; EventuallyWithinState; AlwaysWithinState; stepEval; initState)
open import Aletheia.LTL.Coalgebra using (LTLProc; stepL; toLTL)
  renaming (Atomic to AtomicProc; Not to NotProc; And to AndProc; Or to OrProc;
            NextWaiting to NextWaitingProc; NextActive to NextActiveProc;
            Always to AlwaysProc; Eventually to EventuallyProc; Until to UntilProc;
            EventuallyWithin to EventuallyWithinProc; AlwaysWithin to AlwaysWithinProc)
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
    → Relate AtomicState (AtomicProc p)

  -- Not states are related if their inner states are related
  not-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (NotState st) (NotProc φ)

  -- And states are related if both inner states are related
  and-relate : ∀ {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (AndState st1 st2) (AndProc φ ψ)

  -- Or states are related if both inner states are related
  or-relate : ∀ {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (OrState st1 st2) (OrProc φ ψ)

  -- Always states are related if their inner states are related
  always-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (AlwaysState st) (AlwaysProc φ)

  -- Eventually states are related if their inner states are related
  eventually-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (EventuallyState st) (EventuallyProc φ)

  -- Until states are related if both inner states are related
  until-relate : ∀ {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (UntilState st1 st2) (UntilProc φ ψ)

  -- Next in waiting mode (before skipping first frame)
  next-waiting-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (NextState st) (NextWaitingProc φ)

  -- Next in active mode (after skipping first frame)
  next-active-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (NextActive st) (NextActiveProc φ)

  -- EventuallyWithin: inner must hold within time window
  -- CRITICAL DESIGN ISSUE: startTime is bookkeeping, NOT semantic!
  --
  -- Current (WRONG): States carry startTime, Relate quantifies over it
  -- This forces structural reasoning about time calculations.
  --
  -- Correct approach: States should carry REMAINING time, not startTime
  -- - Remaining = windowMicros ∸ (currTime ∸ actualStart)
  -- - Computed fresh each step, never stored
  -- - Relate constructor only mentions remaining, not startTime
  --
  -- Required refactoring:
  -- 1. Add `Remaining : ℕ` field to StepResult or state
  -- 2. Compute remaining = windowMicros ∸ elapsed when stepping
  -- 3. Relate based on: Relate st φ → remaining₁ ≡ remaining₂ → ...
  -- 4. Never expose startTime to bisimulation
  --
  -- Current stopgap: Allow ANY startTime₁ startTime₂ (quotient abstraction)
  eventually-within-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
                               {windowMicros : ℕ}
                               {startTime1 startTime2 : ℕ}
    → Relate st φ
    → Relate (EventuallyWithinState startTime1 st)
             (EventuallyWithinProc windowMicros startTime2 φ)

  -- AlwaysWithin: Same remaining-time issue as EventuallyWithin
  always-within-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
                           {windowMicros : ℕ}
                           {startTime1 startTime2 : ℕ}
    → Relate st φ
    → Relate (AlwaysWithinState startTime1 st)
             (AlwaysWithinProc windowMicros startTime2 φ)

-- ============================================================================
-- STEP BISIMILARITY: Related states produce bisimilar observations
-- ============================================================================

-- Helper: Predicate evaluator for the monitor (needed for stepEval)
evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → Bool) → Bool
evalAtomicPred prev curr p = p curr

-- Prove that related states produce bisimilar observations when stepped with the same frame
-- Uses toLTL to convert LTLProc to LTL formula for monitor compatibility
step-bisim : ∀ {st : LTLEvalState} {proc : LTLProc}
  → Relate st proc
  → ∀ (prev : Maybe TimedFrame) (curr : TimedFrame)
  → StepResultBisim Relate
      (stepEval (toLTL proc) evalAtomicPred st prev curr)
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
  with stepEval (toLTL φ) evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr
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
  with stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
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
  with stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
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
  with stepEval (toLTL φ) evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr

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
  with stepEval (toLTL φ) evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr

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

-- Temporal operators: Until
-- Until φ ψ means "φ holds until ψ becomes true"
--
-- stepEval (Until φ ψ) ... (UntilState st1 st2) prev curr:
--   Check ψ first (goal condition):
--   | Satisfied → Satisfied
--   | Continue st2' → check φ (holding condition):
--       | Violated ce → Violated ce
--       | Continue st1' → Continue (UntilState st1' st2')
--       | Satisfied → Continue (UntilState st1 st2')
--   | Violated _ → check φ:
--       | Violated ce → Violated ce
--       | Continue st1' → Continue (UntilState st1' st2)
--       | Satisfied → Continue (UntilState st1 st2)
--
-- stepL (Until φ ψ) prev curr:
--   Check ψ first:
--   | Satisfied → Satisfied
--   | Continue ψ' → check φ:
--       | Violated ce → Violated ce
--       | Continue φ' → Continue (Until φ' ψ')
--       | Satisfied → Continue (Until φ ψ')
--   | Violated _ → check φ:
--       | Violated ce → Violated ce
--       | Continue φ' → Continue (Until φ' ψ)
--       | Satisfied → Continue (Until φ ψ)

-- Temporal operators: Until
-- Until φ ψ means "φ must hold until ψ becomes true"
-- Now uses flat with-pattern (like And/Or) after refactoring the monitor!

step-bisim (until-relate {st1} {st2} {φ} {ψ} rel1 rel2) prev curr
  with stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
     | stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr

-- ψ satisfied → Until satisfied (φ result doesn't matter)
... | Satisfied | Satisfied | satisfied-bisim | _ | _ | _
  = satisfied-bisim

-- ψ continues, φ violated → Until violated
... | Continue _ | Continue _ | continue-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- ψ continues, φ continues → Until continues
... | Continue st2' | Continue ψ' | continue-bisim rel2' | Continue st1' | Continue φ' | continue-bisim rel1'
  = continue-bisim (until-relate rel1' rel2')

-- ψ continues, φ satisfied → Until continues (preserves φ)
... | Continue st2' | Continue ψ' | continue-bisim rel2' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (until-relate rel1 rel2')

-- ψ violated, φ violated → Until violated
... | Violated _ | Violated _ | violated-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- ψ violated, φ continues → Until continues (preserves ψ)
... | Violated _ | Violated _ | violated-bisim _ | Continue st1' | Continue φ' | continue-bisim rel1'
  = continue-bisim (until-relate rel1' rel2)

-- ψ violated, φ satisfied → Until continues (preserves both)
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (until-relate rel1 rel2)

-- Impossible cases (results don't match)
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ | () | _ | _ | _
... | Continue _ | Violated _ | () | _ | _ | _
... | Continue _ | Satisfied | () | _ | _ | _
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ | ()
... | _ | _ | _ | Continue _ | Violated _ | ()
... | _ | _ | _ | Continue _ | Satisfied | ()

-- ============================================================================
-- Next operator (modal states: waiting vs active)
-- ============================================================================

-- Next operator: ◯φ means "φ holds at the next state"
-- The monitor has two modal states:
--   - NextState st: waiting to skip the first frame
--   - NextActive st: actively evaluating inner formula after skip
--
-- The coalgebra mirrors this with:
--   - NextWaitingProc φ: waiting mode
--   - NextActiveProc φ: active mode

-- Case 1: Waiting mode
-- Both skip the current frame and transition to active mode
-- Monitor: NextState st → Continue (NextActive st)
-- Coalgebra: NextWaitingProc φ → Continue (NextActiveProc φ)
step-bisim (next-waiting-relate {st} {φ} rel) prev curr
  = continue-bisim (next-active-relate rel)

-- Case 2: Active mode
-- Both evaluate the inner formula
-- Monitor: NextActive st, evaluates inner φ
-- Coalgebra: NextActiveProc φ, evaluates inner φ
-- Results match because inner states are related
step-bisim (next-active-relate {st} {φ} rel) prev curr
  with stepEval (toLTL φ) evalAtomicPred st prev curr | stepL φ prev curr | step-bisim rel prev curr

-- Inner continues → both continue in NextActive mode
... | Continue st' | Continue φ' | continue-bisim rel'
  = continue-bisim (next-active-relate rel')

-- Inner violated → both violated
... | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- Inner satisfied → both satisfied
... | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim

-- Impossible cases (results don't match)
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ | ()
... | Continue _ | Violated _ | ()
... | Continue _ | Satisfied | ()

-- ============================================================================
-- EVENTUALLY WITHIN: Must hold within time window
-- ============================================================================

-- EventuallyWithin: The key insight is that the time window check is deterministic.
-- Given same curr and startTime, both monitor and coalgebra compute the same
-- actualStart, actualElapsed, and inWindow. They will ALWAYS agree on whether
-- window is valid or expired.
--
-- Strategy: Evaluate FULL EventuallyWithin formula (including time check), then
-- case-split on the outer results. The time window abstraction is maintained by
-- treating the whole formula evaluation as a black box.

step-bisim (eventually-within-relate {st} {φ} {windowMicros} {startTime1} {startTime2} rel) prev curr
  with stepEval (EventuallyWithin windowMicros (toLTL φ)) evalAtomicPred (EventuallyWithinState startTime1 st) prev curr
     | stepL (EventuallyWithinProc windowMicros startTime2 φ) prev curr

-- Both satisfied (inner succeeded within valid window)
... | Satisfied | Satisfied
  = satisfied-bisim

-- Both violated (window expired, regardless of inner)
-- Since both use identical time window logic and identical mkCounterexample call,
-- the counterexamples should be identical, but Agda can't see through the if-then-else.
-- We match on the counterexamples and construct the equivalence.
... | Violated ce1 | Violated ce2
  = violated-bisim (mkCEEquiv {!!} {!!})

-- Both continue (window valid, checking continues)
-- Both implementations use identical handleInWindow logic.
-- If inner formula steps and both wrappers Continue, then inner states
-- remain related. We prove this by invoking step-bisim on inner relation.
... | Continue (EventuallyWithinState _ st') | Continue (EventuallyWithinProc _ _ φ')
  with step-bisim rel prev curr
-- If inner step results are bisimilar and both outer Continue,
-- then by handleInWindow semantics, inner states remain related
... | continue-bisim rel' = continue-bisim (eventually-within-relate rel')
... | violated-bisim _ = continue-bisim (eventually-within-relate rel)  -- handleInWindow preserves on violated
... | satisfied-bisim = {!!}  -- handleInWindow returns Satisfied, contradicts Continue

-- Impossible cases (outer results don't match)
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ | ()
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ | ()
... | Continue _ | Satisfied | ()
... | Continue _ | Violated _ | ()

-- ============================================================================
-- ALWAYS WITHIN: Must hold throughout time window
-- ============================================================================

-- AlwaysWithin: Same strategy as EventuallyWithin
-- Time window check is deterministic, so both implementations agree on window validity

step-bisim (always-within-relate {st} {φ} {windowMicros} {startTime1} {startTime2} rel) prev curr
  with stepEval (AlwaysWithin windowMicros (toLTL φ)) evalAtomicPred (AlwaysWithinState startTime1 st) prev curr
     | stepL (AlwaysWithinProc windowMicros startTime2 φ) prev curr

-- Both satisfied (window completed without violations)
... | Satisfied | Satisfied
  = satisfied-bisim

-- Both violated (inner violated within window)
... | Violated ce1 | Violated ce2
  = violated-bisim (mkCEEquiv {!!} {!!})

-- Both continue (window valid, checking continues)
-- Same pattern as EventuallyWithin but with AlwaysWithin semantics
... | Continue (AlwaysWithinState _ st') | Continue (AlwaysWithinProc _ _ φ')
  with step-bisim rel prev curr
-- Inner continues → both wrapped, inner states related
... | continue-bisim rel' = continue-bisim (always-within-relate rel')
-- Inner satisfied → handleInWindow preserves, keep original relation
... | satisfied-bisim = continue-bisim (always-within-relate rel)
-- Inner violated → handleInWindow returns Violated, contradicts Continue
... | violated-bisim _ = {!!}

-- Impossible cases (outer results don't match)
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ | ()
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ | ()
... | Continue _ | Satisfied | ()
... | Continue _ | Violated _ | ()

-- ============================================================================
-- 🎉 PROGRESS! Bisimilarity: 8 operators fully proven, 2 nearly complete
-- ============================================================================

-- What we proved:
-- - Behavioral equivalence between monitor state machine and defunctionalized coalgebra
-- - WITHOUT postulates for extended lambda equality!
-- - Pure coalgebraic reasoning with behavioral bisimilarity
--
-- Operators FULLY proven (8/10):
-- ✅ Atomic p - base case (evaluates predicate at current frame)
-- ✅ Not φ - inverts inner result (3 cases)
-- ✅ And φ ψ - both must hold (9 valid combinations)
-- ✅ Or φ ψ - either must hold (9 valid combinations)
-- ✅ Always φ - must hold at all frames (3 cases, preserves φ when satisfied)
-- ✅ Eventually φ - must hold at some frame (3 cases, preserves φ when violated)
-- ✅ Until φ ψ - φ must hold until ψ (refactored to flat with-patterns, 7 valid combinations)
-- ✅ Next φ - φ holds at next state (modal states: waiting 1 case, active 3 cases)
--
-- Infrastructure complete, proofs deferred (2/10):
-- ⏳ EventuallyWithin - Relate constructor added, stepL implemented, proof deferred
-- ⏳ AlwaysWithin - Relate constructor added, stepL implemented, proof deferred
--
-- Why bounded operators are harder:
-- - Time window logic (actualStart, actualElapsed, inWindow) is interleaved with
--   formula evaluation in both monitor and coalgebra implementations
-- - Proving bisimilarity requires reasoning about if-then-else branches at value level
-- - Need to show that inner bisimilarity is preserved through handleInWindow transformations
-- - The implementations ARE identical by inspection, but formal proof is complex
--
-- Next steps for EventuallyWithin/AlwaysWithin:
-- 1. Factor out time window logic into separate lemmas
-- 2. Prove time window calculations produce identical results given same inputs
-- 3. Prove handleInWindow preserves bisimilarity
-- 4. Compose these lemmas to prove full bisimilarity
-- OR: Refactor implementations to make proof easier (e.g., separate time checking from formula evaluation)
--
-- Key insight: The proof is GENERIC over inner formulas!
-- - All relate constructors take ANY relation rel : Relate st φ
-- - By structural induction, this covers ALL formulas built from proven operators
-- - Example: Always (Not (Next (And (Atomic p) (Atomic q)))) proven via composition
--
-- What this means:
-- For any formula φ built from the 8 proven operators, we can construct a bisimilarity
-- proof by structural recursion on φ. The proof scales to arbitrarily complex
-- real-world LTL properties!
--
-- For formulas using EventuallyWithin/AlwaysWithin: Infrastructure is in place (LTLProc
-- constructors, toLTL conversion, stepL implementation, Relate constructors). Only the
-- bisimilarity proofs themselves are missing.

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

