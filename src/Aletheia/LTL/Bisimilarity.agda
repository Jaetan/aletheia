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
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Inconclusive; Counterexample; LTLEvalState; AtomicState; NotState; AndState; OrState; NextState; NextActive; AlwaysState; EventuallyState; UntilState; ReleaseState; MetricEventuallyState; MetricAlwaysState; MetricUntilState; MetricReleaseState; stepEval; initState; FinalVerdict; Holds; Fails; finalizeEval)
open import Aletheia.LTL.Coalgebra using (LTLProc; stepL; toLTL; finalizeL; initProc; MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc)
  renaming (Atomic to AtomicProc; Not to NotProc; And to AndProc; Or to OrProc;
            NextWaiting to NextWaitingProc; NextActive to NextActiveProc;
            Always to AlwaysProc; Eventually to EventuallyProc; Until to UntilProc;
            Release to ReleaseProc)
open import Aletheia.LTL.StepResultBisim using (StepResultBisim; violated-bisim; satisfied-bisim; continue-bisim; inconclusive-bisim; CounterexampleEquiv; mkCEEquiv)
open import Aletheia.LTL.SignalPredicate using (SignalVal; True; False; Unknown; Pending)
open import Aletheia.LTL.CoalgebraBisim using (CoalgebraBisim)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_∸_; _≤ᵇ_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
  atomic-relate : ∀ {p : TimedFrame → SignalVal}
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
  -- Both sides carry the same resolved flag
  always-relate : ∀ {resolved : Bool} {st : LTLEvalState} {φ : LTLProc}
    → Relate st φ
    → Relate (AlwaysState resolved st) (AlwaysProc resolved φ)

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
  -- Observable requirement: Both sides must have SAME startTime
  -- This ensures they compute identical remaining time (observable equivalence)
  --
  -- Key insight: startTime is bookkeeping that determines observable remaining time
  -- By requiring startTime₁ = startTime₂, we guarantee:
  --   - Same actualStart on first frame
  --   - Same elapsed time on every frame
  --   - Same remaining time (the only observable quantity)
  metric-eventually-relate : ∀ {st : LTLEvalState} {φ : LTLProc}
                               {windowMicros startTime : ℕ}
    → Relate st φ
    → Relate (MetricEventuallyState startTime st)
             (MetricEventuallyProc windowMicros startTime φ)

  -- MetricAlways: Same observable requirement as MetricEventually
  -- Both sides must have SAME startTime and resolved flag
  metric-always-relate : ∀ {resolved : Bool} {st : LTLEvalState} {φ : LTLProc}
                           {windowMicros startTime : ℕ}
    → Relate st φ
    → Relate (MetricAlwaysState resolved startTime st)
             (MetricAlwaysProc resolved windowMicros startTime φ)

  -- Release states are related if both inner states are related
  -- Both sides carry the same resolved flag
  release-relate : ∀ {resolved : Bool} {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (ReleaseState resolved st1 st2) (ReleaseProc resolved φ ψ)

  -- MetricUntil: Bounded Until with observable time tracking
  -- Same observable requirement as other bounded operators
  metric-until-relate : ∀ {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
                          {windowMicros startTime : ℕ}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (MetricUntilState startTime st1 st2)
             (MetricUntilProc windowMicros startTime φ ψ)

  -- MetricRelease: Bounded Release with observable time tracking
  -- Both sides must have SAME resolved flag and startTime
  metric-release-relate : ∀ {resolved : Bool} {st1 st2 : LTLEvalState} {φ ψ : LTLProc}
                            {windowMicros startTime : ℕ}
    → Relate st1 φ
    → Relate st2 ψ
    → Relate (MetricReleaseState resolved startTime st1 st2)
             (MetricReleaseProc resolved windowMicros startTime φ ψ)

-- ============================================================================
-- STEP BISIMILARITY: Related states produce bisimilar observations
-- ============================================================================

-- Helper: Predicate evaluator for the monitor (needed for stepEval)
evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → SignalVal) → SignalVal
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
-- Both evaluate p at current frame, return Satisfied, Violated, or Inconclusive
step-bisim (atomic-relate {p}) prev curr
  with p curr
... | True    = satisfied-bisim
... | False   = violated-bisim (mkCEEquiv refl refl)
... | Unknown = inconclusive-bisim atomic-relate  -- Signal not yet observed
... | Pending = continue-bisim atomic-relate       -- Not enough data yet

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
-- Inner continues → Not continues with negated inner (both return 0, unbounded)
... | Continue _ st' | Continue _ φ' | continue-bisim rel'
  = continue-bisim (not-relate rel')
-- Inner inconclusive → Not is inconclusive (unknown negated is still unknown)
... | Inconclusive st' | Inconclusive φ' | inconclusive-bisim rel'
  = inconclusive-bisim (not-relate rel')
-- Impossible cases
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Continue _ _ | ()

-- Propositional operators: And (Kleene logic)
-- This is more complex - need to handle all combinations including Inconclusive
step-bisim (and-relate {st1} {st2} {φ} {ψ} rel1 rel2) prev curr
  with stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
-- Violated cases (short-circuit: False ∧ _ = False)
... | Violated ce1 | Violated ce2 | violated-bisim ceq | _ | _ | _
  = violated-bisim ceq
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Violated ce1 | Violated ce2 | violated-bisim ceq
  = violated-bisim ceq
... | Satisfied | Satisfied | satisfied-bisim | Violated ce1 | Violated ce2 | violated-bisim ceq
  = violated-bisim ceq
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Violated ce1 | Violated ce2 | violated-bisim ceq
  = violated-bisim ceq
-- Inconclusive cases (neither violated, Unknown ∧ _ = Unknown when not False)
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2'
  = inconclusive-bisim (and-relate rel1' rel2')
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = inconclusive-bisim (and-relate rel1' rel2')
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = inconclusive-bisim (and-relate rel1' rel2)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2'
  = inconclusive-bisim (and-relate rel1' rel2')
... | Satisfied | Satisfied | satisfied-bisim | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2'
  = inconclusive-bisim (and-relate rel1 rel2')
-- Normal cases (neither violated, neither inconclusive)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (and-relate rel1' rel2')
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (and-relate rel1' rel2)
... | Satisfied | Satisfied | satisfied-bisim | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (and-relate rel1 rel2')
... | Satisfied | Satisfied | satisfied-bisim | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
-- Impossible cases: left results don't match
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ _ | () | _ | _ | _
... | Violated _ | Inconclusive _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ _ | () | _ | _ | _
... | Satisfied | Inconclusive _ | () | _ | _ | _
... | Continue _ _ | Violated _ | () | _ | _ | _
... | Continue _ _ | Satisfied | () | _ | _ | _
... | Continue _ _ | Inconclusive _ | () | _ | _ | _
... | Inconclusive _ | Violated _ | () | _ | _ | _
... | Inconclusive _ | Satisfied | () | _ | _ | _
... | Inconclusive _ | Continue _ _ | () | _ | _ | _
-- Impossible cases: right results don't match
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ _ | ()
... | _ | _ | _ | Violated _ | Inconclusive _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ _ | ()
... | _ | _ | _ | Satisfied | Inconclusive _ | ()
... | _ | _ | _ | Continue _ _ | Violated _ | ()
... | _ | _ | _ | Continue _ _ | Satisfied | ()
... | _ | _ | _ | Continue _ _ | Inconclusive _ | ()
... | _ | _ | _ | Inconclusive _ | Violated _ | ()
... | _ | _ | _ | Inconclusive _ | Satisfied | ()
... | _ | _ | _ | Inconclusive _ | Continue _ _ | ()

-- Propositional operators: Or (Kleene logic)
-- Similar structure to And, but dual: True ∨ _ = True
step-bisim (or-relate {st1} {st2} {φ} {ψ} rel1 rel2) prev curr
  with stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
-- Satisfied cases (short-circuit: True ∨ _ = True)
... | Satisfied | Satisfied | satisfied-bisim | _ | _ | _
  = satisfied-bisim
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
-- Inconclusive cases (neither satisfied, neither both violated)
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2'
  = inconclusive-bisim (or-relate rel1' rel2')
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = inconclusive-bisim (or-relate rel1' rel2')
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Violated _ | Violated _ | violated-bisim _
  = inconclusive-bisim (or-relate rel1' rel2)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2'
  = inconclusive-bisim (or-relate rel1' rel2')
... | Violated _ | Violated _ | violated-bisim _ | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2'
  = inconclusive-bisim (or-relate rel1 rel2')
-- Normal cases (neither satisfied, neither inconclusive)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (or-relate rel1' rel2')
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Violated _ | Violated _ | violated-bisim _
  = continue-bisim (or-relate rel1' rel2)
... | Violated _ | Violated _ | violated-bisim _ | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (or-relate rel1 rel2')
... | Violated _ | Violated _ | violated-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq
-- Impossible cases: left results don't match
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ _ | () | _ | _ | _
... | Violated _ | Inconclusive _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ _ | () | _ | _ | _
... | Satisfied | Inconclusive _ | () | _ | _ | _
... | Continue _ _ | Violated _ | () | _ | _ | _
... | Continue _ _ | Satisfied | () | _ | _ | _
... | Continue _ _ | Inconclusive _ | () | _ | _ | _
... | Inconclusive _ | Violated _ | () | _ | _ | _
... | Inconclusive _ | Satisfied | () | _ | _ | _
... | Inconclusive _ | Continue _ _ | () | _ | _ | _
-- Impossible cases: right results don't match
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ _ | ()
... | _ | _ | _ | Violated _ | Inconclusive _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ _ | ()
... | _ | _ | _ | Satisfied | Inconclusive _ | ()
... | _ | _ | _ | Continue _ _ | Violated _ | ()
... | _ | _ | _ | Continue _ _ | Satisfied | ()
... | _ | _ | _ | Continue _ _ | Inconclusive _ | ()
... | _ | _ | _ | Inconclusive _ | Violated _ | ()
... | _ | _ | _ | Inconclusive _ | Satisfied | ()
... | _ | _ | _ | Inconclusive _ | Continue _ _ | ()

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

step-bisim (always-relate {_} {st} {φ} rel) prev curr
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
-- stepEval returns: Continue 0 (AlwaysState st') (unbounded)
-- stepL returns: Continue 0 (Always φ') (unbounded)
-- These are related by: always-relate rel' (where rel' relates st' and φ')
... | Continue _ st' | Continue _ φ' | continue-bisim rel'
  = continue-bisim (always-relate rel')

-- Case 4: Inner formula inconclusive (SAFETY: Unknown → Violated)
-- Both return Violated (can't confirm safety holds)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)

-- Impossible cases (where observations don't match)
-- Agda can prove these are impossible via unification!
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Continue _ _ | ()

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
-- stepEval returns: Continue 0 (EventuallyState st') (unbounded)
-- stepL returns: Continue 0 (Eventually φ') (unbounded)
-- These are related by: eventually-relate rel' (where rel' relates st' and φ')
... | Continue _ st' | Continue _ φ' | continue-bisim rel'
  = continue-bisim (eventually-relate rel')

-- Case 4: Inner formula inconclusive (LIVENESS: propagate, will fail at end-of-stream)
-- Both return Inconclusive (still waiting for satisfaction)
... | Inconclusive st' | Inconclusive φ' | inconclusive-bisim rel'
  = inconclusive-bisim (eventually-relate rel')

-- Impossible cases
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Continue _ _ | ()

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

-- φ inconclusive → Violated (SAFETY: φ must hold, regardless of ψ)
-- Need to enumerate ψ cases explicitly (ψ=Satisfied already handled above)
... | Violated _ | Violated _ | violated-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Continue _ _ | Continue _ _ | continue-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)

-- ψ continues, φ violated → Until violated
... | Continue _ _ | Continue _ _ | continue-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- ψ continues, φ continues → Until continues (both return 0, unbounded)
... | Continue _ st2' | Continue _ ψ' | continue-bisim rel2' | Continue _ st1' | Continue _ φ' | continue-bisim rel1'
  = continue-bisim (until-relate rel1' rel2')

-- ψ continues, φ satisfied → Until continues (preserves φ)
... | Continue _ st2' | Continue _ ψ' | continue-bisim rel2' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (until-relate rel1 rel2')

-- ψ violated, φ violated → Until violated
... | Violated _ | Violated _ | violated-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- ψ violated, φ continues → Until continues (preserves ψ)
... | Violated _ | Violated _ | violated-bisim _ | Continue _ st1' | Continue _ φ' | continue-bisim rel1'
  = continue-bisim (until-relate rel1' rel2)

-- ψ violated, φ satisfied → Until continues (preserves both)
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (until-relate rel1 rel2)

-- ψ inconclusive, φ ok → propagate (LIVENESS: ψ must eventually, keep waiting)
... | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2' | Continue _ st1' | Continue _ φ' | continue-bisim rel1'
  = inconclusive-bisim (until-relate rel1' rel2')
... | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2' | Satisfied | Satisfied | satisfied-bisim
  = inconclusive-bisim (until-relate rel1 rel2')
... | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2' | Violated _ | Violated _ | violated-bisim _
  = inconclusive-bisim (until-relate rel1 rel2')  -- φ failed but ψ unknown, propagate

-- Impossible cases (results don't match)
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ _ | () | _ | _ | _
... | Violated _ | Inconclusive _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ _ | () | _ | _ | _
... | Satisfied | Inconclusive _ | () | _ | _ | _
... | Continue _ _ | Violated _ | () | _ | _ | _
... | Continue _ _ | Satisfied | () | _ | _ | _
... | Continue _ _ | Inconclusive _ | () | _ | _ | _
... | Inconclusive _ | Violated _ | () | _ | _ | _
... | Inconclusive _ | Satisfied | () | _ | _ | _
... | Inconclusive _ | Continue _ _ | () | _ | _ | _
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ _ | ()
... | _ | _ | _ | Violated _ | Inconclusive _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ _ | ()
... | _ | _ | _ | Satisfied | Inconclusive _ | ()
... | _ | _ | _ | Continue _ _ | Violated _ | ()
... | _ | _ | _ | Continue _ _ | Satisfied | ()
... | _ | _ | _ | Continue _ _ | Inconclusive _ | ()
... | _ | _ | _ | Inconclusive _ | Violated _ | ()
... | _ | _ | _ | Inconclusive _ | Satisfied | ()
... | _ | _ | _ | Inconclusive _ | Continue _ _ | ()

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

-- Inner continues → both continue in NextActive mode (both return 0, unbounded)
... | Continue _ st' | Continue _ φ' | continue-bisim rel'
  = continue-bisim (next-active-relate rel')

-- Inner violated → both violated
... | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- Inner satisfied → both satisfied
... | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim

-- Inner inconclusive → both inconclusive (propagate)
... | Inconclusive st' | Inconclusive φ' | inconclusive-bisim rel'
  = inconclusive-bisim (next-active-relate rel')

-- Impossible cases (results don't match)
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Continue _ _ | ()

-- ============================================================================
-- EVENTUALLY WITHIN: Must hold within time window
-- ============================================================================

-- EventuallyWithin: Must hold within time window
-- Observable invariant: Both sides have SAME startTime, therefore compute SAME remaining time
--
-- Proof strategy:
-- 1. Both compute: actualStart = if startTime ≡ᵇ 0 then timestamp curr else startTime
-- 2. Both compute: remaining = windowMicros ∸ (timestamp curr ∸ actualStart)
-- 3. Both compute: inWindow = (timestamp curr ∸ actualStart) ≤ᵇ windowMicros
-- 4. Since inputs identical → outputs identical (deterministic computation)

step-bisim (metric-eventually-relate {st} {φ} {windowMicros} {startTime} rel) prev curr
  -- Compute observable: window validity (both sides compute identically)
  with (timestamp curr ∸ (if startTime ≡ᵇ 0 then timestamp curr else startTime)) ≤ᵇ windowMicros
... | false  -- Window expired on both sides: handleDeadline
  with stepEval (toLTL φ) evalAtomicPred st prev curr
     | stepL φ prev curr
     | step-bisim rel prev curr
... | Satisfied | Satisfied | satisfied-bisim = satisfied-bisim  -- Made it just in time
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ = violated-bisim (mkCEEquiv refl refl)  -- Signal unknown at deadline
... | Violated _ | Violated _ | violated-bisim _ = violated-bisim (mkCEEquiv refl refl)  -- Window expired
... | Continue _ _ | Continue _ _ | continue-bisim _ = violated-bisim (mkCEEquiv refl refl)  -- Window expired
-- Impossible: inner results don't match
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Continue _ _ | ()
step-bisim (metric-eventually-relate {st} {φ} {windowMicros} {startTime} rel) prev curr
  | true  -- Window valid on both sides
  with stepEval (toLTL φ) evalAtomicPred st prev curr
     | stepL φ prev curr
     | step-bisim rel prev curr
... | Satisfied | Satisfied | satisfied-bisim
  = satisfied-bisim
... | Violated _ | Violated _ | violated-bisim _
  = continue-bisim (metric-eventually-relate rel)  -- Both preserve original state
... | Continue _ st' | Continue _ φ' | continue-bisim rel'
  = continue-bisim (metric-eventually-relate rel')  -- Both step inner state
... | Inconclusive st' | Inconclusive φ' | inconclusive-bisim rel'
  = inconclusive-bisim (metric-eventually-relate rel')  -- LIVENESS: propagate
-- Impossible: inner results don't match
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Continue _ _ | ()

-- ============================================================================
-- ALWAYS WITHIN: Must hold throughout time window
-- ============================================================================

-- AlwaysWithin: Must hold throughout time window
-- Observable invariant: Both sides have SAME startTime, therefore compute SAME remaining time

step-bisim (metric-always-relate {_} {st} {φ} {windowMicros} {startTime} rel) prev curr
  -- Compute observable: window validity (both sides compute identically)
  with (timestamp curr ∸ (if startTime ≡ᵇ 0 then timestamp curr else startTime)) ≤ᵇ windowMicros
... | false  -- Window complete on both sides
  = satisfied-bisim  -- Both succeed when window completes
... | true  -- Window valid on both sides
  with stepEval (toLTL φ) evalAtomicPred st prev curr
     | stepL φ prev curr
     | step-bisim rel prev curr
... | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq  -- Both propagate same inner violation
... | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (metric-always-relate rel)  -- Both preserve original state
... | Continue _ st' | Continue _ φ' | continue-bisim rel'
  = continue-bisim (metric-always-relate rel')  -- Both step inner state
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)  -- SAFETY: Inconclusive → Violated
-- Impossible: inner results don't match
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Continue _ _ | ()

-- ============================================================================
-- Release operator (dual of Until)
-- ============================================================================

-- Release: φ Release ψ means ψ holds until φ releases it (or forever)
-- Semantics: Either φ holds (release condition), or ψ holds AND the rest is Release
-- ψ has SAFETY role (must hold) → Inconclusive = Violated
-- φ has LIVENESS role (release) → Inconclusive = propagate
step-bisim (release-relate {_} {st1} {st2} {φ} {ψ} rel1 rel2) prev curr
  with stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr

-- φ satisfied → Release satisfied (release condition met, ψ result doesn't matter)
... | Satisfied | Satisfied | satisfied-bisim | _ | _ | _
  = satisfied-bisim

-- ψ inconclusive → Violated (SAFETY: ψ must hold, regardless of φ)
-- Need to enumerate φ cases explicitly (φ=Satisfied already handled above)
... | Violated _ | Violated _ | violated-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Continue _ _ | Continue _ _ | continue-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)

-- φ continues, ψ violated → Release violated (ψ must hold until release)
... | Continue _ _ | Continue _ _ | continue-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- φ continues, ψ continues → Release continues (both return 0, unbounded)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (release-relate rel1' rel2')

-- φ continues, ψ satisfied → Release continues (preserves ψ)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (release-relate rel1' rel2)

-- φ violated, ψ violated → Release violated
-- Both return ψ's counterexample (second argument in with-clause)
... | Violated ceφ1 | Violated ceφ2 | violated-bisim ceqφ | Violated ceψ1 | Violated ceψ2 | violated-bisim ceqψ
  = violated-bisim ceqψ  -- Observable handler returns ψ's ce

-- φ violated, ψ continues → Release continues (preserves φ)
... | Violated _ | Violated _ | violated-bisim _ | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (release-relate rel1 rel2')

-- φ violated, ψ satisfied → Release continues (preserves both)
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (release-relate rel1 rel2)

-- φ inconclusive, ψ ok → propagate (LIVENESS: φ releases eventually)
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = inconclusive-bisim (release-relate rel1' rel2')
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = inconclusive-bisim (release-relate rel1' rel2)
-- φ inconclusive, ψ violated → Violated (ψ is safety, must hold)
-- Both implementations create identical new counterexamples, so use refl
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Violated _ | Violated _ | violated-bisim _
  = violated-bisim (mkCEEquiv refl refl)

-- Impossible cases (results don't match)
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ _ | () | _ | _ | _
... | Violated _ | Inconclusive _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ _ | () | _ | _ | _
... | Satisfied | Inconclusive _ | () | _ | _ | _
... | Continue _ _ | Violated _ | () | _ | _ | _
... | Continue _ _ | Satisfied | () | _ | _ | _
... | Continue _ _ | Inconclusive _ | () | _ | _ | _
... | Inconclusive _ | Violated _ | () | _ | _ | _
... | Inconclusive _ | Satisfied | () | _ | _ | _
... | Inconclusive _ | Continue _ _ | () | _ | _ | _
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ _ | ()
... | _ | _ | _ | Violated _ | Inconclusive _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ _ | ()
... | _ | _ | _ | Satisfied | Inconclusive _ | ()
... | _ | _ | _ | Continue _ _ | Violated _ | ()
... | _ | _ | _ | Continue _ _ | Satisfied | ()
... | _ | _ | _ | Continue _ _ | Inconclusive _ | ()
... | _ | _ | _ | Inconclusive _ | Violated _ | ()
... | _ | _ | _ | Inconclusive _ | Satisfied | ()
... | _ | _ | _ | Inconclusive _ | Continue _ _ | ()

-- ============================================================================
-- UntilWithin operator (bounded Until)
-- ============================================================================

-- UntilWithin: φ Until ψ within time window
-- Same as Until but with time bound, uses observable remaining time
-- φ has SAFETY role (must hold): Inconclusive → Violated
-- ψ has LIVENESS role (must eventually): Inconclusive → propagate
step-bisim (metric-until-relate {st1} {st2} {φ} {ψ} {windowMicros} {startTime} rel1 rel2) prev curr
  -- Compute observable: window validity (both sides compute identically)
  with (timestamp curr ∸ (if startTime ≡ᵇ 0 then timestamp curr else startTime)) ≤ᵇ windowMicros
... | false  -- Window expired on both sides: handleDeadline on ψResult
  with stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
... | Satisfied | Satisfied | satisfied-bisim = satisfied-bisim  -- ψ satisfied just in time
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ = violated-bisim (mkCEEquiv refl refl)  -- ψ signal unknown at deadline
... | Violated _ | Violated _ | violated-bisim _ = violated-bisim (mkCEEquiv refl refl)  -- Window expired
... | Continue _ _ | Continue _ _ | continue-bisim _ = violated-bisim (mkCEEquiv refl refl)  -- Window expired
-- Impossible: ψ results don't match
... | Satisfied | Violated _ | ()
... | Satisfied | Continue _ _ | ()
... | Satisfied | Inconclusive _ | ()
... | Violated _ | Satisfied | ()
... | Violated _ | Continue _ _ | ()
... | Violated _ | Inconclusive _ | ()
... | Continue _ _ | Satisfied | ()
... | Continue _ _ | Violated _ | ()
... | Continue _ _ | Inconclusive _ | ()
... | Inconclusive _ | Satisfied | ()
... | Inconclusive _ | Violated _ | ()
... | Inconclusive _ | Continue _ _ | ()
step-bisim (metric-until-relate {st1} {st2} {φ} {ψ} {windowMicros} {startTime} rel1 rel2) prev curr
  | true  -- Window valid on both sides
  with stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr
     | stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr

-- ψ satisfied → UntilWithin satisfied
... | Satisfied | Satisfied | satisfied-bisim | _ | _ | _
  = satisfied-bisim

-- φ inconclusive → Violated (SAFETY: φ must hold, regardless of ψ)
-- Need to enumerate ψ cases explicitly (ψ=Satisfied already handled above)
... | Violated _ | Violated _ | violated-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Continue _ _ | Continue _ _ | continue-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)

-- ψ continues, φ violated → UntilWithin violated
... | Continue _ _ | Continue _ _ | continue-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- ψ continues, φ continues → UntilWithin continues
... | Continue _ st2' | Continue _ ψ' | continue-bisim rel2' | Continue _ st1' | Continue _ φ' | continue-bisim rel1'
  = continue-bisim (metric-until-relate rel1' rel2')

-- ψ continues, φ satisfied → UntilWithin continues (preserves φ)
... | Continue _ st2' | Continue _ ψ' | continue-bisim rel2' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (metric-until-relate rel1 rel2')

-- ψ violated, φ violated → UntilWithin violated
-- Observable handlers return φ's counterexample (second StepResult argument)
... | Violated ceψ1 | Violated ceψ2 | violated-bisim ceqψ | Violated ceφ1 | Violated ceφ2 | violated-bisim ceqφ
  = violated-bisim ceqφ  -- Top-level handler makes this reducible

-- ψ violated, φ continues → UntilWithin continues (preserves ψ)
... | Violated _ | Violated _ | violated-bisim _ | Continue _ st1' | Continue _ φ' | continue-bisim rel1'
  = continue-bisim (metric-until-relate rel1' rel2)

-- ψ violated, φ satisfied → UntilWithin continues (preserves both)
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (metric-until-relate rel1 rel2)

-- ψ inconclusive, φ ok (not violated) → propagate (LIVENESS: ψ must eventually)
... | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2' | Continue _ st1' | Continue _ φ' | continue-bisim rel1'
  = inconclusive-bisim (metric-until-relate rel1' rel2')
... | Inconclusive st2' | Inconclusive ψ' | inconclusive-bisim rel2' | Satisfied | Satisfied | satisfied-bisim
  = inconclusive-bisim (metric-until-relate rel1 rel2')
-- ψ inconclusive, φ violated → Violated (safety violation takes precedence)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- Impossible cases
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ _ | () | _ | _ | _
... | Violated _ | Inconclusive _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ _ | () | _ | _ | _
... | Satisfied | Inconclusive _ | () | _ | _ | _
... | Continue _ _ | Violated _ | () | _ | _ | _
... | Continue _ _ | Satisfied | () | _ | _ | _
... | Continue _ _ | Inconclusive _ | () | _ | _ | _
... | Inconclusive _ | Violated _ | () | _ | _ | _
... | Inconclusive _ | Satisfied | () | _ | _ | _
... | Inconclusive _ | Continue _ _ | () | _ | _ | _
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ _ | ()
... | _ | _ | _ | Violated _ | Inconclusive _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ _ | ()
... | _ | _ | _ | Satisfied | Inconclusive _ | ()
... | _ | _ | _ | Continue _ _ | Violated _ | ()
... | _ | _ | _ | Continue _ _ | Satisfied | ()
... | _ | _ | _ | Continue _ _ | Inconclusive _ | ()
... | _ | _ | _ | Inconclusive _ | Violated _ | ()
... | _ | _ | _ | Inconclusive _ | Satisfied | ()
... | _ | _ | _ | Inconclusive _ | Continue _ _ | ()

-- ============================================================================
-- ReleaseWithin operator (bounded Release)
-- ============================================================================

-- ReleaseWithin: φ Release ψ within time window
-- Same as Release but with time bound, uses observable remaining time
-- ψ has SAFETY role (must hold): Inconclusive → Violated
-- φ has LIVENESS role (release): Inconclusive → propagate
step-bisim (metric-release-relate {_} {st1} {st2} {φ} {ψ} {windowMicros} {startTime} rel1 rel2) prev curr
  -- Compute observable: window validity (both sides compute identically)
  with (timestamp curr ∸ (if startTime ≡ᵇ 0 then timestamp curr else startTime)) ≤ᵇ windowMicros
... | false  -- Window complete on both sides
  = satisfied-bisim  -- Both succeed when window completes (ψ held throughout)
... | true  -- Window valid on both sides
  with stepEval (toLTL φ) evalAtomicPred st1 prev curr | stepL φ prev curr | step-bisim rel1 prev curr
     | stepEval (toLTL ψ) evalAtomicPred st2 prev curr | stepL ψ prev curr | step-bisim rel2 prev curr

-- φ satisfied → ReleaseWithin satisfied (release condition met)
... | Satisfied | Satisfied | satisfied-bisim | _ | _ | _
  = satisfied-bisim

-- ψ inconclusive → Violated (SAFETY: ψ must hold, regardless of φ)
-- Need to enumerate φ cases explicitly (φ=Satisfied already handled above)
... | Violated _ | Violated _ | violated-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Continue _ _ | Continue _ _ | continue-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Inconclusive _ | Inconclusive _ | inconclusive-bisim _
  = violated-bisim (mkCEEquiv refl refl)

-- φ continues, ψ violated → ReleaseWithin violated (ψ must hold until release)
... | Continue _ _ | Continue _ _ | continue-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- φ continues, ψ continues → ReleaseWithin continues
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (metric-release-relate rel1' rel2')

-- φ continues, ψ satisfied → ReleaseWithin continues (preserves ψ)
... | Continue _ st1' | Continue _ φ' | continue-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (metric-release-relate rel1' rel2)

-- φ violated, ψ violated → ReleaseWithin violated
-- Observable handlers return ψ's counterexample (second StepResult argument)
... | Violated ceφ1 | Violated ceφ2 | violated-bisim ceqφ | Violated ceψ1 | Violated ceψ2 | violated-bisim ceqψ
  = violated-bisim ceqψ  -- Top-level handler makes this reducible

-- φ violated, ψ continues → ReleaseWithin continues (preserves φ)
... | Violated _ | Violated _ | violated-bisim _ | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = continue-bisim (metric-release-relate rel1 rel2')

-- φ violated, ψ satisfied → ReleaseWithin continues (preserves both)
... | Violated _ | Violated _ | violated-bisim _ | Satisfied | Satisfied | satisfied-bisim
  = continue-bisim (metric-release-relate rel1 rel2)

-- φ inconclusive, ψ ok → propagate (LIVENESS: φ releases eventually)
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Continue _ st2' | Continue _ ψ' | continue-bisim rel2'
  = inconclusive-bisim (metric-release-relate rel1' rel2')
... | Inconclusive st1' | Inconclusive φ' | inconclusive-bisim rel1' | Satisfied | Satisfied | satisfied-bisim
  = inconclusive-bisim (metric-release-relate rel1' rel2)
-- φ inconclusive, ψ violated → Violated (ψ is safety, must hold)
... | Inconclusive _ | Inconclusive _ | inconclusive-bisim _ | Violated _ | Violated _ | violated-bisim ceq
  = violated-bisim ceq

-- Impossible cases
... | Violated _ | Satisfied | () | _ | _ | _
... | Violated _ | Continue _ _ | () | _ | _ | _
... | Violated _ | Inconclusive _ | () | _ | _ | _
... | Satisfied | Violated _ | () | _ | _ | _
... | Satisfied | Continue _ _ | () | _ | _ | _
... | Satisfied | Inconclusive _ | () | _ | _ | _
... | Continue _ _ | Violated _ | () | _ | _ | _
... | Continue _ _ | Satisfied | () | _ | _ | _
... | Continue _ _ | Inconclusive _ | () | _ | _ | _
... | Inconclusive _ | Violated _ | () | _ | _ | _
... | Inconclusive _ | Satisfied | () | _ | _ | _
... | Inconclusive _ | Continue _ _ | () | _ | _ | _
... | _ | _ | _ | Violated _ | Satisfied | ()
... | _ | _ | _ | Violated _ | Continue _ _ | ()
... | _ | _ | _ | Violated _ | Inconclusive _ | ()
... | _ | _ | _ | Satisfied | Violated _ | ()
... | _ | _ | _ | Satisfied | Continue _ _ | ()
... | _ | _ | _ | Satisfied | Inconclusive _ | ()
... | _ | _ | _ | Continue _ _ | Violated _ | ()
... | _ | _ | _ | Continue _ _ | Satisfied | ()
... | _ | _ | _ | Continue _ _ | Inconclusive _ | ()
... | _ | _ | _ | Inconclusive _ | Violated _ | ()
... | _ | _ | _ | Inconclusive _ | Satisfied | ()
... | _ | _ | _ | Inconclusive _ | Continue _ _ | ()

-- ============================================================================
-- Bisimilarity: ALL 14 operators fully proven!
-- ============================================================================

-- What we proved:
-- - Behavioral equivalence between monitor state machine and defunctionalized coalgebra
-- - WITHOUT postulates for extended lambda equality!
-- - Pure coalgebraic reasoning with behavioral bisimilarity
--
-- Per-frame stepping (step-bisim):
-- ✅ Atomic p - base case (evaluates predicate at current frame)
-- ✅ Not φ - inverts inner result
-- ✅ And φ ψ - both must hold (Kleene logic, 9 valid combinations)
-- ✅ Or φ ψ - either must hold (Kleene logic, 9 valid combinations)
-- ✅ Always φ - must hold at all frames, with resolved flag tracking
-- ✅ Eventually φ - must hold at some frame
-- ✅ Until φ ψ - φ must hold until ψ (7 valid combinations)
-- ✅ Release φ ψ - dual of Until, with resolved flag tracking
-- ✅ Next φ - φ holds at next state (modal states: waiting + active)
-- ✅ MetricEventually φ - bounded eventually (window logic + inner bisimilarity)
-- ✅ MetricAlways φ - bounded always (window logic + resolved flag)
-- ✅ MetricUntil φ ψ - bounded until (window logic + 11 cases)
-- ✅ MetricRelease φ ψ - bounded release (window logic + resolved flag)
--
-- End-of-stream finalization (finalize-bisim):
-- ✅ All 14 operators: finalizeEval st ≡ finalizeL proc when Relate st proc
--
-- Key insight: The proof is GENERIC over inner formulas!
-- - All relate constructors take ANY relation rel : Relate st φ
-- - By structural induction, this covers ALL formulas built from proven operators
-- - Example: Always (Not (Next (And (Atomic p) (Atomic q)))) proven via composition

-- ============================================================================
-- TRUST BOUNDARY: Signal predicate evaluation
-- ============================================================================

-- The proofs above are PARAMETRIC over the atomic predicate evaluator:
--   evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → SignalVal) → SignalVal
-- Both coalgebras receive the same predicate function `p : TimedFrame → SignalVal`,
-- so bisimilarity holds for ALL possible predicates — not just correct ones.
--
-- This is strictly stronger than proving correctness for a specific predicate.
-- The LTL engine is generic; it guarantees temporal logic semantics regardless
-- of what the predicate computes.
--
-- Whether predicates correctly evaluate CAN signals (extraction, scaling,
-- comparison) is a SEPARATE concern, covered by:
--   - CAN/Encoding.agda: injectSignal-preserves-disjoint-bits
--   - CAN/Endianness.agda: extractBits-injectBits-roundtrip
--   - CAN/Batch/Properties.agda: injectAll-preserves-disjoint
--   - Data/BitVec/Conversion.agda: bitVec-roundtrip, bitVecToℕ-bounded
--
-- Together: LTL bisimilarity + CAN encoding proofs cover the full pipeline
-- from raw CAN frames to temporal verdict, with no gap between the layers.

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
-- This shows that for ANY formula built from the 14 proven operators,
-- we can mechanically construct both the initial state and the bisimilarity relation!

-- ============================================================================
-- FINALIZE BISIMILARITY: End-of-stream verdict is the same on both sides
-- ============================================================================

-- Prove that finalizeEval (evaluator) and finalizeL (coalgebra) produce
-- the same FinalVerdict when the states are related.
--
-- This completes the end-to-end correctness: bisimilar stepping during
-- the stream AND the same final verdict at end of stream.

finalize-bisim : ∀ {st : LTLEvalState} {proc : LTLProc}
  → Relate st proc
  → finalizeEval st ≡ finalizeL proc

-- Atomic: both return Fails
finalize-bisim (atomic-relate {p}) = refl

-- Not: compose inner result
finalize-bisim (not-relate {st} {φ} rel)
  with finalizeEval st | finalizeL φ | finalize-bisim rel
... | Holds   | .Holds   | refl = refl
... | Fails _ | .(Fails _) | refl = refl

-- And: compose left, then right
finalize-bisim (and-relate {st1} {st2} {φ} {ψ} rel1 rel2)
  with finalizeEval st1 | finalizeL φ | finalize-bisim rel1
... | Fails r | .(Fails r) | refl = refl
... | Holds   | .Holds     | refl
  with finalizeEval st2 | finalizeL ψ | finalize-bisim rel2
...   | Fails r | .(Fails r) | refl = refl
...   | Holds   | .Holds     | refl = refl

-- Or: compose left, then right
finalize-bisim (or-relate {st1} {st2} {φ} {ψ} rel1 rel2)
  with finalizeEval st1 | finalizeL φ | finalize-bisim rel1
... | Holds   | .Holds     | refl = refl
... | Fails _ | .(Fails _) | refl
  with finalizeEval st2 | finalizeL ψ | finalize-bisim rel2
...   | Holds   | .Holds     | refl = refl
...   | Fails r | .(Fails r) | refl = refl

-- Always: resolved flag determines verdict (same on both sides)
finalize-bisim (always-relate {false} _) = refl
finalize-bisim (always-relate {true} _) = refl

-- Eventually: both return Fails
finalize-bisim (eventually-relate _) = refl

-- Until: both return Fails
finalize-bisim (until-relate _ _) = refl

-- Next waiting: both return Fails
finalize-bisim (next-waiting-relate _) = refl

-- Next active: delegate to inner
finalize-bisim (next-active-relate rel) = finalize-bisim rel

-- MetricEventually: both return Fails
finalize-bisim (metric-eventually-relate _) = refl

-- MetricAlways: resolved flag determines verdict
finalize-bisim (metric-always-relate {false} _) = refl
finalize-bisim (metric-always-relate {true} _) = refl

-- Release: resolved flag determines verdict
finalize-bisim (release-relate {false} _ _) = refl
finalize-bisim (release-relate {true} _ _) = refl

-- MetricUntil: both return Fails
finalize-bisim (metric-until-relate _ _) = refl

-- MetricRelease: resolved flag determines verdict
finalize-bisim (metric-release-relate {false} _ _) = refl
finalize-bisim (metric-release-relate {true} _ _) = refl

-- ============================================================================
-- INIT-RELATE: Initial states are related
-- ============================================================================

-- Prove that `initState φ` (evaluator) and `initProc φ` (coalgebra) are
-- related by `Relate` for any LTL formula φ.
--
-- This completes the proof chain:
--   1. init-relate:    starting states are related
--   2. step-bisim:     each frame preserves relatedness
--   3. finalize-bisim: final verdict is identical
--
-- Together, these three proofs establish end-to-end correctness:
-- for any LTL formula, the incremental evaluator and the defunctionalized
-- coalgebra produce identical observations on every frame and the same
-- final verdict at end of stream.

init-relate : ∀ (φ : LTL (TimedFrame → SignalVal))
  → Relate (initState φ) (initProc φ)

-- Atomic: AtomicState ~ AtomicProc p
init-relate (Atomic p) = atomic-relate

-- Propositional: structural recursion
init-relate (Not φ)   = not-relate (init-relate φ)
init-relate (And φ ψ) = and-relate (init-relate φ) (init-relate ψ)
init-relate (Or φ ψ)  = or-relate (init-relate φ) (init-relate ψ)

-- Next: starts in waiting mode on both sides
init-relate (Next φ) = next-waiting-relate (init-relate φ)

-- Unbounded temporal: structural recursion
-- Safety operators start with resolved=false on both sides
init-relate (Always φ)    = always-relate (init-relate φ)
init-relate (Eventually φ) = eventually-relate (init-relate φ)
init-relate (Until φ ψ)   = until-relate (init-relate φ) (init-relate ψ)
init-relate (Release φ ψ) = release-relate (init-relate φ) (init-relate ψ)

-- Bounded temporal: both sides start with startTime=0
-- Safety operators start with resolved=false on both sides
init-relate (MetricEventually _ φ)    = metric-eventually-relate (init-relate φ)
init-relate (MetricAlways _ φ)        = metric-always-relate (init-relate φ)
init-relate (MetricUntil _ φ ψ)       = metric-until-relate (init-relate φ) (init-relate ψ)
init-relate (MetricRelease _ φ ψ)     = metric-release-relate (init-relate φ) (init-relate ψ)

