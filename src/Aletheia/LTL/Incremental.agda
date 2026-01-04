{-# OPTIONS --safe --without-K #-}

-- Incremental LTL model checker for finite traces with early termination.
--
-- Purpose: Check LTL properties over finite frame lists with progressive evaluation.
-- Key features: Early termination (stops when result known), short-circuit And/Or evaluation.
-- Role: Used by Protocol.StreamState for real-time violation detection during streaming.
--
-- Algorithm: Accumulates frames, evaluates formulas progressively, returns violation on failure.
-- Performance: Optimized for streaming (doesn't wait for full trace).
module Aletheia.LTL.Incremental where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_)
open import Aletheia.LTL.Syntax
open import Aletheia.LTL.Evaluation using () renaming (evalAtFrame to evalAtFrameWith)
open import Aletheia.Trace.Context using (TimedFrame; timestamp)

-- ============================================================================
-- INCREMENTAL LTL CHECKING (O(1) MEMORY)
-- ============================================================================

-- Process frames one at a time without accumulating history.
-- Key features:
-- 1. O(1) memory: no accumulation of frames
-- 2. Stateful evaluation: each property tracks its own state
-- 3. Early termination: stops when result is known
-- 4. Generic over predicate types (avoids circular dependencies)

-- ============================================================================
-- COUNTEREXAMPLE SUPPORT
-- ============================================================================

-- Counterexample: evidence of why a property failed
record Counterexample : Set where
  constructor mkCounterexample
  field
    violatingFrame : TimedFrame    -- The frame where violation occurred
    reason : String                -- Human-readable explanation

-- ============================================================================
-- EVALUATION STATE
-- ============================================================================

-- State for incremental LTL evaluation
-- Tracks position in the formula and intermediate results
data LTLEvalState : Set where
  -- Atomic predicates (stateless)
  AtomicState : LTLEvalState

  -- Propositional operators
  NotState : LTLEvalState → LTLEvalState
  AndState : LTLEvalState → LTLEvalState → LTLEvalState
  OrState  : LTLEvalState → LTLEvalState → LTLEvalState

  -- Temporal operators
  NextState : LTLEvalState → LTLEvalState       -- Waiting to skip first frame
  NextActive : LTLEvalState → LTLEvalState      -- Skipped, now evaluating inner

  -- Always: track if violated
  AlwaysState : LTLEvalState → LTLEvalState
  AlwaysFailed : LTLEvalState

  -- Eventually: track if satisfied
  EventuallyState : LTLEvalState → LTLEvalState
  EventuallySucceeded : LTLEvalState

  -- Until: track state of both subformulas
  UntilState : LTLEvalState → LTLEvalState → LTLEvalState
  UntilSucceeded : LTLEvalState
  UntilFailed : LTLEvalState

  -- Release: dual of Until (ψ holds until φ releases it)
  ReleaseState : LTLEvalState → LTLEvalState → LTLEvalState
  ReleaseSucceeded : LTLEvalState
  ReleaseFailed : LTLEvalState

  -- Bounded temporal operators: track start time and result
  MetricEventuallyState : ℕ → LTLEvalState → LTLEvalState  -- startTime
  MetricEventuallyFailed : LTLEvalState
  MetricEventuallySucceeded : LTLEvalState

  MetricAlwaysState : ℕ → LTLEvalState → LTLEvalState  -- startTime
  MetricAlwaysFailed : LTLEvalState
  MetricAlwaysSucceeded : LTLEvalState

  MetricUntilState : ℕ → LTLEvalState → LTLEvalState → LTLEvalState  -- startTime, left, right
  MetricUntilSucceeded : LTLEvalState
  MetricUntilFailed : LTLEvalState

  MetricReleaseState : ℕ → LTLEvalState → LTLEvalState → LTLEvalState  -- startTime, left, right
  MetricReleaseSucceeded : LTLEvalState
  MetricReleaseFailed : LTLEvalState

-- Result of one evaluation step (parameterized by state type)
-- Allows comparing observations from different coalgebras (monitor vs defunctionalized LTL)
-- CRITICAL: Continue now carries remaining time as observable for bounded operators
--   - Unbounded operators (Always, Eventually, Until, etc.): return 0 (no time bound)
--   - Bounded operators (MetricEventually, MetricAlways): return remaining microseconds
data StepResult (S : Set) : Set where
  Continue : ℕ → S → StepResult S  -- remaining time (0 = unbounded) + state
  Violated : Counterexample → StepResult S  -- Property violated
  Satisfied : StepResult S  -- Property satisfied

-- ============================================================================
-- INITIALIZATION
-- ============================================================================

-- Initialize evaluation state from formula
-- Bounded operators start with 0 timestamp (updated on first frame)
initState : ∀ {Atom : Set} → LTL Atom → LTLEvalState
initState (Atomic _) = AtomicState
initState (Not φ) = NotState (initState φ)
initState (And φ ψ) = AndState (initState φ) (initState ψ)
initState (Or φ ψ) = OrState (initState φ) (initState ψ)
initState (Next φ) = NextState (initState φ)
initState (Always φ) = AlwaysState (initState φ)
initState (Eventually φ) = EventuallyState (initState φ)
initState (Until φ ψ) = UntilState (initState φ) (initState ψ)
initState (Release φ ψ) = ReleaseState (initState φ) (initState ψ)
initState (MetricEventually _ φ) = MetricEventuallyState 0 (initState φ)
initState (MetricAlways _ φ) = MetricAlwaysState 0 (initState φ)
initState (MetricUntil _ φ ψ) = MetricUntilState 0 (initState φ) (initState ψ)
initState (MetricRelease _ φ ψ) = MetricReleaseState 0 (initState φ) (initState ψ)

-- ============================================================================
-- INCREMENTAL EVALUATION HELPERS
-- ============================================================================

-- Remaining time semantics (0 = unbounded/infinite time)
-- Key insight from MTL formal semantics:
--   (ρ,m)⊨MTL α∧β iff (ρ,m)⊨MTL α and (ρ,m)⊨MTL β
-- Both α and β evaluated at SAME time point m, each with own time window.
-- Time constraints live in CHILDREN (bounded operators), not PARENTS (compound operators).
--
-- Therefore:
--   - Bounded operators (MetricEventually, MetricAlways) return actual remaining microseconds
--   - Unbounded operators (And, Or, Not, Always, Eventually, Until, Next) return 0
--   - Children track their own times; parents don't aggregate!

-- Helper: combine results for And operator (avoids nested with-clauses in stepEval)
stepEval-and-helper : StepResult LTLEvalState → StepResult LTLEvalState → LTLEvalState → LTLEvalState → StepResult LTLEvalState
stepEval-and-helper (Violated ce) _ _ _ = Violated ce  -- Left failed
stepEval-and-helper (Continue _ st1') (Violated ce) _ _ = Violated ce  -- Right failed
stepEval-and-helper (Continue _ st1') (Continue _ st2') _ _ = Continue 0 (AndState st1' st2')  -- And is unbounded
stepEval-and-helper (Continue _ st1') Satisfied _ st2 = Continue 0 (AndState st1' st2)  -- And is unbounded
stepEval-and-helper Satisfied (Violated ce) _ _ = Violated ce  -- Right failed
stepEval-and-helper Satisfied (Continue _ st2') st1 _ = Continue 0 (AndState st1 st2')  -- And is unbounded
stepEval-and-helper Satisfied Satisfied _ _ = Satisfied  -- Both satisfied

-- Helper: combine results for Or operator (avoids nested with-clauses in stepEval)
stepEval-or-helper : StepResult LTLEvalState → StepResult LTLEvalState → LTLEvalState → LTLEvalState → StepResult LTLEvalState
stepEval-or-helper Satisfied _ _ _ = Satisfied  -- Left satisfied
stepEval-or-helper (Continue _ st1') Satisfied _ _ = Satisfied  -- Right satisfied
stepEval-or-helper (Continue _ st1') (Continue _ st2') _ _ = Continue 0 (OrState st1' st2')
stepEval-or-helper (Continue _ st1') (Violated _) _ st2 = Continue 0 (OrState st1' st2)  -- Right violated, keep checking left
stepEval-or-helper (Violated _) Satisfied _ _ = Satisfied  -- Right satisfied
stepEval-or-helper (Violated _) (Continue _ st2') st1 _ = Continue 0 (OrState st1 st2')  -- Left violated, keep checking right
stepEval-or-helper (Violated _) (Violated ce) _ _ = Violated ce  -- Both violated


-- ============================================================================
-- OBSERVABLE-LEVEL HANDLERS FOR BOUNDED OPERATORS
-- ============================================================================

-- These handlers work purely at the observable StepResult level.
-- They only pattern match on StepResult observations, not on state structure.
-- The states are used ONLY to reconstruct continuations, not for branching logic.

-- MetricEventually handler: Continues until inner formula satisfied or window expires
metricEventuallyHandlerIncr : ℕ → ℕ → LTLEvalState → StepResult LTLEvalState → ℕ → ℕ → StepResult LTLEvalState
metricEventuallyHandlerIncr windowMicros start st Satisfied _ _ = Satisfied
metricEventuallyHandlerIncr windowMicros start st (Continue _ st') _ remaining =
  Continue remaining (MetricEventuallyState start st')
metricEventuallyHandlerIncr windowMicros start st (Violated _) _ remaining =
  Continue remaining (MetricEventuallyState start st)  -- Keep looking

-- MetricAlways handler: Continues while inner formula holds, fails if violated
metricAlwaysHandlerIncr : ℕ → ℕ → LTLEvalState → StepResult LTLEvalState → ℕ → ℕ → StepResult LTLEvalState
metricAlwaysHandlerIncr windowMicros start st (Violated ce) _ _ = Violated ce
metricAlwaysHandlerIncr windowMicros start st (Continue _ st') _ remaining =
  Continue remaining (MetricAlwaysState start st')
metricAlwaysHandlerIncr windowMicros start st Satisfied _ remaining =
  Continue remaining (MetricAlwaysState start st)  -- Keep checking

-- MetricUntil handler: φ must hold until ψ becomes true, within window
-- Observable logic: Branch ONLY on StepResult patterns (ψ then φ)
metricUntilHandlerIncr : ℕ → ℕ → LTLEvalState → LTLEvalState → StepResult LTLEvalState → StepResult LTLEvalState → ℕ → ℕ → StepResult LTLEvalState
-- ψ satisfied → MetricUntil satisfied
metricUntilHandlerIncr _ _ _ _ Satisfied _ _ _ = Satisfied
-- ψ continues, φ violated → MetricUntil violated
metricUntilHandlerIncr _ _ _ _ (Continue _ st2') (Violated ce) _ _ = Violated ce
-- ψ continues, φ continues → MetricUntil continues
metricUntilHandlerIncr windowMicros start st1 st2 (Continue _ st2') (Continue _ st1') _ remaining =
  Continue remaining (MetricUntilState start st1' st2')
-- ψ continues, φ satisfied → MetricUntil continues (preserve original φ)
metricUntilHandlerIncr windowMicros start st1 st2 (Continue _ st2') Satisfied _ remaining =
  Continue remaining (MetricUntilState start st1 st2')
-- ψ violated, φ violated → MetricUntil violated
metricUntilHandlerIncr _ _ _ _ (Violated _) (Violated ce) _ _ = Violated ce
-- ψ violated, φ continues → MetricUntil continues (preserve original ψ)
metricUntilHandlerIncr windowMicros start st1 st2 (Violated _) (Continue _ st1') _ remaining =
  Continue remaining (MetricUntilState start st1' st2)
-- ψ violated, φ satisfied → MetricUntil continues (preserve both)
metricUntilHandlerIncr windowMicros start st1 st2 (Violated _) Satisfied _ remaining =
  Continue remaining (MetricUntilState start st1 st2)

-- MetricRelease handler: ψ must hold until φ releases it, within window
-- Observable logic: Branch ONLY on StepResult patterns (φ then ψ)
metricReleaseHandlerIncr : ℕ → ℕ → LTLEvalState → LTLEvalState → StepResult LTLEvalState → StepResult LTLEvalState → ℕ → ℕ → StepResult LTLEvalState
-- φ satisfied → MetricRelease satisfied (release condition met)
metricReleaseHandlerIncr _ _ _ _ Satisfied _ _ _ = Satisfied
-- φ continues, ψ violated → MetricRelease violated (ψ must hold until release)
metricReleaseHandlerIncr _ _ _ _ (Continue _ st1') (Violated ce) _ _ = Violated ce
-- φ continues, ψ continues → MetricRelease continues
metricReleaseHandlerIncr windowMicros start st1 st2 (Continue _ st1') (Continue _ st2') _ remaining =
  Continue remaining (MetricReleaseState start st1' st2')
-- φ continues, ψ satisfied → MetricRelease continues (preserve original ψ)
metricReleaseHandlerIncr windowMicros start st1 st2 (Continue _ st1') Satisfied _ remaining =
  Continue remaining (MetricReleaseState start st1' st2)
-- φ violated, ψ violated → MetricRelease violated
metricReleaseHandlerIncr _ _ _ _ (Violated _) (Violated ce) _ _ = Violated ce
-- φ violated, ψ continues → MetricRelease continues (preserve original φ)
metricReleaseHandlerIncr windowMicros start st1 st2 (Violated _) (Continue _ st2') _ remaining =
  Continue remaining (MetricReleaseState start st1 st2')
-- φ violated, ψ satisfied → MetricRelease continues (preserve both)
metricReleaseHandlerIncr windowMicros start st1 st2 (Violated _) Satisfied _ remaining =
  Continue remaining (MetricReleaseState start st1 st2)

-- ============================================================================
-- INCREMENTAL EVALUATION
-- ============================================================================

-- Evaluate one frame incrementally
-- Generic over predicate type to avoid circular dependencies
-- The evaluator function takes: prevFrame, currFrame, predicate → Bool
stepEval : ∀ {Atom : Set}
         → LTL Atom                                     -- Formula
         → (Maybe TimedFrame → TimedFrame → Atom → Bool)  -- Predicate evaluator
         → LTLEvalState                                 -- Current state
         → Maybe TimedFrame                             -- Previous frame (for ChangedBy)
         → TimedFrame                                   -- Current frame
         → StepResult LTLEvalState

-- Atomic: evaluate predicate on current frame
-- Returns Satisfied (not Continue) because atomic props evaluate at single point
stepEval (Atomic p) eval AtomicState prev curr =
  if eval prev curr p
  then Satisfied
  else Violated (mkCounterexample curr "atomic predicate failed")

-- Not: evaluate inner and invert result
stepEval (Not φ) eval (NotState st) prev curr
  with stepEval φ eval st prev curr
... | Continue _ st' = Continue 0 (NotState st')
... | Violated _ = Satisfied  -- Inner violated = outer satisfied (¬false = true)
... | Satisfied = Violated (mkCounterexample curr "negation failed (inner satisfied)")

-- And: both must hold (uses helper to avoid nested with-clauses)
stepEval (And φ ψ) eval (AndState st1 st2) prev curr =
  stepEval-and-helper (stepEval φ eval st1 prev curr) (stepEval ψ eval st2 prev curr) st1 st2

-- Or: either must hold (uses helper to avoid nested with-clauses)
stepEval (Or φ ψ) eval (OrState st1 st2) prev curr =
  stepEval-or-helper (stepEval φ eval st1 prev curr) (stepEval ψ eval st2 prev curr) st1 st2

-- Next: skip first frame, then evaluate on subsequent frames
-- First frame: skip it without evaluating, transition to NextActive
stepEval (Next φ) eval (NextState st) prev curr
  = Continue 0 (NextActive st)

-- Subsequent frames: evaluate inner formula φ
stepEval (Next φ) eval (NextActive st) prev curr
  with stepEval φ eval st prev curr
... | Continue _ st' = Continue 0 (NextActive st')
... | Violated ce = Violated ce
... | Satisfied = Satisfied

-- Always: must hold on every frame
stepEval (Always φ) eval (AlwaysState st) prev curr
  with stepEval φ eval st prev curr
... | Continue _ st' = Continue 0 (AlwaysState st')
... | Violated ce = Violated ce  -- Violation detected
... | Satisfied = Continue 0 (AlwaysState st)  -- Preserve state!

stepEval (Always _) _ AlwaysFailed _ curr = Violated (mkCounterexample curr "Always already failed")

-- Eventually: must hold at some point
stepEval (Eventually φ) eval (EventuallyState st) prev curr
  with stepEval φ eval st prev curr
... | Continue _ st' = Continue 0 (EventuallyState st')
... | Violated _ = Continue 0 (EventuallyState st)  -- Not yet, keep looking
... | Satisfied = Satisfied  -- Found!

stepEval (Eventually _) _ EventuallySucceeded _ _ = Satisfied

-- Until: φ until ψ
-- Until: φ must hold until ψ becomes true
-- Refactored to use flat with-clauses (easier to prove bisimilarity)
stepEval (Until φ ψ) eval (UntilState st1 st2) prev curr
  with stepEval ψ eval st2 prev curr | stepEval φ eval st1 prev curr
-- ψ satisfied → Until satisfied (φ result doesn't matter)
... | Satisfied | _ = Satisfied
-- ψ continues, φ violated → Until violated
... | Continue _ st2' | Violated ce = Violated ce
-- ψ continues, φ continues → Until continues
... | Continue _ st2' | Continue _ st1' = Continue 0 (UntilState st1' st2')
-- ψ continues, φ satisfied → Until continues (preserve original φ state)
... | Continue _ st2' | Satisfied = Continue 0 (UntilState st1 st2')
-- ψ violated, φ violated → Until violated
... | Violated _ | Violated ce = Violated ce
-- ψ violated, φ continues → Until continues (preserve original ψ state)
... | Violated _ | Continue _ st1' = Continue 0 (UntilState st1' st2)
-- ψ violated, φ satisfied → Until continues (preserve both)
... | Violated _ | Satisfied = Continue 0 (UntilState st1 st2)

stepEval (Until _ _) _ UntilSucceeded _ _ = Satisfied
stepEval (Until _ _) _ UntilFailed _ curr = Violated (mkCounterexample curr "Until failed")

-- Release: φ releases ψ (dual of Until)
-- ψ must hold until φ releases it, or ψ holds forever
-- Semantics: φ R ψ ≡ ¬(¬φ U ¬ψ)
stepEval (Release φ ψ) eval (ReleaseState st1 st2) prev curr
  with stepEval φ eval st1 prev curr | stepEval ψ eval st2 prev curr
-- φ satisfied → Release satisfied (φ released ψ, mission accomplished)
... | Satisfied | _ = Satisfied
-- φ continues, ψ violated → Release violated (ψ must hold until release)
... | Continue _ st1' | Violated ce = Violated ce
-- φ continues, ψ continues → Release continues
... | Continue _ st1' | Continue _ st2' = Continue 0 (ReleaseState st1' st2')
-- φ continues, ψ satisfied → Release continues (ψ still holding, waiting for φ)
... | Continue _ st1' | Satisfied = Continue 0 (ReleaseState st1' st2)
-- φ violated, ψ violated → Release violated
... | Violated _ | Violated ce = Violated ce
-- φ violated, ψ continues → Release continues (ψ holds, φ may never come)
... | Violated _ | Continue _ st2' = Continue 0 (ReleaseState st1 st2')
-- φ violated, ψ satisfied → Release continues (ψ holds, φ may never come)
... | Violated _ | Satisfied = Continue 0 (ReleaseState st1 st2)

stepEval (Release _ _) _ ReleaseSucceeded _ _ = Satisfied
stepEval (Release _ _) _ ReleaseFailed _ curr = Violated (mkCounterexample curr "Release failed")

-- MetricEventually: must hold within time window
stepEval (MetricEventually windowMicros φ) eval (MetricEventuallyState startTime st) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed  -- OBSERVABLE remaining time
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricEventuallyHandlerIncr windowMicros actualStart st (stepEval φ eval st prev curr) actualStart remaining
     else Violated (mkCounterexample curr "MetricEventually: window expired")

stepEval (MetricEventually _ _) _ MetricEventuallySucceeded _ _ = Satisfied
stepEval (MetricEventually _ _) _ MetricEventuallyFailed _ curr = Violated (mkCounterexample curr "MetricEventually: window expired")

-- MetricAlways: must hold throughout time window
stepEval (MetricAlways windowMicros φ) eval (MetricAlwaysState startTime st) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed  -- OBSERVABLE remaining time
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricAlwaysHandlerIncr windowMicros actualStart st (stepEval φ eval st prev curr) actualStart remaining
     else Satisfied  -- Window complete, always held

stepEval (MetricAlways _ _) _ MetricAlwaysSucceeded _ _ = Satisfied
stepEval (MetricAlways _ _) _ MetricAlwaysFailed _ curr = Violated (mkCounterexample curr "MetricAlways: violated within window")

-- MetricUntil: φ must hold until ψ within time window
stepEval (MetricUntil windowMicros φ ψ) eval (MetricUntilState startTime st1 st2) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricUntilHandlerIncr windowMicros actualStart st1 st2 (stepEval ψ eval st2 prev curr) (stepEval φ eval st1 prev curr) actualStart remaining
     else Violated (mkCounterexample curr "MetricUntil: window expired before ψ")

stepEval (MetricUntil _ _ _) _ MetricUntilSucceeded _ _ = Satisfied
stepEval (MetricUntil _ _ _) _ MetricUntilFailed _ curr = Violated (mkCounterexample curr "MetricUntil: window expired")

-- MetricRelease: ψ must hold until φ releases it within time window
stepEval (MetricRelease windowMicros φ ψ) eval (MetricReleaseState startTime st1 st2) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricReleaseHandlerIncr windowMicros actualStart st1 st2 (stepEval φ eval st1 prev curr) (stepEval ψ eval st2 prev curr) actualStart remaining
     else Satisfied  -- Window complete, ψ held throughout (or was released)

stepEval (MetricRelease _ _ _) _ MetricReleaseSucceeded _ _ = Satisfied
stepEval (MetricRelease _ _ _) _ MetricReleaseFailed _ curr = Violated (mkCounterexample curr "MetricRelease failed")

-- Catch-all for mismatched formula/state pairs (shouldn't happen if initState is used)
stepEval _ _ _ _ curr = Violated (mkCounterexample curr "internal error: formula/state mismatch")

-- ============================================================================
-- EVALUATE NON-TEMPORAL FORMULAS (legacy list-based checking)
-- ============================================================================

-- Evaluate formula at a single frame (handles Atomic, Not, And, Or)
-- Temporal operators return false (they need the full trace)
-- Delegates to LTL.Evaluation.evalAtFrame with temporalDefault=false
evalAtFrame : ∀ {A : Set} → A → LTL (A → Bool) → Bool
evalAtFrame = evalAtFrameWith false


-- ============================================================================
-- NOTE: Legacy list-based evaluators REMOVED
-- Removed: checkFormula, checkWithCounterexample, checkIncremental, checkMultiple
-- These were reference/specification functions never used in production.
-- Production uses stepEval (streaming state machine) exclusively.
-- See: /home/nicolas/.claude/plans/synthetic-honking-goblet.md for rationale.
-- ============================================================================

-- ============================================================================
-- COUNTEREXAMPLE TYPES
-- ============================================================================

-- Result of checking with counterexample support
-- Used by Coinductive.agda's checkColistCE for counterexample generation
data CheckResult : Set where
  Pass : CheckResult
  Fail : Counterexample → CheckResult

-- ============================================================================
-- NOTE ON MEMORY-BOUNDED STREAMING
-- ============================================================================
--
-- True memory-bounded streaming (processing frames without building full list)
-- requires either:
-- 1. Sized types (--sized-types) to prove termination on coinductive streams
-- 2. A fundamentally different parser architecture with lazy I/O
--
-- Current approach: Use list-based checking which compiles to lazy Haskell
-- code via MAlonzo. This provides reasonable memory efficiency for most traces.
--
-- For 1GB+ traces, consider:
-- - Chunked processing (check in segments)
-- - External preprocessing to filter relevant frames
-- - Streaming parser in Haskell shim (breaks verification boundary)
