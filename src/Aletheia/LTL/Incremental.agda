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

  -- Bounded temporal operators: track start time and result
  EventuallyWithinState : ℕ → LTLEvalState → LTLEvalState  -- startTime
  EventuallyWithinFailed : LTLEvalState
  EventuallyWithinSucceeded : LTLEvalState

  AlwaysWithinState : ℕ → LTLEvalState → LTLEvalState  -- startTime
  AlwaysWithinFailed : LTLEvalState
  AlwaysWithinSucceeded : LTLEvalState

-- Result of one evaluation step
data StepResult : Set where
  Continue : LTLEvalState → StepResult  -- Keep checking
  Violated : Counterexample → StepResult  -- Property violated
  Satisfied : StepResult  -- Property satisfied (Eventually)

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
initState (EventuallyWithin _ φ) = EventuallyWithinState 0 (initState φ)
initState (AlwaysWithin _ φ) = AlwaysWithinState 0 (initState φ)

-- ============================================================================
-- INCREMENTAL EVALUATION HELPERS
-- ============================================================================

-- Helper: combine results for And operator (avoids nested with-clauses in stepEval)
stepEval-and-helper : StepResult → StepResult → LTLEvalState → LTLEvalState → StepResult
stepEval-and-helper (Violated ce) _ _ _ = Violated ce  -- Left failed
stepEval-and-helper (Continue st1') (Violated ce) _ _ = Violated ce  -- Right failed
stepEval-and-helper (Continue st1') (Continue st2') _ _ = Continue (AndState st1' st2')
stepEval-and-helper (Continue st1') Satisfied st1 _ = Continue (AndState st1' st1)  -- Right satisfied, keep checking left
stepEval-and-helper Satisfied (Violated ce) _ _ = Violated ce  -- Right failed
stepEval-and-helper Satisfied (Continue st2') _ st2 = Continue (AndState st2 st2')  -- Left satisfied, keep checking right
stepEval-and-helper Satisfied Satisfied _ _ = Satisfied  -- Both satisfied

-- Helper: combine results for Or operator (avoids nested with-clauses in stepEval)
stepEval-or-helper : StepResult → StepResult → LTLEvalState → LTLEvalState → StepResult
stepEval-or-helper Satisfied _ _ _ = Satisfied  -- Left satisfied
stepEval-or-helper (Continue st1') Satisfied _ _ = Satisfied  -- Right satisfied
stepEval-or-helper (Continue st1') (Continue st2') _ _ = Continue (OrState st1' st2')
stepEval-or-helper (Continue st1') (Violated _) st1 _ = Continue (OrState st1' st1)  -- Right violated, keep checking left
stepEval-or-helper (Violated _) Satisfied _ _ = Satisfied  -- Right satisfied
stepEval-or-helper (Violated _) (Continue st2') _ st2 = Continue (OrState st2 st2')  -- Left violated, keep checking right
stepEval-or-helper (Violated _) (Violated ce) _ _ = Violated ce  -- Both violated


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
         → StepResult

-- Atomic: evaluate predicate on current frame
-- Returns Satisfied (not Continue) because atomic props evaluate at single point
stepEval (Atomic p) eval AtomicState prev curr =
  if eval prev curr p
  then Satisfied
  else Violated (mkCounterexample curr "atomic predicate failed")

-- Not: evaluate inner and invert result
stepEval (Not φ) eval (NotState st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (NotState st')
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
  = Continue (NextActive st)

-- Subsequent frames: evaluate inner formula φ
stepEval (Next φ) eval (NextActive st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (NextActive st')
... | Violated ce = Violated ce
... | Satisfied = Satisfied

-- Always: must hold on every frame
stepEval (Always φ) eval (AlwaysState st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (AlwaysState st')
... | Violated ce = Violated ce  -- Violation detected
... | Satisfied = Continue (AlwaysState st)  -- Preserve state!

stepEval (Always _) _ AlwaysFailed _ curr = Violated (mkCounterexample curr "Always already failed")

-- Eventually: must hold at some point
stepEval (Eventually φ) eval (EventuallyState st) prev curr
  with stepEval φ eval st prev curr
... | Continue st' = Continue (EventuallyState st')
... | Violated _ = Continue (EventuallyState st)  -- Not yet, keep looking
... | Satisfied = Satisfied  -- Found!

stepEval (Eventually _) _ EventuallySucceeded _ _ = Satisfied

-- Until: φ until ψ
stepEval (Until φ ψ) eval (UntilState st1 st2) prev curr
  -- Check if ψ holds (satisfaction condition)
  with stepEval ψ eval st2 prev curr
... | Satisfied = Satisfied  -- ψ holds, Until satisfied
... | Continue st2'
  -- ψ doesn't hold yet, check if φ holds (waiting condition)
  with stepEval φ eval st1 prev curr
... | Violated ce = Violated ce  -- φ failed before ψ held
... | Continue st1' = Continue (UntilState st1' st2')  -- Both continuing
... | Satisfied = Continue (UntilState st1 st2')  -- Preserve st1
stepEval (Until φ ψ) eval (UntilState st1 st2) prev curr | Violated _
  -- ψ failed, check if φ still holds
  with stepEval φ eval st1 prev curr
... | Violated ce = Violated ce  -- Both failed
... | Continue st1' = Continue (UntilState st1' st2)  -- Preserve st2
... | Satisfied = Continue (UntilState st1 st2)  -- Preserve both

stepEval (Until _ _) _ UntilSucceeded _ _ = Satisfied
stepEval (Until _ _) _ UntilFailed _ curr = Violated (mkCounterexample curr "Until failed")

-- EventuallyWithin: must hold within time window
stepEval (EventuallyWithin windowMicros φ) eval (EventuallyWithinState startTime st) prev curr =
  let currTime = timestamp curr
      -- Initialize start time on first frame
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then handleInWindow (stepEval φ eval st prev curr) actualStart
     else Violated (mkCounterexample curr "EventuallyWithin: window expired")
  where
    handleInWindow : StepResult → ℕ → StepResult
    handleInWindow Satisfied _ = Satisfied
    handleInWindow (Continue st') start = Continue (EventuallyWithinState start st')
    handleInWindow (Violated _) start = Continue (EventuallyWithinState start st)  -- Preserve state

stepEval (EventuallyWithin _ _) _ EventuallyWithinSucceeded _ _ = Satisfied
stepEval (EventuallyWithin _ _) _ EventuallyWithinFailed _ curr = Violated (mkCounterexample curr "EventuallyWithin: window expired")

-- AlwaysWithin: must hold throughout time window
stepEval (AlwaysWithin windowMicros φ) eval (AlwaysWithinState startTime st) prev curr =
  let currTime = timestamp curr
      -- Initialize start time on first frame
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then handleInWindow (stepEval φ eval st prev curr) actualStart
     else Satisfied  -- Window complete, always held
  where
    handleInWindow : StepResult → ℕ → StepResult
    handleInWindow (Violated ce) _ = Violated ce
    handleInWindow (Continue st') start = Continue (AlwaysWithinState start st')
    handleInWindow Satisfied start = Continue (AlwaysWithinState start st)  -- Preserve state

stepEval (AlwaysWithin _ _) _ AlwaysWithinSucceeded _ _ = Satisfied
stepEval (AlwaysWithin _ _) _ AlwaysWithinFailed _ curr = Violated (mkCounterexample curr "AlwaysWithin: violated within window")

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
