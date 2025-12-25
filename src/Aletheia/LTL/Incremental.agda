{-# OPTIONS --safe --without-K --guardedness #-}

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
... | Satisfied = Continue (AlwaysState st)  -- Satisfied on this frame, keep checking

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
... | Continue st1' = Continue (UntilState st1' st2')
... | Satisfied = Continue (UntilState st1 st2')  -- φ holds, keep waiting for ψ
stepEval (Until φ ψ) eval (UntilState st1 st2) prev curr | Violated _
  -- ψ failed, check if φ still holds
  with stepEval φ eval st1 prev curr
... | Violated ce = Violated ce  -- Both failed
... | Continue st1' = Continue (UntilState st1' st2)
... | Satisfied = Continue (UntilState st1 st2)

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
    handleInWindow (Violated _) start = Continue (EventuallyWithinState start st)

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
    handleInWindow Satisfied start = Continue (AlwaysWithinState start st)

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
-- MAIN INCREMENTAL CHECKER
-- ============================================================================

-- Check a formula on a list with early termination
-- Structurally recursive on both formula and list
-- Main recursive checker (structural on formula)
-- Takes the start timestamp explicitly for bounded operators
checkFormula : ℕ → List TimedFrame → LTL (TimedFrame → Bool) → Bool

-- Atomic: check first frame
checkFormula _ [] (Atomic _) = true  -- Empty = vacuous
checkFormula _ (tf ∷ _) (Atomic pred) = pred tf

-- Not: invert
checkFormula start trace (Not ψ) = not (checkFormula start trace ψ)

-- And: both must hold (short-circuit on failure)
checkFormula start trace (And ψ₁ ψ₂) =
  if checkFormula start trace ψ₁
  then checkFormula start trace ψ₂
  else false

-- Or: either must hold (short-circuit on success)
checkFormula start trace (Or ψ₁ ψ₂) =
  if checkFormula start trace ψ₁
  then true
  else checkFormula start trace ψ₂

-- Next: check second frame
checkFormula _ [] (Next _) = true
checkFormula _ (_ ∷ []) (Next _) = true
checkFormula start (_ ∷ rest) (Next ψ) = checkFormula start rest ψ

-- Always: must hold on all frames (early termination on violation)
checkFormula start trace (Always ψ) = goAlways trace
  where
    goAlways : List TimedFrame → Bool
    goAlways [] = true
    goAlways (tf ∷ rest) =
      if evalAtFrame tf ψ
      then goAlways rest  -- Continue checking
      else false          -- Violated! Early termination

-- Eventually: must hold somewhere (early termination on satisfaction)
checkFormula start trace (Eventually ψ) = goEventually trace
  where
    goEventually : List TimedFrame → Bool
    goEventually [] = false  -- Never satisfied
    goEventually (tf ∷ rest) =
      if evalAtFrame tf ψ
      then true               -- Found! Early termination
      else goEventually rest  -- Keep looking

-- Until: φ until ψ
checkFormula start trace (Until ψ₁ ψ₂) = goUntil trace
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
checkFormula start trace (EventuallyWithin windowMicros ψ) = goEW trace
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
checkFormula start trace (AlwaysWithin windowMicros ψ) = goAW trace
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
-- NOTE: checkIncremental and checkMultiple REMOVED
-- These were reference/specification functions never used in production.
-- Production uses stepEval (streaming state machine) exclusively.
-- See: /home/nicolas/.claude/plans/synthetic-honking-goblet.md for rationale.
-- ============================================================================

-- ============================================================================
-- COUNTEREXAMPLE GENERATION (legacy list-based checking)
-- ============================================================================

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
