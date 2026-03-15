{-# OPTIONS --safe --without-K #-}

-- Shared types for incremental LTL model checking.
--
-- Provides: Counterexample, StepResult, FinalVerdict
-- These are used by both Coalgebra.agda (proof-oriented stepL) and
-- Protocol/StreamState.agda (production code).
--
-- The actual step function (stepL) lives in Coalgebra.agda, using
-- Havelund-Rosu formula progression with ℕ-indexed predicates.
module Aletheia.LTL.Incremental where

open import Aletheia.Prelude
open import Aletheia.Trace.CANTrace using (TimedFrame)

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
-- STEP RESULT
-- ============================================================================

-- Result of one evaluation step (parameterized by state type)
-- Three constructors: Continue, Violated, Satisfied.
-- Unknown/Pending signals produce Continue (formula keeps processing).
-- CRITICAL: Continue carries remaining time as observable for bounded operators
--   - Unbounded operators (Always, Eventually, Until, etc.): return 0 (no time bound)
--   - Bounded operators (MetricEventually, MetricAlways): return remaining microseconds
data StepResult (S : Set) : Set where
  Continue     : ℕ → S → StepResult S       -- remaining time (0 = unbounded) + state
  Violated     : Counterexample → StepResult S  -- Property violated
  Satisfied    : StepResult S               -- Property satisfied

-- ============================================================================
-- END-OF-STREAM FINALIZATION
-- ============================================================================

-- Verdict for a property at end-of-stream
data FinalVerdict : Set where
  Holds : FinalVerdict                -- Property satisfied on finite trace
  Fails : String → FinalVerdict       -- Property violated at end-of-stream
