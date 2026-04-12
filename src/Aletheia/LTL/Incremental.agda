{-# OPTIONS --safe --without-K #-}

-- Shared types for incremental LTL model checking.
--
-- Provides: LTLReason, Counterexample, StepResult, FinalVerdict
-- These are used by both Coalgebra.agda (proof-oriented stepL) and
-- Protocol/StreamState.agda (production code).
--
-- The actual step function (stepL) lives in Coalgebra.agda, using
-- Havelund-Rosu formula progression with ℕ-indexed predicates.
module Aletheia.LTL.Incremental where

open import Aletheia.Prelude
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- ============================================================================
-- LTL REASON ADT
-- ============================================================================

-- Closed enumeration of all reasons stepL/finalizeL can attribute to a
-- terminal verdict. Replaces the previous bare `String` representation:
-- the wording is now produced by `formatLTLReason` at the JSON boundary
-- (Protocol.ResponseFormat) so the Agda core never traffics in display
-- strings, while bindings still receive the same wire-format text.
--
-- The constructor names follow the convention <operator><cause>:
--   * stepL counterexamples carry the four `*Failed`/`*Expired` reasons
--   * finalizeL Fails verdicts carry the seven `*Unsatisfied`/etc. reasons
--   * finalizeL Unsure verdicts carry the single `AtomicUnresolved` reason
data LTLReason : Set where
  -- stepL counterexample reasons
  AtomicFailed                : LTLReason  -- Atomic predicate evaluated False
  NotStepSatisfied            : LTLReason  -- Not(φ): φ stepped to Satisfied
  MetricEventuallyExpired     : LTLReason  -- F[w] window passed without ψ
  MetricUntilExpired          : LTLReason  -- U[w] window passed without ψ
  -- finalizeL Fails reasons
  NotEosSatisfied             : LTLReason  -- Not(φ): φ finalized to Holds
  NextNoFrame                 : LTLReason  -- X(φ): no next frame at EOS
  EventuallyUnsatisfied       : LTLReason  -- F(φ): φ never satisfied at EOS
  UntilUnsatisfied            : LTLReason  -- U(φ,ψ): ψ never satisfied at EOS
  MetricEventuallyUnsatisfied : LTLReason  -- F[w](φ): φ never within window
  MetricUntilUnsatisfied      : LTLReason  -- U[w](φ,ψ): ψ never within window
  -- finalizeL Unsure reasons
  AtomicUnresolved            : LTLReason  -- Atomic predicate never observed

-- Human-readable rendering. Strings are pinned by binding tests so changes
-- here are wire-format changes — keep substring stability when refactoring.
formatLTLReason : LTLReason → String
formatLTLReason AtomicFailed                = "Atomic: predicate failed"
formatLTLReason NotStepSatisfied            = "Not: inner formula satisfied"
formatLTLReason MetricEventuallyExpired     = "MetricEventually: window expired"
formatLTLReason MetricUntilExpired          = "MetricUntil: window expired before ψ"
formatLTLReason NotEosSatisfied             = "Not: inner satisfied at end of stream"
formatLTLReason NextNoFrame                 = "Next: no next frame available at end of stream"
formatLTLReason EventuallyUnsatisfied       = "Eventually: never satisfied before end of stream"
formatLTLReason UntilUnsatisfied            = "Until: ψ never satisfied before end of stream"
formatLTLReason MetricEventuallyUnsatisfied = "MetricEventually: never satisfied within window before end of stream"
formatLTLReason MetricUntilUnsatisfied      = "MetricUntil: ψ never satisfied within window before end of stream"
formatLTLReason AtomicUnresolved            = "Atomic: predicate never resolved at end of stream"

-- ============================================================================
-- COUNTEREXAMPLE SUPPORT
-- ============================================================================

-- Counterexample: evidence of why a property failed.
--
-- The `reason` field is consumed at two sites:
--   * FrameProcessor/Properties/Step.agda projects it via `Counterexample.reason`
--     when proving dispatchIterResult-violation / handleDataFrame-violation-complete.
--   * Protocol/ResponseFormat.agda formats it (via `formatLTLReason`) into the
--     JSON `reason` field bindings expose to user code.
-- Both sites need a runtime value, so the field cannot be marked @0 / @irr.
record Counterexample : Set where
  constructor mkCounterexample
  field
    violatingFrame : TimedFrame    -- The frame where violation occurred
    reason : LTLReason             -- Closed reason ADT (formatted at JSON boundary)

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

-- Verdict for a property at end-of-stream.
--
-- Three-valued per Kleene logic — faithful to the denotational Unknown
-- that arises when an atomic predicate is never observed on the trace:
--   Holds   — property definitely satisfied on finite trace
--   Fails   — property definitely violated at end-of-stream
--   Unsure  — no evidence either way (e.g. Always(p) on a trace where
--             p's signal was never present; verdictToSV Unsure = Unknown
--             and Sound Unknown _ holds vacuously via sound-m-unk)
-- The LTLReason arguments to Fails and Unsure are formatted at the JSON
-- boundary (Protocol.ResponseFormat) into runtime strings:
--   Fails reason  → Violation (with formatLTLReason reason in CounterexampleData)
--   Unsure reason → Unresolved (with formatLTLReason reason in PropertyResult)
data FinalVerdict : Set where
  Holds  : FinalVerdict                  -- Property satisfied on finite trace
  Fails  : LTLReason → FinalVerdict      -- Property violated at end-of-stream
  Unsure : LTLReason → FinalVerdict      -- Inconclusive at end-of-stream
