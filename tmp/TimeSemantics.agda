{-# OPTIONS --safe --without-K #-}

-- Experiment: How should remaining time work for compound operators?
--
-- Key insight from MTL semantics:
--   (ρ,m)⊨MTL α∧β iff (ρ,m)⊨MTL α and (ρ,m)⊨MTL β)
-- Both α and β evaluated at SAME time point m, but each has own time window.
--
-- Question: What should StepResult return for remaining time?

module TimeSemantics where

open import Data.Nat using (ℕ; _∸_; _≤ᵇ_; _⊓_)
open import Data.Bool using (Bool; true; false; if_then_else_)

-- ============================================================================
-- MODEL 1: Single remaining time in StepResult
-- ============================================================================

data StepResult1 (S : Set) : Set where
  Continue : ℕ → S → StepResult1 S  -- single remaining time
  Violated : StepResult1 S
  Satisfied : StepResult1 S

-- Example: And (EventuallyWithin 1000 φ) (EventuallyWithin 500 ψ)
-- Left returns: Continue 1000 st1'
-- Right returns: Continue 500 st2'
-- And returns: Continue ??? (AndState st1' st2')
--
-- Options:
--   A) Continue 500 (...) -- min, tightest constraint
--   B) Continue 0 (...)   -- unbounded, children have own times
--   C) Continue 1000 (...) -- max, loosest constraint
--
-- Problem: None of these capture that left has 1000 and right has 500!
-- The And itself doesn't have "a" time - its children do.

-- ============================================================================
-- MODEL 2: Time lives in state, not in StepResult
-- ============================================================================

data StepResult2 (S : Set) : Set where
  Continue : S → StepResult2 S  -- state carries its own time info
  Violated : StepResult2 S
  Satisfied : StepResult2 S

data State2 : Set where
  AtomicState : State2
  AndState : State2 → State2 → State2
  EventuallyWithinState : ℕ → State2 → State2  -- remaining time in state

-- Example: And (EventuallyWithin 1000 φ) (EventuallyWithin 500 ψ)
-- States: AndState (EventuallyWithinState 1000 st1) (EventuallyWithinState 500 st2)
-- Each child knows its own remaining time!
--
-- Advantage: Time is distributed, as in MTL semantics
-- Disadvantage: How do we use this for bisimilarity proof?
--               We wanted remaining time as OBSERVABLE in StepResult

-- ============================================================================
-- MODEL 3: Remaining time = 0 for unbounded, actual for bounded
-- ============================================================================

-- Key insight: "Remaining time" answers "when does THIS formula time out?"
--
-- EventuallyWithin 1000 φ: times out in 1000 microseconds → return 1000
-- And φ ψ: never times out (unbounded) → return 0
-- Or φ ψ: never times out (unbounded) → return 0
--
-- For And (EventuallyWithin 1000 φ) (EventuallyWithin 500 ψ):
--   Left: Continue 1000 st1'  (EventuallyWithin times out in 1000)
--   Right: Continue 500 st2'  (EventuallyWithin times out in 500)
--   And: Continue 0 (AndState st1' st2')  (And itself never times out)
--
-- The time constraints live in the CHILDREN, not the parent.

data StepResult3 (S : Set) : Set where
  Continue : ℕ → S → StepResult3 S  -- 0 = unbounded
  Violated : StepResult3 S
  Satisfied : StepResult3 S

-- Semantics:
--   0 = this formula has no time bound (infinite time)
--   n > 0 = this formula will time out in n microseconds

-- ============================================================================
-- EXPERIMENT: Time expiration for compound operators
-- ============================================================================

-- Question: When does an And violate due to timeout?
--
-- Example: And (EventuallyWithin 1000 φ) ψ at time t=0
--   - At t=500: left has 500 remaining, right is unbounded
--   - At t=1000: left times out
--   - If φ hasn't held yet, left returns Violated
--   - And must return Violated (left violated)
--
-- So: Time expiration is handled BY THE BOUNDED OPERATOR ITSELF
--     The And just propagates the violation
--     The And doesn't need to track time - its children do!

-- Question: What should And return as remaining time for bisimilarity?
--
-- For bisimilarity proof, we need to compare:
--   - Monitor state: AndState (EventuallyWithinState start1 st1) (EventuallyWithinState start2 st2)
--   - Coalgebra state: And (EventuallyWithinProc window1 start1 φ) (EventuallyWithinProc window2 start2 ψ)
--
-- The Relate relation should match states pairwise:
--   Relate (AndState st1 st2) (AndProc φ ψ) when
--     Relate st1 φ and Relate st2 ψ
--
-- The remaining time for each EventuallyWithin is tracked in ITS OWN state!
-- The And doesn't aggregate it - it just combines children.

-- ============================================================================
-- CONCLUSION
-- ============================================================================

-- Model 3 is correct:
--   - Bounded operators (EventuallyWithin, AlwaysWithin, UntilWithin) return actual remaining
--   - Unbounded operators (And, Or, Not, Always, Eventually, Until, Next) return 0
--   - Compound operators don't "combine" times - children track their own
--   - Time expiration handled by bounded operators themselves
--   - And/Or just propagate violations from children
--
-- For bisimilarity proof:
--   - Relate matches states pairwise (compositionally)
--   - Each bounded operator's remaining time is observable in its own state
--   - Compound operators don't need remaining time - they're unbounded
--
-- This matches the MTL formal semantics where α and β each know their own windows!
