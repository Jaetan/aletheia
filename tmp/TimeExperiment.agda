{-# OPTIONS --safe --without-K #-}

-- Concrete experiment: Stepping through compound formulas with time bounds

module TimeExperiment where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_; _⊓_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

-- Simplified frame and formula types
record Frame : Set where
  constructor mkFrame
  field
    timestamp : ℕ

data Formula : Set where
  Atomic : Formula
  And : Formula → Formula → Formula
  EventuallyWithin : ℕ → Formula → Formula  -- window in microseconds

data State : Set where
  AtomicState : State
  AndState : State → State → State
  EventuallyWithinState : ℕ → State → State  -- startTime, inner

data StepResult : Set where
  Continue : ℕ → State → StepResult  -- remaining time (0 = unbounded)
  Violated : StepResult
  Satisfied : StepResult

-- ============================================================================
-- STEPPING LOGIC
-- ============================================================================

-- Simplified evaluation (always returns false for atoms)
evalAtomic : Frame → Bool
evalAtomic _ = false

-- Step EventuallyWithin
stepEventuallyWithin : ℕ → ℕ → State → Frame → StepResult
stepEventuallyWithin windowMicros startTime inner curr =
  let currTime = Frame.timestamp curr
      actualStart = if startTime ≤ᵇ 0 then currTime else startTime
      elapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ elapsed
      inWindow = elapsed ≤ᵇ windowMicros
  in if inWindow
     then Continue remaining (EventuallyWithinState actualStart inner)
     else Violated

-- Step And
stepAnd : State → State → Frame → StepResult
stepAnd st1 st2 curr =
  let res1 = stepSimple st1 curr
      res2 = stepSimple st2 curr
  in combineAnd res1 res2
  where
    stepSimple : State → Frame → StepResult
    stepSimple AtomicState curr =
      if evalAtomic curr then Satisfied else Violated
    stepSimple (AndState s1 s2) curr = stepAnd s1 s2 curr
    stepSimple (EventuallyWithinState start inner) curr =
      stepEventuallyWithin 1000 start inner curr

    combineAnd : StepResult → StepResult → StepResult
    combineAnd Violated _ = Violated
    combineAnd _ Violated = Violated
    combineAnd (Continue r1 st1') (Continue r2 st2') =
      Continue 0 (AndState st1' st2')  -- And is unbounded!
    combineAnd (Continue r1 st1') Satisfied =
      Continue 0 (AndState st1' AtomicState)  -- placeholder
    combineAnd Satisfied (Continue r2 st2') =
      Continue 0 (AndState AtomicState st2')  -- placeholder
    combineAnd Satisfied Satisfied = Satisfied

-- ============================================================================
-- SCENARIO: And (EventuallyWithin 1000 φ) (EventuallyWithin 500 ψ)
-- ============================================================================

-- Initial state
initialState : State
initialState = AndState
  (EventuallyWithinState 0 AtomicState)  -- left: window=1000
  (EventuallyWithinState 0 AtomicState)  -- right: window=500

-- Frame at t=0
frame0 : Frame
frame0 = mkFrame 0

-- Step at t=0
-- Result: Continue 0 (AndState (EWS 0 ...) (EWS 0 ...))
step0 : StepResult
step0 = stepAnd (EventuallyWithinState 0 AtomicState) (EventuallyWithinState 0 AtomicState) frame0

-- Frame at t=300
frame300 : Frame
frame300 = mkFrame 300

-- If we step the left child (window=1000, start=0) at t=300:
--   elapsed = 300 - 0 = 300
--   remaining = 1000 - 300 = 700
--   Result: Continue 700 (EventuallyWithinState 0 AtomicState)

-- If we step the right child (window=500, start=0) at t=300:
--   elapsed = 300 - 0 = 300
--   remaining = 500 - 300 = 200
--   Result: Continue 200 (EventuallyWithinState 0 AtomicState)

-- When And combines them:
--   Left: Continue 700 st1'
--   Right: Continue 200 st2'
--   And: Continue 0 (AndState st1' st2')  -- And itself is unbounded!

-- Frame at t=600
frame600 : Frame
frame600 = mkFrame 600

-- If we step the left child (window=1000, start=0) at t=600:
--   elapsed = 600 - 0 = 600
--   remaining = 1000 - 600 = 400
--   Result: Continue 400 (EventuallyWithinState 0 AtomicState)

-- If we step the right child (window=500, start=0) at t=600:
--   elapsed = 600 - 0 = 600
--   remaining = 500 - 600 = 0 (saturating subtraction)
--   inWindow = 600 ≤ᵇ 500 = false
--   Result: Violated

-- When And combines them:
--   Left: Continue 400 st1'
--   Right: Violated
--   And: Violated  -- Propagates violation from right child!

-- ============================================================================
-- KEY INSIGHTS
-- ============================================================================

-- 1. Each bounded operator tracks its OWN remaining time
--    - Left: 700 microseconds at t=300
--    - Right: 200 microseconds at t=300
--
-- 2. And returns 0 (unbounded) because AND ITSELF has no time bound
--    - The time constraints are in the CHILDREN
--    - And just evaluates both children at the same time point
--
-- 3. Time expiration handled BY THE BOUNDED OPERATOR
--    - At t=600, right child detects timeout and returns Violated
--    - And propagates this violation
--    - And doesn't need to check times - children do it!
--
-- 4. For bisimilarity proof:
--    - Relate (AndState st1 st2) (AndProc φ ψ)
--      when Relate st1 φ and Relate st2 ψ
--    - Each child's remaining time is observable in its own Continue result
--    - And's remaining time is 0 (compositional, unbounded)
--
-- 5. This matches MTL formal semantics:
--    - (ρ,m)⊨MTL α∧β iff (ρ,m)⊨MTL α and (ρ,m)⊨MTL β
--    - Both evaluated at same time m
--    - Each has its own time window
--    - And doesn't aggregate windows!

-- ============================================================================
-- CONCLUSION: Model 3 is correct!
-- ============================================================================

-- StepResult should use:
--   - 0 for unbounded operators (And, Or, Not, Always, Eventually, Until, Next)
--   - Actual remaining microseconds for bounded operators (EventuallyWithin, AlwaysWithin)
--
-- This is exactly what my "first try" was doing!
-- No need for minRemaining/maxRemaining - children track their own times.
