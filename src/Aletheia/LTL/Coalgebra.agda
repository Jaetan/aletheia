{-# OPTIONS --safe --without-K #-}

-- Defunctionalized LTL coalgebra
--
-- Purpose: Define LTL semantics as "how it reacts to frames",
-- not "what it means". This is the defunctionalization trick that
-- avoids extended lambdas entirely!
--
-- Key insight: We don't define ⟦ φ ⟧ : Stream Frame → Set (semantic predicate).
-- Instead, we define stepL : LTLProc → Frame → StepResult LTLProc (operational reaction).
--
-- For Always φ:
-- - stepL checks φ on current frame
-- - Either fails immediately, or
-- - Returns continuation that is again Always φ
--
-- This is observationally identical to the monitor, provable via coalgebraic bisimilarity!

module Aletheia.LTL.Coalgebra where

open import Aletheia.Prelude
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; mkCounterexample)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)
open import Data.Nat using (_∸_; _≤ᵇ_; _≡ᵇ_)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- LTLPROC: Defunctionalized LTL process with runtime state
-- ============================================================================

-- LTLProc is the LTL formula enriched with runtime state for operators that need it.
--
-- Design philosophy:
-- - The formula tells us HOW to react to the next frame
-- - We pattern match on formula structure to define step behavior
-- - No coinductive types needed here - coinduction happens at bisimilarity level!
--
-- Runtime state examples:
-- - Next: modal state (NextWaiting vs NextActive) to track if we've skipped first frame
-- - MetricEventually/MetricAlways: startTime tracking (TODO: Phase 3)
--
-- This is a proper data type (not type alias) to support modal constructors for Next.

data LTLProc : Set where
  -- Propositional operators (stateless)
  Atomic : (TimedFrame → Bool) → LTLProc
  Not : LTLProc → LTLProc
  And : LTLProc → LTLProc → LTLProc
  Or : LTLProc → LTLProc → LTLProc

  -- Next with modal state (two constructors for waiting vs active)
  NextWaiting : LTLProc → LTLProc  -- Waiting to skip first frame
  NextActive : LTLProc → LTLProc   -- Evaluating inner formula after skip

  -- Temporal operators (stateless)
  Always : LTLProc → LTLProc
  Eventually : LTLProc → LTLProc
  Until : LTLProc → LTLProc → LTLProc
  Release : LTLProc → LTLProc → LTLProc  -- Dual of Until: ψ holds until φ releases it

  -- Bounded temporal operators (with time tracking)
  MetricEventuallyProc : ℕ → ℕ → LTLProc → LTLProc  -- windowMicros, startTime, inner
  MetricAlwaysProc : ℕ → ℕ → LTLProc → LTLProc      -- windowMicros, startTime, inner
  MetricUntilProc : ℕ → ℕ → LTLProc → LTLProc → LTLProc      -- windowMicros, startTime, φ, ψ
  MetricReleaseProc : ℕ → ℕ → LTLProc → LTLProc → LTLProc    -- windowMicros, startTime, φ, ψ

-- ============================================================================
-- CONVERSION: LTLProc → LTL (for monitor interop)
-- ============================================================================

-- Convert LTLProc back to LTL formula for use with monitor
-- This extracts the static formula from the runtime state.
--
-- Key insight: NextWaitingProc and NextActiveProc both convert to Next φ
-- because they represent different runtime states of the same formula.
toLTL : LTLProc → LTL (TimedFrame → Bool)
toLTL (Atomic p) = Atomic p
toLTL (Not φ) = Not (toLTL φ)
toLTL (And φ ψ) = And (toLTL φ) (toLTL ψ)
toLTL (Or φ ψ) = Or (toLTL φ) (toLTL ψ)
toLTL (NextWaiting φ) = Next (toLTL φ)   -- Waiting mode → Next formula
toLTL (NextActive φ) = Next (toLTL φ)    -- Active mode → Next formula
toLTL (Always φ) = Always (toLTL φ)
toLTL (Eventually φ) = Eventually (toLTL φ)
toLTL (Until φ ψ) = Until (toLTL φ) (toLTL ψ)
toLTL (Release φ ψ) = Release (toLTL φ) (toLTL ψ)
toLTL (MetricEventuallyProc window _ φ) = MetricEventually window (toLTL φ)  -- Ignore startTime (runtime state)
toLTL (MetricAlwaysProc window _ φ) = MetricAlways window (toLTL φ)          -- Ignore startTime (runtime state)
toLTL (MetricUntilProc window _ φ ψ) = MetricUntil window (toLTL φ) (toLTL ψ)      -- Ignore startTime
toLTL (MetricReleaseProc window _ φ ψ) = MetricRelease window (toLTL φ) (toLTL ψ)  -- Ignore startTime

-- ============================================================================
-- OBSERVABLE-LEVEL HANDLERS FOR BOUNDED OPERATORS
-- ============================================================================

-- These handlers work purely at the observable StepResult level.
-- They only pattern match on StepResult observations, not on formula structure.
-- The formulas (φ, ψ) are used ONLY to reconstruct continuations, not for branching logic.

-- MetricEventually handler: Continues until inner formula satisfied or window expires
metricEventuallyHandler : ℕ → ℕ → LTLProc → StepResult LTLProc → ℕ → ℕ → StepResult LTLProc
metricEventuallyHandler windowMicros start φ Satisfied _ _ = Satisfied
metricEventuallyHandler windowMicros start φ (Continue _ φ') _ remaining =
  Continue remaining (MetricEventuallyProc windowMicros start φ')
metricEventuallyHandler windowMicros start φ (Violated _) _ remaining =
  Continue remaining (MetricEventuallyProc windowMicros start φ)  -- Keep looking

-- MetricAlways handler: Continues while inner formula holds, fails if violated
metricAlwaysHandler : ℕ → ℕ → LTLProc → StepResult LTLProc → ℕ → ℕ → StepResult LTLProc
metricAlwaysHandler windowMicros start φ (Violated ce) _ _ = Violated ce
metricAlwaysHandler windowMicros start φ (Continue _ φ') _ remaining =
  Continue remaining (MetricAlwaysProc windowMicros start φ')
metricAlwaysHandler windowMicros start φ Satisfied _ remaining =
  Continue remaining (MetricAlwaysProc windowMicros start φ)  -- Keep checking

-- MetricUntil handler: φ must hold until ψ becomes true, within window
-- Observable logic: Branch ONLY on StepResult patterns (ψ then φ)
metricUntilHandler : ℕ → ℕ → LTLProc → LTLProc → StepResult LTLProc → StepResult LTLProc → ℕ → ℕ → StepResult LTLProc
-- ψ satisfied → MetricUntil satisfied
metricUntilHandler _ _ _ _ Satisfied _ _ _ = Satisfied
-- ψ continues, φ violated → MetricUntil violated
metricUntilHandler _ _ _ _ (Continue _ ψ') (Violated ce) _ _ = Violated ce
-- ψ continues, φ continues → MetricUntil continues
metricUntilHandler windowMicros start φ ψ (Continue _ ψ') (Continue _ φ') _ remaining =
  Continue remaining (MetricUntilProc windowMicros start φ' ψ')
-- ψ continues, φ satisfied → MetricUntil continues (preserve original φ)
metricUntilHandler windowMicros start φ ψ (Continue _ ψ') Satisfied _ remaining =
  Continue remaining (MetricUntilProc windowMicros start φ ψ')
-- ψ violated, φ violated → MetricUntil violated
metricUntilHandler _ _ _ _ (Violated _) (Violated ce) _ _ = Violated ce
-- ψ violated, φ continues → MetricUntil continues (preserve original ψ)
metricUntilHandler windowMicros start φ ψ (Violated _) (Continue _ φ') _ remaining =
  Continue remaining (MetricUntilProc windowMicros start φ' ψ)
-- ψ violated, φ satisfied → MetricUntil continues (preserve both)
metricUntilHandler windowMicros start φ ψ (Violated _) Satisfied _ remaining =
  Continue remaining (MetricUntilProc windowMicros start φ ψ)

-- MetricRelease handler: ψ must hold until φ releases it, within window
-- Observable logic: Branch ONLY on StepResult patterns (φ then ψ)
metricReleaseHandler : ℕ → ℕ → LTLProc → LTLProc → StepResult LTLProc → StepResult LTLProc → ℕ → ℕ → StepResult LTLProc
-- φ satisfied → MetricRelease satisfied (release condition met)
metricReleaseHandler _ _ _ _ Satisfied _ _ _ = Satisfied
-- φ continues, ψ violated → MetricRelease violated (ψ must hold until release)
metricReleaseHandler _ _ _ _ (Continue _ φ') (Violated ce) _ _ = Violated ce
-- φ continues, ψ continues → MetricRelease continues
metricReleaseHandler windowMicros start φ ψ (Continue _ φ') (Continue _ ψ') _ remaining =
  Continue remaining (MetricReleaseProc windowMicros start φ' ψ')
-- φ continues, ψ satisfied → MetricRelease continues (preserve original ψ)
metricReleaseHandler windowMicros start φ ψ (Continue _ φ') Satisfied _ remaining =
  Continue remaining (MetricReleaseProc windowMicros start φ' ψ)
-- φ violated, ψ violated → MetricRelease violated
metricReleaseHandler _ _ _ _ (Violated _) (Violated ce) _ _ = Violated ce
-- φ violated, ψ continues → MetricRelease continues (preserve original φ)
metricReleaseHandler windowMicros start φ ψ (Violated _) (Continue _ ψ') _ remaining =
  Continue remaining (MetricReleaseProc windowMicros start φ ψ')
-- φ violated, ψ satisfied → MetricRelease continues (preserve both)
metricReleaseHandler windowMicros start φ ψ (Violated _) Satisfied _ remaining =
  Continue remaining (MetricReleaseProc windowMicros start φ ψ)

-- ============================================================================
-- DEFUNCTIONALIZED STEP SEMANTICS
-- ============================================================================

-- How LTL reacts to one frame.
--
-- This is NOT extracting from Delay Bool!
-- This is defining step-based operational semantics directly.
--
-- Key principle: Pattern match on formula, define what happens at this frame.

stepL : LTLProc → Maybe TimedFrame → TimedFrame → StepResult LTLProc

-- Atomic: evaluate predicate at current frame
-- Returns Satisfied (like the monitor does for atomic predicates)
stepL (Atomic p) prev curr =
  if p curr
  then Satisfied
  else Violated (mkCounterexample curr "atomic predicate failed")

-- Not: invert inner result
stepL (Not φ) prev curr
  with stepL φ prev curr
... | Continue _ φ' = Continue 0 (Not φ')
... | Violated _ = Satisfied  -- Inner violated means outer satisfied
... | Satisfied = Violated (mkCounterexample curr "negation failed (inner satisfied)")

-- And: both must hold
stepL (And φ ψ) prev curr
  with stepL φ prev curr | stepL ψ prev curr
... | Violated ce | _ = Violated ce  -- Left failed
... | Continue _ φ' | Violated ce = Violated ce  -- Right failed
... | Continue _ φ' | Continue _ ψ' = Continue 0 (And φ' ψ')  -- Both continue, And is unbounded
... | Continue _ φ' | Satisfied = Continue 0 (And φ' ψ)  -- Right satisfied, keep checking left
... | Satisfied | Violated ce = Violated ce  -- Right failed
... | Satisfied | Continue _ ψ' = Continue 0 (And φ ψ')  -- Left satisfied, keep checking right
... | Satisfied | Satisfied = Satisfied  -- Both satisfied

-- Or: either must hold
stepL (Or φ ψ) prev curr
  with stepL φ prev curr | stepL ψ prev curr
... | Satisfied | _ = Satisfied  -- Left satisfied
... | Continue _ φ' | Satisfied = Satisfied  -- Right satisfied
... | Continue _ φ' | Continue _ ψ' = Continue 0 (Or φ' ψ')  -- Both continue, Or is unbounded
... | Continue _ φ' | Violated _ = Continue 0 (Or φ' ψ)  -- Right violated, keep checking left
... | Violated _ | Satisfied = Satisfied  -- Right satisfied
... | Violated _ | Continue _ ψ' = Continue 0 (Or φ ψ')  -- Left violated, keep checking right
... | Violated _ | Violated ce = Violated ce  -- Both violated

-- Next: skip first frame, then check inner formula
-- Modal state tracks whether we've skipped the first frame yet

-- Waiting mode: Skip current frame without evaluating, transition to Active
stepL (NextWaiting φ) prev curr = Continue 0 (NextActive φ)

-- Active mode: Evaluate inner formula (after skip)
stepL (NextActive φ) prev curr
  with stepL φ prev curr
... | Continue _ φ' = Continue 0 (NextActive φ')  -- Inner continues, stay active
... | Violated ce = Violated ce               -- Inner violated
... | Satisfied = Satisfied                   -- Inner satisfied

-- Always: must hold on every frame
-- This is the key operator! Check φ now, continue checking Always φ forever.
stepL (Always φ) prev curr
  with stepL φ prev curr
... | Violated ce = Violated ce  -- φ failed at this frame
... | Satisfied = Continue 0 (Always φ)  -- φ holds, keep checking on future frames
... | Continue _ φ' = Continue 0 (Always φ')  -- φ continues, keep checking

-- Eventually: must hold at some point
stepL (Eventually φ) prev curr
  with stepL φ prev curr
... | Satisfied = Satisfied  -- Found it!
... | Violated _ = Continue 0 (Eventually φ)  -- Not yet, keep looking
... | Continue _ φ' = Continue 0 (Eventually φ')  -- Still checking inner

-- Until: φ holds until ψ
-- Until: φ must hold until ψ becomes true
-- Refactored to use flat with-clauses (easier to prove bisimilarity)
stepL (Until φ ψ) prev curr
  with stepL ψ prev curr | stepL φ prev curr
-- ψ satisfied → Until satisfied (φ result doesn't matter)
... | Satisfied | _ = Satisfied
-- ψ continues, φ violated → Until violated
... | Continue _ ψ' | Violated ce = Violated ce
-- ψ continues, φ continues → Until continues
... | Continue _ ψ' | Continue _ φ' = Continue 0 (Until φ' ψ')
-- ψ continues, φ satisfied → Until continues (preserve original φ formula)
... | Continue _ ψ' | Satisfied = Continue 0 (Until φ ψ')
-- ψ violated, φ violated → Until violated
... | Violated _ | Violated ce = Violated ce
-- ψ violated, φ continues → Until continues (preserve original ψ formula)
... | Violated _ | Continue _ φ' = Continue 0 (Until φ' ψ)
-- ψ violated, φ satisfied → Until continues (preserve both)
... | Violated _ | Satisfied = Continue 0 (Until φ ψ)

-- Release: ψ holds until φ releases it (dual of Until)
-- φ Release ψ: ψ must hold until φ becomes true (or forever)
stepL (Release φ ψ) prev curr
  with stepL φ prev curr | stepL ψ prev curr
-- φ satisfied → Release satisfied (release condition met)
... | Satisfied | _ = Satisfied
-- φ continues, ψ violated → Release violated (ψ must hold until release)
... | Continue _ φ' | Violated ce = Violated ce
-- φ continues, ψ continues → Release continues
... | Continue _ φ' | Continue _ ψ' = Continue 0 (Release φ' ψ')
-- φ continues, ψ satisfied → Release continues (preserve original ψ)
... | Continue _ φ' | Satisfied = Continue 0 (Release φ' ψ)
-- φ violated, ψ violated → Release violated
... | Violated _ | Violated ce = Violated ce
-- φ violated, ψ continues → Release continues (preserve original φ)
... | Violated _ | Continue _ ψ' = Continue 0 (Release φ ψ')
-- φ violated, ψ satisfied → Release continues (preserve both)
... | Violated _ | Satisfied = Continue 0 (Release φ ψ)

-- MetricEventually: must hold within time window
stepL (MetricEventuallyProc windowMicros startTime φ) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed  -- OBSERVABLE remaining time
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricEventuallyHandler windowMicros actualStart φ (stepL φ prev curr) actualStart remaining
     else Violated (mkCounterexample curr "MetricEventually: window expired")

-- MetricAlways: must hold throughout time window
stepL (MetricAlwaysProc windowMicros startTime φ) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed  -- OBSERVABLE remaining time
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricAlwaysHandler windowMicros actualStart φ (stepL φ prev curr) actualStart remaining
     else Satisfied  -- Window complete, always held

-- MetricUntil: φ holds until ψ, within time window
stepL (MetricUntilProc windowMicros startTime φ ψ) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed  -- OBSERVABLE remaining time
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricUntilHandler windowMicros actualStart φ ψ (stepL ψ prev curr) (stepL φ prev curr) actualStart remaining
     else Violated (mkCounterexample curr "MetricUntil: window expired before ψ")

-- MetricRelease: ψ holds until φ releases it, within time window
stepL (MetricReleaseProc windowMicros startTime φ ψ) prev curr =
  let currTime = timestamp curr
      actualStart = if startTime ≡ᵇ 0 then currTime else startTime
      actualElapsed = currTime ∸ actualStart
      remaining = windowMicros ∸ actualElapsed  -- OBSERVABLE remaining time
      inWindow = actualElapsed ≤ᵇ windowMicros
  in if inWindow
     then metricReleaseHandler windowMicros actualStart φ ψ (stepL φ prev curr) (stepL ψ prev curr) actualStart remaining
     else Satisfied  -- Window complete, ψ held throughout (release not required)

-- ============================================================================
-- OBSERVATIONS
-- ============================================================================

-- Key observations:
--
-- 1. Always φ:
--    - stepL checks φ at current frame
--    - Returns Continue (Always φ) if φ holds
--    - This is exactly what the monitor does!
--    - Provable via bisimilarity
--
-- 2. No extended lambdas!
--    - We pattern match on formula structure
--    - Define operational behavior directly
--    - No semantic predicates, no Delay Bool
--
-- 3. Some operators need state (Next, MetricEventually, MetricAlways)
--    - Next needs "have we skipped yet?" flag
--    - MetricEventually/MetricAlways need startTime
--    - This suggests LTLProc might need to be enriched with runtime state
--
-- 4. This is defunctionalization in action!
--    - Instead of ⟦ Always φ ⟧ = λ stream → ...
--    - We define stepL (Always φ) frame = ...
--    - The continuation is Always φ itself (or Always φ' if inner continues)

-- ============================================================================
-- NEXT STEPS
-- ============================================================================

-- TODO:
-- 1. Handle Next properly (need mode: Waiting vs Active)
-- 2. Handle MetricEventually/MetricAlways (need startTime state)
-- 3. Prove bisimilarity with monitor (starting with Always φ where φ = Atomic p)
-- 4. Extend to other operators

-- For now, this gives us the core structure for Always, which is the base case!
