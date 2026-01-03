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
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; EventuallyWithin; AlwaysWithin)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; mkCounterexample)
open import Aletheia.Trace.Context using (TimedFrame; timestamp)
open import Data.Nat using (_∸_; _≤ᵇ_; _≡ᵇ_)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- LTLPROC: Defunctionalized LTL process
-- ============================================================================

-- LTLProc is simply the LTL formula paired with any needed runtime state.
--
-- Design philosophy:
-- - The formula tells us HOW to react to the next frame
-- - We pattern match on formula structure to define step behavior
-- - No coinductive types needed here - coinduction happens at bisimilarity level!
--
-- For now, LTLProc = LTL formula itself.
-- We may need to add state for operators like EventuallyWithin (startTime tracking).

LTLProc : Set
LTLProc = LTL (TimedFrame → Bool)

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
... | Continue φ' = Continue (Not φ')
... | Violated _ = Satisfied  -- Inner violated means outer satisfied
... | Satisfied = Violated (mkCounterexample curr "negation failed (inner satisfied)")

-- And: both must hold
stepL (And φ ψ) prev curr
  with stepL φ prev curr | stepL ψ prev curr
... | Violated ce | _ = Violated ce  -- Left failed
... | Continue φ' | Violated ce = Violated ce  -- Right failed
... | Continue φ' | Continue ψ' = Continue (And φ' ψ')  -- Both continue
... | Continue φ' | Satisfied = Continue (And φ' ψ)  -- Right satisfied, keep checking left
... | Satisfied | Violated ce = Violated ce  -- Right failed
... | Satisfied | Continue ψ' = Continue (And φ ψ')  -- Left satisfied, keep checking right
... | Satisfied | Satisfied = Satisfied  -- Both satisfied

-- Or: either must hold
stepL (Or φ ψ) prev curr
  with stepL φ prev curr | stepL ψ prev curr
... | Satisfied | _ = Satisfied  -- Left satisfied
... | Continue φ' | Satisfied = Satisfied  -- Right satisfied
... | Continue φ' | Continue ψ' = Continue (Or φ' ψ')  -- Both continue
... | Continue φ' | Violated _ = Continue (Or φ' ψ)  -- Right violated, keep checking left
... | Violated _ | Satisfied = Satisfied  -- Right satisfied
... | Violated _ | Continue ψ' = Continue (Or φ ψ')  -- Left violated, keep checking right
... | Violated _ | Violated ce = Violated ce  -- Both violated

-- Next: skip first frame, then check inner formula
-- This is where we need state! "Have we skipped yet?"
-- For now, simplified: Always returns Continue (Next φ) on first call
-- TODO: This needs refinement - maybe LTLProc needs to track "mode" for Next
stepL (Next φ) prev curr = Continue (Next φ)  -- Simplified for now

-- Always: must hold on every frame
-- This is the key operator! Check φ now, continue checking Always φ forever.
stepL (Always φ) prev curr
  with stepL φ prev curr
... | Violated ce = Violated ce  -- φ failed at this frame
... | Satisfied = Continue (Always φ)  -- φ holds, keep checking on future frames
... | Continue φ' = Continue (Always φ')  -- φ continues, keep checking

-- Eventually: must hold at some point
stepL (Eventually φ) prev curr
  with stepL φ prev curr
... | Satisfied = Satisfied  -- Found it!
... | Violated _ = Continue (Eventually φ)  -- Not yet, keep looking
... | Continue φ' = Continue (Eventually φ')  -- Still checking inner

-- Until: φ holds until ψ
-- Until: φ must hold until ψ becomes true
-- Refactored to use flat with-clauses (easier to prove bisimilarity)
stepL (Until φ ψ) prev curr
  with stepL ψ prev curr | stepL φ prev curr
-- ψ satisfied → Until satisfied (φ result doesn't matter)
... | Satisfied | _ = Satisfied
-- ψ continues, φ violated → Until violated
... | Continue ψ' | Violated ce = Violated ce
-- ψ continues, φ continues → Until continues
... | Continue ψ' | Continue φ' = Continue (Until φ' ψ')
-- ψ continues, φ satisfied → Until continues (preserve original φ formula)
... | Continue ψ' | Satisfied = Continue (Until φ ψ')
-- ψ violated, φ violated → Until violated
... | Violated _ | Violated ce = Violated ce
-- ψ violated, φ continues → Until continues (preserve original ψ formula)
... | Violated _ | Continue φ' = Continue (Until φ' ψ)
-- ψ violated, φ satisfied → Until continues (preserve both)
... | Violated _ | Satisfied = Continue (Until φ ψ)

-- Bounded operators: Need to track start time!
-- This reveals a limitation: LTLProc needs state for these operators.
-- For now, simplified versions:
stepL (EventuallyWithin n φ) prev curr = Continue (EventuallyWithin n φ)  -- TODO: track time
stepL (AlwaysWithin n φ) prev curr = Continue (AlwaysWithin n φ)  -- TODO: track time

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
-- 3. Some operators need state (Next, EventuallyWithin, AlwaysWithin)
--    - Next needs "have we skipped yet?" flag
--    - EventuallyWithin/AlwaysWithin need startTime
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
-- 2. Handle EventuallyWithin/AlwaysWithin (need startTime state)
-- 3. Prove bisimilarity with monitor (starting with Always φ where φ = Atomic p)
-- 4. Extend to other operators

-- For now, this gives us the core structure for Always, which is the base case!
