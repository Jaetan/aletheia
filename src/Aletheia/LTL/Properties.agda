{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Correctness properties for LTL evaluation (Phase 3 Goal #2).
--
-- Purpose: Prove LTL evaluator correctness for streaming protocol verification.
-- Properties: Coinductive equivalence between streaming stepEval and formal checkColist semantics.
-- Approach: Prove stepEval ≡ checkColist (streaming state machine matches infinite-trace LTL).
--
-- PROOF STRATEGY (Direct Coinductive Correctness):
--
-- Aletheia has TWO evaluation implementations:
--   1. stepEval (LTLEvalState → Frame → StepResult) - Streaming, O(1) memory, PRODUCTION
--   2. checkColist (Colist Frame → Delay Bool) - Coinductive, infinite streams, FORMAL SEMANTICS
--
-- This module proves: stepEval ≡ checkColist
--   - Defines foldStepEval: lifts stepEval to work on colists
--   - Proves equivalence: foldStepEval φ trace ≡ checkColist φ trace
--   - Uses coinductive reasoning, sized types, productivity checking
--
-- Why this approach?
--   - Production ONLY uses stepEval (streaming state machine)
--   - checkColist defines true LTL semantics (infinite traces)
--   - Avoids finite/streaming semantic mismatches
--   - Direct proof: show production implementation matches mathematical definition
--
-- Previous approach (DISCARDED):
--   - Proved checkIncremental (finite traces) was correct
--   - Attempted stepEval ≡ checkIncremental equivalence
--   - Blocked by semantic mismatch (Continue case on finite traces)
--   - checkIncremental never used in production → removed as dead code
--
-- See: /home/nicolas/.claude/plans/synthetic-honking-goblet.md for full rationale
--
-- Current status: Cleanup phase complete, ready for coinductive infrastructure
-- Next: Define foldStepEval, prove Atomic case, then propositional operators

module Aletheia.LTL.Properties where

-- Standard library imports
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- Aletheia imports
open import Aletheia.LTL.Syntax
open import Aletheia.LTL.Incremental
open import Aletheia.LTL.Coinductive using (checkColist)
open import Aletheia.Trace.Context using (TimedFrame)

-- ============================================================================
-- PHASE 2: COINDUCTIVE INFRASTRUCTURE
-- ============================================================================

-- Evaluator for atomic predicates in LTL (TimedFrame → Bool)
-- The predicate itself doesn't use previous frame, but stepEval's signature requires it
evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → Bool) → Bool
evalAtomicPred _ curr p = p curr

-- Fold stepEval over a colist to get coinductive result
-- This bridges stepEval (frame-by-frame) and checkColist (whole colist)
foldStepEval : ∀ {i : Size}
             → LTL (TimedFrame → Bool)
             → Colist TimedFrame i
             → Delay Bool i

-- Empty trace: vacuously true
foldStepEval φ [] = now true

-- Non-empty trace: process frames iteratively
foldStepEval φ (f ∷ rest) = later λ where .force → go φ (initState φ) nothing f (rest .force)
  where
    -- Helper: threads state and previous frame through colist
    go : ∀ {i : Size}
       → LTL (TimedFrame → Bool)     -- Original formula (for stepEval)
       → LTLEvalState                -- Current evaluation state
       → Maybe TimedFrame             -- Previous frame
       → TimedFrame                   -- Current frame
       → Colist TimedFrame i          -- Remaining frames
       → Delay Bool i

    -- Process current frame with stepEval
    go φ st prev curr rest with stepEval φ evalAtomicPred st prev curr

    -- Continue: process next frame (or finish if no more frames)
    ... | Continue st' with rest
    ...   | [] = now true  -- No more frames, default to true (finite prefix semantics)
    ...   | (next ∷ rest') = later λ where .force → go φ st' (just curr) next (rest' .force)

    -- Violated: property failed
    go φ st prev curr rest | Violated _ = now false

    -- Satisfied: property succeeded
    go φ st prev curr rest | Satisfied = now true

-- ============================================================================
-- PHASE 3: ATOMIC CASE EQUIVALENCE
-- ============================================================================

-- Prove Atomic predicates are equivalent between foldStepEval and checkColist
-- After fixing checkColist to evaluate at first frame (not last), this is straightforward
atomic-fold-equiv : ∀ {i : Size} (p : TimedFrame → Bool) (trace : Colist TimedFrame i)
  → foldStepEval (Atomic p) trace ≡ checkColist (Atomic p) trace

-- Empty trace: both return 'now true'
atomic-fold-equiv p [] = refl

-- Non-empty trace: both evaluate predicate at first frame
atomic-fold-equiv p (f ∷ rest) with p f
... | true  = refl  -- Both return 'now true'
... | false = refl  -- Both return 'now false'

-- ============================================================================
-- PHASE 4: PROPOSITIONAL OPERATORS (TODO)
-- ============================================================================

-- TODO: Prove Not, And, Or equivalence using structural induction

-- ============================================================================
-- PHASE 5: TEMPORAL OPERATORS (TODO - RESEARCH FIRST)
-- ============================================================================

-- ⚠️ PAUSE before implementation: Research coinductive LTL proofs
-- TODO: Always, Eventually, Until, Next
-- TODO: EventuallyWithin, AlwaysWithin

-- ============================================================================
-- PHASE 6: GLOBAL EQUIVALENCE THEOREM (TODO)
-- ============================================================================

-- TODO: Main theorem combining all cases
-- postulate
--   stepEval-coinductive-equiv : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame i)
--     → foldStepEval φ trace ≡ checkColist φ trace

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================

-- Phase 1 (COMPLETE): Cleanup
--   - Removed checkIncremental and all finite-trace proofs (~1100 lines)
--   - Removed extractResult, runStepEval, simpleEval helpers
--   - Updated module header to reflect coinductive strategy
--
-- Phase 2 (IN PROGRESS): Infrastructure
--   ✅ Resolved --safe vs sized-types (removed --safe, added --sized-types)
--   ✅ Imported coinductive infrastructure (Colist, Delay, Size)
--   ✅ Defined evalAtomicPred helper
--   ✅ Defined foldStepEval : LTL (TimedFrame → Bool) → Colist TimedFrame → Delay Bool
--   ⏸️ Type-checking in progress
--
-- Phase 3-4 (NEXT): Easy cases
--   - Atomic: Never returns Continue, simple proof
--   - Propositional: Not, And, Or using structural induction
--
-- Phase 5 (RESEARCH REQUIRED): Temporal operators
--   - Always: Productivity proof (infinite checking)
--   - Eventually: Termination/productivity
--   - Until: Complex state correspondence
--   - Requires: literature review, sized types expertise
--
-- Phase 6 (INTEGRATION): Global theorem
--   - Combine all operator proofs
--   - Pattern match on formula structure
