{-# OPTIONS --safe --without-K --guardedness #-}

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

open import Aletheia.LTL.Syntax
open import Aletheia.LTL.Incremental
open import Aletheia.Trace.Context using (TimedFrame)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Note: Coinductive infrastructure imports will be added in Phase 2
-- Currently incompatible: Size (requires --sized-types, conflicts with --safe)
-- Will need to either: use guardedness only, or remove --safe flag for coinductive proofs

-- ============================================================================
-- PLACEHOLDER: Coinductive Equivalence Proofs
-- ============================================================================

-- TODO (Phase 2): Define foldStepEval - streaming fold over colist
-- TODO (Phase 3): Prove atomic-fold-equiv - Atomic case
-- TODO (Phase 4): Prove propositional operators - Not, And, Or
-- TODO (Phase 5): Prove temporal operators - Always, Eventually, Until, etc.
-- TODO (Phase 6): Global theorem - stepEval-coinductive-equiv

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================

-- Phase 1 (COMPLETE): Cleanup
--   - Removed checkIncremental and all finite-trace proofs (~1100 lines)
--   - Removed extractResult, runStepEval, simpleEval helpers
--   - Updated module header to reflect coinductive strategy
--
-- Phase 2 (NEXT): Infrastructure
--   - Define foldStepEval : LTL (TimedFrame → Bool) → Colist TimedFrame → Delay Bool
--   - Define StateInvariant : LTLEvalState → LTL → Colist → Set
--   - Set up coinductive proof framework
--
-- Phase 3-4 (PENDING): Easy cases
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
