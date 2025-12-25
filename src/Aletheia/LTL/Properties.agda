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
open import Codata.Sized.Delay.Bisimilarity as DelayBisim using (_⊢_≈_; Bisim)
import Codata.Sized.Delay.Bisimilarity as DB
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; inspect; [_])

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

-- Top-level helper: threads state and previous frame through colist
-- Extracted from where-clause to make it visible in proofs
foldStepEval-go : ∀ {i : Size}
                → LTL (TimedFrame → Bool)     -- Original formula (for stepEval)
                → LTLEvalState                -- Current evaluation state
                → Maybe TimedFrame             -- Previous frame
                → TimedFrame                   -- Current frame
                → Colist TimedFrame i          -- Remaining frames
                → Delay Bool i

-- Process current frame with stepEval
foldStepEval-go φ st prev curr rest with stepEval φ evalAtomicPred st prev curr

-- Continue: process next frame (or finish if no more frames)
... | Continue st' with rest
...   | [] = now true  -- No more frames, default to true (finite prefix semantics)
...   | (next ∷ rest') = later λ where .force → foldStepEval-go φ st' (just curr) next (rest' .force)

-- Violated: property failed
foldStepEval-go φ st prev curr rest | Violated _ = now false

-- Satisfied: property succeeded
foldStepEval-go φ st prev curr rest | Satisfied = now true

-- Fold stepEval over a colist to get coinductive result
-- This bridges stepEval (frame-by-frame) and checkColist (whole colist)
foldStepEval : ∀ {i : Size}
             → LTL (TimedFrame → Bool)
             → Colist TimedFrame i
             → Delay Bool i

-- Empty trace: vacuously true
foldStepEval φ [] = now true

-- Non-empty trace: delegate to helper
foldStepEval φ (f ∷ rest) = later λ where .force → foldStepEval-go φ (initState φ) nothing f (rest .force)

-- ============================================================================
-- PHASE 3: ATOMIC CASE EQUIVALENCE
-- ============================================================================

-- Prove Atomic predicates are bisimilar between foldStepEval and checkColist
-- Uses weak bisimilarity (∞ ⊢_≈_) instead of propositional equality
-- This is the standard approach for coinductive proofs
-- Note: We specialize to size ∞ to match the bisimilarity relation

-- Helper lemma: stepEval for Atomic computes based on predicate value
-- The definition of stepEval for Atomic is: if eval then Satisfied else Violated
-- So we can directly compute what it returns based on p f
stepEval-atomic-computes : ∀ (p : TimedFrame → Bool) (f : TimedFrame)
  → stepEval (Atomic p) evalAtomicPred AtomicState nothing f
    ≡ (if p f then Satisfied else Violated (mkCounterexample f "atomic predicate failed"))
stepEval-atomic-computes p f with p f
... | true  = refl
... | false = refl

-- Helper: prove what foldStepEval-go computes for Atomic
-- Since foldStepEval-go is top-level, Agda can reduce it!
-- This is the key that makes the proof work
atomic-go-equiv : ∀ (p : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Atomic p) AtomicState nothing f rest ≈ now (p f)

-- Pattern match on p f to make both sides reduce
atomic-go-equiv p f rest with p f
... | true  = DB.now refl  -- When p f = true: foldStepEval-go reduces to 'now true', checkColist to 'now true'
... | false = DB.now refl  -- When p f = false: foldStepEval-go reduces to 'now false', checkColist to 'now false'

-- With foldStepEval-go extracted to top-level, Agda can now reduce it in proofs!
atomic-fold-equiv : ∀ (p : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Atomic p) trace ≈ checkColist (Atomic p) trace

-- Empty case: both return 'now true'
atomic-fold-equiv p [] = DB.now refl

-- Non-empty case: use copattern matching to handle the 'later' constructor
atomic-fold-equiv p (f ∷ rest) = DB.later λ where .force → atomic-go-equiv p f (rest .force)

-- ============================================================================
-- PHASE 4: PROPOSITIONAL OPERATORS
-- ============================================================================

-- Strategy: Use induction on formula structure + coinductive reasoning for delays
-- Key insight: Propositional operators in stepEval may return Continue,
-- requiring us to follow the state machine through multiple frames

-- Import Delay utilities for reasoning about coinductive results
open import Codata.Sized.Delay as Delay using (bind; map)
open import Data.Bool using (not; _∧_; _∨_)

-- Helper: prove what foldStepEval-go computes for Not (Atomic p)
-- The state machine for Not (Atomic p) is:
--   - If p f = true: Atomic returns Satisfied, Not returns Violated → foldStepEval-go returns now false
--   - If p f = false: Atomic returns Violated, Not returns Continue, then rest=[] → now true
not-atomic-go-equiv : ∀ (p : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Not (Atomic p)) (NotState AtomicState) nothing f rest ≈ now (not (p f))

-- Pattern match on p f to make both sides reduce
-- When p f = true: Atomic returns Satisfied, Not returns Violated, foldStepEval-go returns 'now false'
-- When p f = false: Atomic returns Violated, Not returns Satisfied, foldStepEval-go returns 'now true'
not-atomic-go-equiv p f rest with p f
... | true = DB.now refl  -- Both sides reduce to 'now false'
... | false = DB.now refl  -- Both sides reduce to 'now true'

-- Main theorem for Not (Atomic p)
not-atomic-fold-equiv : ∀ (p : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Not (Atomic p)) trace ≈ checkColist (Not (Atomic p)) trace

-- Empty case: both return 'now true'
not-atomic-fold-equiv p [] = DB.now refl

-- Non-empty case: use copattern matching to handle the 'later' constructor
not-atomic-fold-equiv p (f ∷ rest) = DB.later λ where .force → not-atomic-go-equiv p f (rest .force)

-- And: Both operands must hold
-- For And (Atomic p) (Atomic q), the result should be (p f ∧ q f)

-- Helper: characterize stepEval for And (Atomic p) (Atomic q)
stepEval-and-atomic-computes : ∀ (p q : TimedFrame → Bool) (f : TimedFrame)
  → (p f ∧ q f ≡ true → stepEval (And (Atomic p) (Atomic q)) evalAtomicPred (AndState AtomicState AtomicState) nothing f ≡ Satisfied)
  × (p f ∧ q f ≡ false → ∃[ ce ] stepEval (And (Atomic p) (Atomic q)) evalAtomicPred (AndState AtomicState AtomicState) nothing f ≡ Violated ce)
stepEval-and-atomic-computes p q f with p f | q f
... | true  | true  = (λ _ → refl) , (λ ())
... | true  | false = (λ ()) , (mkCounterexample f "atomic predicate failed" , refl)
... | false | true  = (λ ()) , (mkCounterexample f "atomic predicate failed" , refl)
... | false | false = (λ ()) , (mkCounterexample f "atomic predicate failed" , refl)

and-atomic-go-equiv : ∀ (p q : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (And (Atomic p) (Atomic q)) (AndState AtomicState AtomicState) nothing f rest
      ≈ now (p f ∧ q f)

-- Pattern match on p f ∧ q f to enable reduction
and-atomic-go-equiv p q f rest with p f ∧ q f in eq
... | true  = DB.now refl  -- Both true: foldStepEval-go returns 'now true'
... | false = DB.now refl  -- At least one false: foldStepEval-go returns 'now false'

-- Main theorem for And (Atomic p) (Atomic q)
and-atomic-fold-equiv : ∀ (p q : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (And (Atomic p) (Atomic q)) trace ≈ checkColist (And (Atomic p) (Atomic q)) trace

-- Empty case: both return 'now true'
and-atomic-fold-equiv p q [] = DB.now refl

-- Non-empty case: use copattern matching
and-atomic-fold-equiv p q (f ∷ rest) = DB.later λ where .force → and-atomic-go-equiv p q f (rest .force)

-- Or: Either operand must hold
-- For Or (Atomic p) (Atomic q), the result should be (p f ∨ q f)

or-atomic-go-equiv : ∀ (p q : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Or (Atomic p) (Atomic q)) (OrState AtomicState AtomicState) nothing f rest
      ≈ now (p f ∨ q f)

-- Pattern match on p f and q f directly to enable reduction through nested with-clauses
or-atomic-go-equiv p q f rest with p f in eq-p | q f in eq-q
... | true  | true  = DB.now refl  -- Left satisfied: Or returns Satisfied immediately, foldStepEval-go returns now true
... | true  | false = DB.now refl  -- Left satisfied: Or returns Satisfied immediately, foldStepEval-go returns now true
... | false | true  = DB.now refl  -- Left violated, right satisfied: Or returns Satisfied, foldStepEval-go returns now true
... | false | false = DB.now refl  -- Both violated: Or returns Violated, foldStepEval-go returns now false

-- Main theorem for Or (Atomic p) (Atomic q)
or-atomic-fold-equiv : ∀ (p q : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Or (Atomic p) (Atomic q)) trace ≈ checkColist (Or (Atomic p) (Atomic q)) trace

-- Empty case: both return 'now true'
or-atomic-fold-equiv p q [] = DB.now refl

-- Non-empty case: use copattern matching
or-atomic-fold-equiv p q (f ∷ rest) = DB.later λ where .force → or-atomic-go-equiv p q f (rest .force)

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
