{-# OPTIONS --sized-types --without-K #-}

-- Evaluation helpers for LTL Properties proofs
--
-- This module contains foldStepEval and related helpers, extracted from Properties.agda
-- to break circular dependencies with AlwaysLemmas.agda.
--
-- Dependency chain:
--   EvalHelpers (this module)
--   ├─ Incremental (stepEval, initState)
--   ├─ Coinductive (evaluateLTLOnTrace)
--   └─ Evaluation (evalAtInfiniteExtension)
--
-- Both Properties.agda and AlwaysLemmas.agda can import from here.

module Aletheia.LTL.Properties.EvalHelpers where

-- Standard library imports
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)

-- Aletheia imports
open import Aletheia.Trace.Context using (TimedFrame)
open import Aletheia.LTL.Syntax using (LTL; Next; Always)
open import Aletheia.LTL.Incremental using (LTLEvalState; NextActive; AlwaysState; initState; stepEval; StepResult; Violated; Satisfied; Continue)
open import Aletheia.LTL.Evaluation using (evalAtInfiniteExtension)

-- ============================================================================
-- EVALUATION HELPERS
-- ============================================================================

-- Evaluator for atomic predicates in LTL (TimedFrame → Bool)
-- The predicate itself doesn't use previous frame, but stepEval's signature requires it
evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → Bool) → Bool
evalAtomicPred _ curr p = p curr

-- Forward declaration of foldStepEval-go (defined mutually with helpers below)
foldStepEval-go : ∀ {i : Size}
                → LTL (TimedFrame → Bool)     -- Original formula (for stepEval)
                → LTLEvalState                -- Current evaluation state
                → Maybe TimedFrame             -- Previous frame
                → TimedFrame                   -- Current frame
                → Colist TimedFrame i          -- Remaining frames
                → Delay Bool i

-- Helper: Process Continue result for infinite extension (empty rest)
-- When trace ends, evaluate formula assuming current frame repeats forever
private
  foldStepEval-continue-empty : ∀ {i : Size}
    → (φ : LTL (TimedFrame → Bool))
    → LTLEvalState
    → TimedFrame
    → Delay Bool i
  foldStepEval-continue-empty (Next ψ) (NextActive _) curr = now (evalAtInfiniteExtension curr ψ)
  foldStepEval-continue-empty (Always ψ) (AlwaysState _) curr = now (evalAtInfiniteExtension curr ψ)
  foldStepEval-continue-empty φ _ curr = now (evalAtInfiniteExtension curr φ)

-- Helper: Process Continue result for non-empty rest
private
  foldStepEval-continue-nonempty : ∀ {i : Size}
    → (φ : LTL (TimedFrame → Bool))
    → LTLEvalState
    → TimedFrame
    → TimedFrame
    → Thunk (Colist TimedFrame) i
    → Delay Bool i
  foldStepEval-continue-nonempty φ st' curr next rest' =
    later λ where .force → foldStepEval-go φ st' (just curr) next (rest' .force)

-- Helper: Process StepResult without using 'with'
-- This makes proofs easier by avoiding with-pattern matching
private
  foldStepEval-process-result : ∀ {i : Size}
    → (φ : LTL (TimedFrame → Bool))
    → StepResult
    → TimedFrame
    → Colist TimedFrame i
    → Delay Bool i
  foldStepEval-process-result φ (Violated _) curr rest = now false
  foldStepEval-process-result φ Satisfied curr rest = now true
  foldStepEval-process-result φ (Continue st') curr [] = foldStepEval-continue-empty φ st' curr
  foldStepEval-process-result φ (Continue st') curr (next ∷ rest') =
    foldStepEval-continue-nonempty φ st' curr next rest'

-- Main recursive helper: evaluate formula on non-empty trace
-- Delegates to foldStepEval-process-result to avoid 'with'
foldStepEval-go φ st prev curr rest =
  foldStepEval-process-result φ (stepEval φ evalAtomicPred st prev curr) curr rest

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
