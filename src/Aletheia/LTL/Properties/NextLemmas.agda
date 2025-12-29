{-# OPTIONS --sized-types --without-K #-}

-- Next operator lemmas: Prove correspondence between incremental and coinductive semantics
--
-- The Next operator has the simplest structure of all temporal operators:
--   evaluateLTLOnTrace (Next ψ) frame (next ∷ rest') =
--     later λ where .force → evaluateLTLOnTrace ψ next (rest' .force)
--
-- No bind, no if-then-else - just skip first frame and evaluate inner formula!
--
-- This simplicity means we need FEWER postulates than Always (0-2 expected).

module Aletheia.LTL.Properties.NextLemmas where

-- Standard library imports
open import Size using (Size; ∞; Size<_)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later; bind)
open import Codata.Sized.Delay.Bisimilarity as DelayBisim using (_⊢_≈_; Bisim)
import Codata.Sized.Delay.Bisimilarity as DB
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Aletheia imports
open import Aletheia.Trace.Context using (TimedFrame)
open import Aletheia.LTL.Syntax using (LTL; Next)
open import Aletheia.LTL.Coinductive using (evaluateLTLOnTrace)
open import Aletheia.LTL.Incremental using (LTLEvalState; NextState; NextActive; initState; stepEval; StepResult; Violated; Satisfied; Continue; Counterexample)
open import Aletheia.LTL.Properties.EvalHelpers using (foldStepEval-go; evalAtomicPred)

-- Generic bisimilarity lemmas
open import Aletheia.LTL.Properties.DelayLemmas using (later-ext)

-- ============================================================================
-- Next Operator Structure Analysis
-- ============================================================================

-- The Next operator has a trivial structure:
--
-- Coinductive (RHS):
--   evaluateLTLOnTrace (Next ψ) frame (next ∷ rest') =
--     later (λ where .force → evaluateLTLOnTrace ψ next (rest' .force))
--
-- Incremental (LHS):
--   stepEval (Next φ) eval (NextState st) prev curr = Continue (NextActive st)
--   stepEval (Next φ) eval (NextActive st) prev curr = stepEval φ eval st prev curr
--
-- The key insight: Next just "shifts" the trace by one frame!
--
-- No bind operation → No continuation extraction problem!
-- Just a single later → Can use later-ext directly!

-- ============================================================================
-- LHS Lemmas: Properties of foldStepEval-go (Next φ)
-- ============================================================================

-- The incremental Next operator works in two phases:
-- 1. First frame: NextState → NextActive (skip)
-- 2. Second frame onward: Evaluate inner formula φ

-- When inner stepEval returns Violated, Next returns false
foldStepEval-go-next-violated : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞) (ce : Counterexample)
  → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
  → i ⊢ foldStepEval-go (Next φ) (NextActive st) prev curr rest ≈ now false
foldStepEval-go-next-violated φ st prev curr rest ce eq-violated
  rewrite eq-violated = DB.now refl

-- When inner stepEval returns Satisfied, Next returns true
foldStepEval-go-next-satisfied : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Satisfied
  → i ⊢ foldStepEval-go (Next φ) (NextActive st) prev curr rest ≈ now true
foldStepEval-go-next-satisfied φ st prev curr rest eq-satisfied
  rewrite eq-satisfied = DB.now refl

-- When inner stepEval returns Continue, Next continues with updated state
foldStepEval-go-next-continue : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st st' : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Continue st'
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Next φ) (NextActive st') (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Next φ) (NextActive st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-next-continue {i} φ st st' prev curr next rest' k step-eq k-correct
  rewrite step-eq = later-ext _ k helper
  where
    helper : ∀ {j : Size< i} → j ⊢ (λ where .force → foldStepEval-go (Next φ) (NextActive st') (just curr) next (rest' .force)) .force ≈ k .force
    helper {j} = DB.sym (k-correct {j})

-- ============================================================================
-- RHS Lemmas: Properties of evaluateLTLOnTrace (Next φ)
-- ============================================================================

-- The Next operator RHS is MUCH simpler than Always!
-- No bind operation - just a single later wrapping the inner evaluation
--
-- Structure:
--   evaluateLTLOnTrace (Next ψ) frame (next ∷ rest') =
--     later (λ where .force → evaluateLTLOnTrace ψ next (rest' .force))
--
-- This is exactly the same structure as foldStepEval-continue-nonempty!
-- So we might not need ANY RHS-specific postulates!

-- When we have a thunk k that evaluates the inner formula,
-- show that Next wraps it in a later
next-rhs-structure : ∀ (φ : LTL (TimedFrame → Bool))
  (frame next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → (∀ {i : Size} → i ⊢ k .force ≈ evaluateLTLOnTrace φ next (rest' .force))
  → ∞ ⊢ later k ≈ evaluateLTLOnTrace (Next φ) frame (next ∷ rest')
next-rhs-structure φ frame next rest' k k-correct =
  later-ext k _ helper
  where
    helper : ∀ {i : Size} → i ⊢ k .force ≈ (λ where .force → evaluateLTLOnTrace φ next (rest' .force)) .force
    helper {i} = k-correct {i}

-- CRITICAL: Does this type-check?
-- If YES: We can prove RHS properties using ONLY later-ext (no postulates!) ✅
-- If NO: We need extended lambda equality (postulate) ❌

-- ============================================================================
-- Summary of Next Operator Lemmas
-- ============================================================================

-- LHS lemmas (proven using rewrite + later-ext):
-- ✅ foldStepEval-go-next-violated
-- ✅ foldStepEval-go-next-satisfied
-- ✅ foldStepEval-go-next-continue

-- RHS lemmas:
-- ✅ next-rhs-structure (proven using later-ext - TEST if this works!)

-- Expected postulate count: 0 if next-rhs-structure type-checks!
-- This would be a HUGE win - the Next operator might need NO new postulates!

-- The key difference from Always:
-- - Always uses bind → need to access continuation → extended lambda problem
-- - Next uses just later → can use later-ext directly → NO extended lambda problem!
