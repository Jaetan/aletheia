{-# OPTIONS --sized-types --without-K #-}

-- Investigation Results (December 2025): Extended Lambda Equality
--
-- FINDING: The K axiom does NOT help with extended lambda nominal equality.
-- Two syntactically identical extended lambdas (λ where .force → ...) at different
-- source locations remain nominally distinct even with K enabled.
--
-- TESTED: AlwaysLemmas without --without-K flag → lemmas still required postulates
-- CONCLUSION: K provides UIP (uniqueness of identity proofs), NOT lambda equality
--
-- We use --without-K for stricter guarantees (HoTT compatibility) since K provides
-- no benefit for our use case.
--
-- See investigation details:
--   - ~/.claude/plans/cosmic-spinning-axolotl.md (comprehensive plan)
--   - ~/.claude/plans/ancient-snuggling-rainbow.md (initial investigation)
--   - /tmp/bind-if-later-ext-def.agda (generic lemma experiment)
--   - /tmp/always-test.agda (experimentation showing fundamental limitation)
--
-- This module breaks the circular dependency:
--   Properties.agda → AlwaysLemmas.agda → EvalHelpers.agda
-- by importing evaluation helpers from EvalHelpers instead of Properties.

module Aletheia.LTL.Properties.AlwaysLemmas where

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
open import Aletheia.LTL.Syntax using (LTL; Always)
open import Aletheia.LTL.Coinductive using (evaluateLTLOnTrace)
open import Aletheia.LTL.Incremental using (LTLEvalState; initState; stepEval; StepResult; Violated; Satisfied; Continue; AlwaysState; Counterexample)
open import Aletheia.LTL.Properties.EvalHelpers using (foldStepEval-go; evalAtomicPred)

-- Generic bisimilarity lemmas
open import Aletheia.LTL.Properties.DelayLemmas using (bind-cong; bind-now; later-ext)

-- ============================================================================
-- RHS extraction postulates - DELETED for honest proof assessment
-- ============================================================================
-- These operator-specific postulates were masking gaps in the proof.
-- They are replaced with holes to show what still needs to be proven.

-- ============================================================================
-- ATTEMPT 2: Prove LHS lemmas for foldStepEval-go
-- ============================================================================

-- When inner stepEval returns Violated, Always foldStepEval returns false
foldStepEval-go-always-violated : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞) (ce : Counterexample)
  → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
  → i ⊢ foldStepEval-go (Always φ) (AlwaysState st) prev curr rest ≈ now false
foldStepEval-go-always-violated φ st prev curr rest ce eq-violated
  rewrite eq-violated = DB.now refl

-- When inner stepEval returns Satisfied, Always continues with preserved state
foldStepEval-go-always-satisfied : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Satisfied
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Always φ) (AlwaysState st) (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Always φ) (AlwaysState st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-always-satisfied {i} φ st prev curr next rest' k eq-satisfied k-correct
  rewrite eq-satisfied = later-ext _ k helper
  where
    helper : ∀ {j : Size< i} → j ⊢ (λ where .force → foldStepEval-go (Always φ) (AlwaysState st) (just curr) next (rest' .force)) .force ≈ k .force
    helper {j} = DB.sym (k-correct {j})

-- When inner stepEval returns Continue, Always continues with updated state
foldStepEval-go-always-continue : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st st' : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Continue st'
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Always φ) (AlwaysState st') (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Always φ) (AlwaysState st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-always-continue {i} φ st st' prev curr next rest' k step-eq k-correct
  rewrite step-eq = later-ext _ k helper
  where
    helper : ∀ {j : Size< i} → j ⊢ (λ where .force → foldStepEval-go (Always φ) (AlwaysState st') (just curr) next (rest' .force)) .force ≈ k .force
    helper {j} = DB.sym (k-correct {j})

