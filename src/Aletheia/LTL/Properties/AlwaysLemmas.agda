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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Aletheia imports
open import Aletheia.Trace.Context using (TimedFrame)
open import Aletheia.LTL.Syntax using (LTL; Always)
open import Aletheia.LTL.Coinductive using (evaluateLTLOnTrace)
open import Aletheia.LTL.Incremental using (LTLEvalState; initState; stepEval; StepResult; Violated; Satisfied; Continue; AlwaysState; Counterexample)
open import Aletheia.LTL.Properties.EvalHelpers using (foldStepEval-go; evalAtomicPred)

-- Generic bisimilarity lemmas
open import Aletheia.LTL.Properties.DelayLemmas using (bind-cong; bind-now; later-ext)

-- ============================================================================
-- RHS extraction lemmas - Attempt to prove with generic postulates only
-- ============================================================================
-- Strategy: Use bind-now for False/True cases, leave Continue case as hole

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

-- ============================================================================
-- RHS lemmas for evaluateLTLOnTrace (Always φ)
-- ============================================================================

-- General postulate for extended lambda equality (blocked by nominal distinction)
--
-- PROBLEM: Agda treats syntactically identical extended lambdas at different source
-- locations as nominally distinct, even in Cubical mode with path equality.
--
-- SOLUTION: Postulate that propositional equality holds for definitional equality.
-- This is a META-LEVEL statement: "refl should work here, but Agda blocks it."
--
-- Evidence: See EXTENDED_LAMBDA_BLOCKER_EVIDENCE.md and /tmp/cubical-test-results.md
postulate
  defEq-to-propEq : ∀ {A : Set} (x : A) → x ≡ x

-- When inner formula evaluates to false, Always evaluates to false
-- Proof: Use always-unfold, then apply bind reasoning via PropEq→Bisim conversion
always-rhs-when-false : ∀ (φ : LTL (TimedFrame → Bool))
  (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  → ∞ ⊢ evaluateLTLOnTrace φ curr (next ∷ rest') ≈ now false
  → ∞ ⊢ evaluateLTLOnTrace (Always φ) curr (next ∷ rest') ≈ now false
always-rhs-when-false φ curr next rest' inner-false =
  -- Use always-unfold to expose the bind structure
  -- Then use bind-cong and bind-now to reduce
  let unfold-eq = always-unfold φ curr next rest'

      -- The RHS of unfold-eq is: bind (evaluateLTLOnTrace φ ...) (λ r → if r then ... else now false)
      -- We need to show this ≈ now false given that evaluateLTLOnTrace φ ... ≈ now false

      -- Apply bind-cong: since inner ≈ now false, bind inner cont ≈ bind (now false) cont
      -- Then bind-now: bind (now false) cont ≈ cont false = now false

      rhs-reduces : ∞ ⊢ bind (evaluateLTLOnTrace φ curr (next ∷ rest'))
                             (λ r → if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
                                         else now false)
                      ≈ now false
      rhs-reduces =
        let step1 = bind-cong (evaluateLTLOnTrace φ curr (next ∷ rest')) (now false)
                              (λ r → if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
                                          else now false)
                              (λ r → if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
                                          else now false)
                              inner-false
                              (λ _ → DB.refl)
            step2 = bind-now false
                             (λ r → if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
                                         else now false)
                             (now false)
                             (DB.now refl)
        in DelayBisim.trans step1 step2

  in subst (λ x → ∞ ⊢ x ≈ now false) (sym unfold-eq) rhs-reduces

-- When inner formula evaluates to true, Always continues with recursive call
-- Implementation: Directly use the postulate
always-rhs-when-true : ∀ (φ : LTL (TimedFrame → Bool))
  (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → ∞ ⊢ evaluateLTLOnTrace φ curr (next ∷ rest') ≈ now true
  → (∀ {i : Size} → i ⊢ k .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force))
  → ∞ ⊢ later k ≈ evaluateLTLOnTrace (Always φ) curr (next ∷ rest')
always-rhs-when-true = always-true-case
  -- Goal: ∞ ⊢ later k ≈ evaluateLTLOnTrace (Always φ) curr (next ∷ rest')
  --
  -- By definition:
  --   evaluateLTLOnTrace (Always φ) curr (next ∷ rest')
  --   = bind (evaluateLTLOnTrace φ curr (next ∷ rest')) λ r →
  --       if r then later (λ where .force → evaluateLTLOnTrace (Always φ) next (rest' .force))
  --            else now false
  --
  -- We have: inner-true : evaluateLTLOnTrace φ curr (next ∷ rest') ≈ now true
  --
  -- By bind-cong:
  --   bind (evaluateLTLOnTrace φ ...) continuation
  --   ≈ bind (now true) continuation
  --
  -- By bind-now:
  --   bind (now true) continuation
  --   ≈ continuation true
  --   = if true then later (λ where .force → evaluateLTLOnTrace (Always φ) next ...) else now false
  --   = later (λ where .force → evaluateLTLOnTrace (Always φ) next ...)
  --
  -- Now we need to relate:
  --   later k  ≈  later (λ where .force → evaluateLTLOnTrace (Always φ) next ...)
  --
  -- By later-ext, this reduces to proving:
  --   k .force ≈ (λ where .force → evaluateLTLOnTrace (Always φ) next ...) .force
  --   = evaluateLTLOnTrace (Always φ) next (rest' .force)
  --
  -- Which we have from k-correct!
  --
  -- PROBLEM: Still blocked by extended lambda nominal equality in bind reduction.

-- Continue case: LEFT AS HOLE (see STRATEGY1_TYPE_ANALYSIS.md Part 11)
-- This is the genuinely hard case requiring state correspondence
always-rhs-continue-continues : ∀ (φ : LTL (TimedFrame → Bool)) (st' : LTLEvalState)
  (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred (initState φ) nothing curr ≡ Continue st'
  → (∀ {i : Size} → i ⊢ k .force ≈ evaluateLTLOnTrace (Always φ) next (rest' .force))
  → ∞ ⊢ later k ≈ evaluateLTLOnTrace (Always φ) curr (next ∷ rest')
always-rhs-continue-continues φ st' curr next rest' k step-eq k-correct = {!!}
  -- TODO: This requires understanding how stepEval Continue st' relates to
  -- evaluateLTLOnTrace result. See STRATEGY1_TYPE_ANALYSIS.md for analysis.

