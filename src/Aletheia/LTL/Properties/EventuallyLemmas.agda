{-# OPTIONS --sized-types --without-K #-}

-- Eventually operator lemmas: Prove correspondence between incremental and coinductive semantics
--
-- The Eventually operator is the DUAL of Always:
--   evaluateLTLOnTrace (Eventually ψ) frame (next ∷ rest') =
--     bind (evaluateLTLOnTrace ψ frame (next ∷ rest')) λ r →
--       if r then now true else later (λ where .force → evaluateLTLOnTrace (Eventually ψ) next (rest' .force))
--
-- Key differences from Always:
-- - Always continues on true, fails on false: if r then later (...) else now false
-- - Eventually succeeds on true, continues on false: if r then now true else later (...)
-- - Mirror structure means similar proof strategy
--
-- Expected postulates: 2-4 (similar to Always, due to bind operation)

module Aletheia.LTL.Properties.EventuallyLemmas where

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
open import Aletheia.LTL.Syntax using (LTL; Eventually)
open import Aletheia.LTL.Coinductive using (evaluateLTLOnTrace)
open import Aletheia.LTL.Incremental using (LTLEvalState; EventuallyState; EventuallySucceeded; initState; stepEval; StepResult; Violated; Satisfied; Continue; Counterexample)
open import Aletheia.LTL.Properties.EvalHelpers using (foldStepEval-go; evalAtomicPred)

-- Generic bisimilarity lemmas
open import Aletheia.LTL.Properties.DelayLemmas using (later-ext; bind-now)

-- ============================================================================
-- Eventually Operator Structure Analysis
-- ============================================================================

-- The Eventually operator has a bind structure similar to Always:
--
-- Coinductive (RHS):
--   evaluateLTLOnTrace (Eventually ψ) frame (next ∷ rest') =
--     bind (evaluateLTLOnTrace ψ frame (next ∷ rest')) λ r →
--       if r then now true
--            else later (λ where .force → evaluateLTLOnTrace (Eventually ψ) next (rest' .force))
--
-- Incremental (LHS):
--   stepEval (Eventually φ) eval (EventuallyState st) prev curr
--     with stepEval φ eval st prev curr
--   ... | Continue st' = Continue (EventuallyState st')
--   ... | Violated _ = Continue (EventuallyState st)  -- Not yet, keep looking
--   ... | Satisfied = Satisfied  -- Found!
--
-- The key insight: Eventually SUCCEEDS when inner formula is true (dual of Always)
--
-- This has a bind operation → Will need continuation extraction → Expect 2-4 postulates
-- (Similar to Always, but with opposite polarity)

-- ============================================================================
-- LHS Lemmas: Properties of foldStepEval-go (Eventually φ)
-- ============================================================================

-- The incremental Eventually operator checks the inner formula at each frame.
-- If inner formula is satisfied, Eventually is satisfied.
-- If inner formula is violated, Eventually continues (keeps looking).
-- If inner formula continues, Eventually continues with updated state.

-- When inner stepEval returns Satisfied, Eventually returns true
foldStepEval-go-eventually-satisfied : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr : TimedFrame) (rest : Colist TimedFrame ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Satisfied
  → i ⊢ foldStepEval-go (Eventually φ) (EventuallyState st) prev curr rest ≈ now true
foldStepEval-go-eventually-satisfied φ st prev curr rest eq-satisfied
  rewrite eq-satisfied = DB.now refl

-- When inner stepEval returns Violated, Eventually continues (keeps looking)
-- Note: The state doesn't update - we keep the same state and continue searching
foldStepEval-go-eventually-violated : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (ce : Counterexample)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Violated ce
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Eventually φ) (EventuallyState st) (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Eventually φ) (EventuallyState st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-eventually-violated {i} φ st prev curr next rest' ce k eq-violated k-correct
  rewrite eq-violated = later-ext _ k helper
  where
    helper : ∀ {j : Size< i} → j ⊢ (λ where .force → foldStepEval-go (Eventually φ) (EventuallyState st) (just curr) next (rest' .force)) .force ≈ k .force
    helper {j} = DB.sym (k-correct {j})

-- When inner stepEval returns Continue, Eventually continues with updated state
foldStepEval-go-eventually-continue : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (st st' : LTLEvalState)
  (prev : Maybe TimedFrame) (curr next : TimedFrame) (rest' : Thunk (Colist TimedFrame) ∞)
  (k : Thunk (Delay Bool) ∞)
  → stepEval φ evalAtomicPred st prev curr ≡ Continue st'
  → (∀ {j : Size< i} → j ⊢ k .force ≈ foldStepEval-go (Eventually φ) (EventuallyState st') (just curr) next (rest' .force))
  → i ⊢ foldStepEval-go (Eventually φ) (EventuallyState st) prev curr (next ∷ rest') ≈ later k
foldStepEval-go-eventually-continue {i} φ st st' prev curr next rest' k step-eq k-correct
  rewrite step-eq = later-ext _ k helper
  where
    helper : ∀ {j : Size< i} → j ⊢ (λ where .force → foldStepEval-go (Eventually φ) (EventuallyState st') (just curr) next (rest' .force)) .force ≈ k .force
    helper {j} = DB.sym (k-correct {j})

-- ============================================================================
-- RHS Lemmas: Properties of evaluateLTLOnTrace (Eventually φ)
-- ============================================================================

-- The Eventually operator RHS uses bind (like Always), so we'll need postulates
-- for continuation extraction.
--
-- Structure:
--   evaluateLTLOnTrace (Eventually ψ) frame (next ∷ rest') =
--     bind (evaluateLTLOnTrace ψ frame (next ∷ rest')) λ r →
--       if r then now true else later (λ where .force → evaluateLTLOnTrace (Eventually ψ) next (rest' .force))
--
-- Key difference from Always: continuation behavior is OPPOSITE
-- - When r = true: return now true (success!)
-- - When r = false: continue searching with later (...)
--
-- This means:
-- - eventually-rhs-when-true needs to show: if inner ≈ now true, then bind returns now true
-- - eventually-rhs-when-false needs to show: if inner ≈ now false, then bind returns later (...)
--
-- The first can be proven using bind-now!
-- The second requires extracting the continuation from bind → POSTULATE

-- DELETED: eventually-rhs-when-true (operator-specific postulate)
-- DELETED: eventually-rhs-when-false (operator-specific postulate)
-- These postulates were masking gaps in the proof and have been replaced with holes.

-- The continuation is embedded in evaluateLTLOnTrace definition:
-- λ r → if r then now true else later (λ where .force → evaluateLTLOnTrace (Eventually φ) next (rest' .force))
--                                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--                                       This extended lambda is nominally distinct from k
--
-- To prove this, we would need:
-- 1. Extract continuation from bind
-- 2. Apply to false: continuation false ≡ later (λ where .force → evaluateLTLOnTrace ...)
-- 3. Prove k .force ≈ (λ where .force → evaluateLTLOnTrace ...) .force
--
-- Step 2 blocks on extended lambda nominal equality (same issue as Always).

-- ============================================================================
-- Summary of Eventually Operator Lemmas
-- ============================================================================

-- LHS lemmas (proven using rewrite + later-ext):
-- ✅ foldStepEval-go-eventually-satisfied
-- ✅ foldStepEval-go-eventually-violated
-- ✅ foldStepEval-go-eventually-continue

-- RHS lemmas:
-- ❌ eventually-rhs-when-true (POSTULATE - extended lambda nominal equality)
-- ❌ eventually-rhs-when-false (POSTULATE - extended lambda nominal equality)

-- Expected postulate count: 2 for Eventually (compared to 4 for Always)
--
-- Why only 2 instead of 4?
-- - Always has 4 RHS postulates: always-rhs-when-false, always-rhs-when-true,
--   always-rhs-satisfied-continues, always-rhs-continue-continues
-- - Eventually mirrors the first 2 but doesn't need the last 2 (yet)
-- - May need additional postulates when writing full bisimilarity proofs
--
-- The extended lambda nominal equality problem affects BOTH branches:
-- - True branch: if r then now true else later (...) → extended lambda in else
-- - False branch: continuation contains extended lambda
--
-- Even though "now true" is simple, the continuation λ r → if r then ... else later (...)
-- is embedded in evaluateLTLOnTrace and nominally distinct from any local construction.

-- ============================================================================
-- Postulate Count Update
-- ============================================================================

-- Before Eventually: 9 postulates (5 generic delay + 4 Always-specific + 0 Next)
-- After Eventually: 11 postulates (5 generic delay + 4 Always + 2 Eventually + 0 Next)
--
-- Running total: 11 postulates
--
-- Postulate discipline status: ⚠️ Added 2 new postulates for Eventually
-- - Both are necessary due to extended lambda nominal equality
-- - Mirror the Always pattern (always-rhs-when-false, always-rhs-when-true)
-- - No workaround found in standard Agda without-K
-- - Deferred to Phase 5: witnessed delay or cubical Agda exploration
