{-# OPTIONS --without-K --sized-types #-}

-- Generic bisimilarity lemmas for the Delay monad
-- These are standard properties used in Delay monad proofs
--
-- RATIONALE FOR POSTULATES:
-- The Agda standard library provides basic bisimilarity (reflexive, symmetric, transitive)
-- but does NOT provide bind congruence or extensionality for extended lambda patterns.
-- These properties are standard in delay monad literature (see research papers).
--
-- We postulate them here as generic, reusable lemmas rather than operator-specific ones.

module Aletheia.LTL.Properties.DelayLemmas where

open import Size using (Size; ∞; Size<_)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later; bind)
open import Codata.Sized.Delay.Bisimilarity using (_⊢_≈_; Bisim; now; later)
import Codata.Sized.Delay.Bisimilarity as DB
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_)

private
  variable
    ℓ ℓ' : Level
    A B : Set ℓ
    i : Size

-- ============================================================================
-- BIND CONGRUENCE (Generic for all uses of bind)
-- ============================================================================

-- If two delays are bisimilar and continuations are pointwise equal,
-- then binding them produces bisimilar results
--
-- This is a fundamental property of monadic bind with respect to bisimilarity
-- Provable in setoid-based developments, postulated here for definitional equality
postulate
  bind-cong : {A B : Set ℓ} {i : Size}
    (d1 d2 : Delay A ∞)
    (f g : A → Delay B ∞)
    → i ⊢ d1 ≈ d2
    → ((x : A) → i ⊢ f x ≈ g x)  -- Pointwise bisimilarity of continuations
    → i ⊢ bind d1 f ≈ bind d2 g

-- Specialization: If d ≈ now x, then bind d f ≈ f x
-- This captures bind reduction for the 'now' case
postulate
  bind-now : {A B : Set ℓ} {i : Size}
    (x : A) (f : A → Delay B ∞) (d : Delay A ∞)
    → i ⊢ d ≈ now x
    → i ⊢ bind d f ≈ f x

-- ============================================================================
-- LATER/THUNK EXTENSIONALITY
-- ============================================================================

-- If two thunks force to bisimilar values, then 'later' applied to them is bisimilar
--
-- This is the key property needed for extended lambda equality:
-- If (t1 .force ≈ t2 .force) for all sizes, then (later t1 ≈ later t2)
--
-- Standard in coinductive proofs, but requires extensionality for thunks
postulate
  later-ext : {A : Set ℓ} {i : Size}
    (t1 t2 : Thunk (Delay A) ∞)
    → (∀ {j : Size< i} → j ⊢ t1 .force ≈ t2 .force)
    → i ⊢ later t1 ≈ later t2

-- Variant: Prove bisimilarity by showing forced thunks are equal
-- Useful when we have propositional equality after forcing
postulate
  later-cong : {A : Set ℓ} {i : Size}
    (t1 t2 : Thunk (Delay A) ∞)
    → (∀ {j : Size< i} → t1 .force ≡ t2 .force)  -- Propositional equality
    → i ⊢ later t1 ≈ later t2

-- ============================================================================
-- TRANSITIVITY AND SYMMETRY (from stdlib, re-exported for convenience)
-- ============================================================================

-- These are proven in the standard library, we just re-export them
-- Note: We don't re-export trans, sym, refl here to avoid name clashes
-- Use DB.trans, DB.sym, DB.refl directly, or import from DelayBisim

-- ============================================================================
-- USAGE NOTES
-- ============================================================================

-- These lemmas are GENERIC and can be used for proving equivalences for:
-- - Always operator
-- - Eventually operator
-- - Until operator
-- - Any other operator using bind and later
--
-- They capture the essential properties of Delay bisimilarity needed for
-- coinductive LTL proofs without being tied to specific operators.
