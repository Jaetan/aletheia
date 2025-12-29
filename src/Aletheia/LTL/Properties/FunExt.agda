{-# OPTIONS --without-K #-}

-- Functional extensionality for LTL temporal operator proofs.
-- Provides functional extensionality to resolve lambda nominal equality issues.
--
-- DESIGN RATIONALE:
-- We postulate functional extensionality rather than using a proof from an external library
-- because of fundamental flag incompatibilities in Agda's current ecosystem:
-- - Full cubical Agda (with proven funExt) requires --guardedness
-- - Our coinductive LTL modules require --sized-types
-- - These two flags are INCOMPATIBLE (can lead to inconsistency per Agda documentation)
--
-- Theoretical soundness:
-- - Functional extensionality is PROVABLE in cubical type theory
-- - It's consistent with intensional type theory (not an arbitrary axiom)
-- - We postulate it here as a practical workaround for the flag incompatibility
-- - This does not compromise logical consistency
--
-- This resolves lambda nominal equality issues in Properties.agda where --without-K
-- treats syntactically identical lambdas at different source locations as distinct objects.

module Aletheia.LTL.Properties.FunExt where

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)

-- ============================================================================
-- FUNCTIONAL EXTENSIONALITY (POSTULATED)
-- ============================================================================

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : Set ℓ'

-- Core postulate: Two functions that agree on all inputs are equal
-- This is provable in cubical type theory, but we postulate it for flag compatibility
postulate
  funExt : ∀ {A : Set ℓ} {B : A → Set ℓ'}  {f g : (x : A) → B x}
         → ((x : A) → f x ≡ g x)
         → f ≡ g

-- Specialized for non-dependent functions (simpler to use)
funExt-simple : {A : Set ℓ} {B : Set ℓ'} {f g : A → B}
              → ((x : A) → f x ≡ g x)
              → f ≡ g
funExt-simple {f = f} {g = g} pointwise-eq = funExt pointwise-eq

-- ============================================================================
-- LAMBDA EQUALITY LEMMAS
-- ============================================================================

-- Prove two lambda expressions are equal if they compute the same result
-- Usage: When --without-K treats two syntactically identical lambdas as different
lambda-equal-if-pointwise-equal : {A : Set ℓ} {B : Set ℓ'} (f g : A → B)
                                → ((x : A) → f x ≡ g x)
                                → f ≡ g
lambda-equal-if-pointwise-equal f g = funExt

-- Reflexivity: Any lambda is equal to itself (trivial but useful for rewriting)
lambda-equal-refl : {A : Set ℓ} {B : Set ℓ'} (f : A → B)
                  → f ≡ f
lambda-equal-refl f = refl

-- ============================================================================
-- CONDITIONAL EQUALITY LEMMAS (for if_then_else_)
-- ============================================================================

-- Two conditionals are equal if their branches are equal
conditional-equal-via-branches : {A : Set ℓ} (b : Bool) {x y z w : A}
                               → x ≡ y
                               → z ≡ w
                               → (if b then x else z) ≡ (if b then y else w)
conditional-equal-via-branches false x≡y z≡w = z≡w
conditional-equal-via-branches true x≡y z≡w = x≡y

-- ============================================================================
-- APPLICATION-SPECIFIC LEMMAS FOR LTL PROOFS
-- ============================================================================

-- Bind continuation equality for Always operator
-- This is the KEY lemma that resolves the lambda nominal equality blocker
--
-- In Properties.agda (Violated case), we have two syntactically identical lambdas:
-- 1. Local lambda: λ r → if r then (later ...) else now false
-- 2. Definition lambda from Coinductive.agda (same structure)
--
-- Under --without-K, these are treated as DIFFERENT because they're at different source locations.
-- With functional extensionality, we can prove they're EQUAL (they agree on all inputs).
bind-continuation-equal-for-always : {A : Set ℓ} {B : Set ℓ'} (k1 k2 : A → B)
                                   → ((x : A) → k1 x ≡ k2 x)  -- If they agree on all inputs
                                   → k1 ≡ k2                     -- Then they're equal (by funExt)
bind-continuation-equal-for-always k1 k2 pointwise-eq = funExt pointwise-eq

-- Note: While we postulate funExt here, it IS provable in cubical type theory!
-- The postulate is consistent and doesn't introduce logical inconsistency.
-- We use it here purely for flag compatibility (avoiding --guardedness/--sized-types conflict).

-- ============================================================================
-- USAGE NOTES
-- ============================================================================

-- How to use these lemmas in Properties.agda:
--
-- 1. Import: open import Aletheia.LTL.Properties.FunExt using (funExt)
-- 2. Use funExt to prove lambda equality:
--    lambda-eq : f ≡ g
--    lambda-eq = funExt (λ x → ... proof that f x ≡ g x ...)
--
-- This resolves the blocker:
--   OLD: Can't prove (λ x → ...) ≡ (λ x → ...) because different source locations
--   NEW: Use funExt to prove they're equal (they agree on all inputs!)
