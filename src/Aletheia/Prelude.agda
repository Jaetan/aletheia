{-# OPTIONS --safe --without-K #-}

-- Common imports and utilities used throughout the Aletheia codebase.
--
-- Purpose: Centralize frequently-used standard library imports to reduce boilerplate.
-- Exports: Core types (Bool, Nat, List, Maybe, String), basic operations, proofs.
-- Role: Foundation module imported by most other Aletheia modules.
module Aletheia.Prelude where

-- Basic types
open import Data.Bool public
  using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Unit public
  using (tt)

open import Data.Nat public
  using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _≡ᵇ_)
  -- Note: _≤ᵇ_ not exported to avoid clash with Data.Rational._≤ᵇ_

open import Data.List public
  using (List; []; _∷_; length; map; filter; foldr)

open import Data.Maybe public
  using (Maybe; just; nothing; maybe)

open import Data.String public
  using (String; _++_)

-- Import string equality for utility functions
open import Data.String.Properties using (_≟_)

open import Data.Product public
  using (_×_; _,_; proj₁; proj₂)

open import Data.Sum public
  using (_⊎_; inj₁; inj₂)

-- Rationals (common in signal processing)
open import Data.Rational public
  using (ℚ)

open import Data.Integer public
  using (ℤ; +_)

-- Equality and decidability
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; cong; sym; trans)

open import Relation.Nullary public
  using (Dec; yes; no; ¬_)

open import Relation.Nullary.Decidable public
  using (⌊_⌋)

-- Function combinators
open import Function public
  using (_∘_; _$_; id; const)

-- COMMON UTILITY FUNCTIONS
-- ============================================================================

-- Find first element in list matching a predicate
-- Note: Uses Bool for runtime efficiency; stdlib's Data.List.Relation.Unary.Any is proof-oriented
findByPredicate : ∀ {A : Set} → (A → Bool) → List A → Maybe A
findByPredicate pred [] = nothing
findByPredicate pred (x ∷ xs) = if pred x then just x else findByPredicate pred xs

-- Look up value by string key in association list
-- Note: Uses Bool equality for runtime lookup; proof-oriented alternatives exist in stdlib
lookupByKey : ∀ {A : Set} → String → List (String × A) → Maybe A
lookupByKey key [] = nothing
lookupByKey key ((k , v) ∷ rest) =
  if ⌊ k ≟ key ⌋ then just v else lookupByKey key rest

-- List indexing: O(n) lookup by position
listIndex : ∀ {A : Set} → ℕ → List A → Maybe A
listIndex _ [] = nothing
listIndex zero (x ∷ _) = just x
listIndex (suc n) (_ ∷ xs) = listIndex n xs

-- Lift Maybe to E ⊎ A with an error value on Nothing
require : ∀ {E A : Set} → E → Maybe A → E ⊎ A
require err = maybe inj₂ (inj₁ err)

-- Bind operator for Either (⊎) monad (used by parsers and command routing)
_>>=ₑ_ : ∀ {E A B : Set} → E ⊎ A → (A → E ⊎ B) → E ⊎ B
inj₁ err >>=ₑ _ = inj₁ err
inj₂ x >>=ₑ f = f x

-- Map over the error (left) side of a coproduct
mapₑ : ∀ {E₁ E₂ A : Set} → (E₁ → E₂) → E₁ ⊎ A → E₂ ⊎ A
mapₑ f (inj₁ e) = inj₁ (f e)
mapₑ _ (inj₂ a) = inj₂ a

-- CAN ID bounds (used for validation and type constraints)
standard-can-id-max : ℕ
standard-can-id-max = 2048  -- 2^11 (11-bit standard CAN IDs: 0x000-0x7FF)

extended-can-id-max : ℕ
extended-can-id-max = 536870912  -- 2^29 (29-bit extended CAN IDs: 0x00000000-0x1FFFFFFF)

-- Maximum physical bits in a CAN-FD frame (64 bytes × 8 bits)
max-physical-bits : ℕ
max-physical-bits = 512

-- Boolean conditional that provides a T proof in the true branch.
-- Unlike if_then_else_, this passes the T b witness to the true branch,
-- enabling construction of types that embed T (n <ᵇ max).
-- Defined as a regular function (no with), so rewrite works in proofs.
ifᵀ_then_else_ : ∀ {A : Set} (b : Bool) → (T b → A) → A → A
ifᵀ true  then f else _ = f tt
ifᵀ false then _ else x = x

-- T b has at most one inhabitant: T true = ⊤ (unique by η), T false = ⊥ (empty).
-- Essential for decidable equality and roundtrip proofs on bounded types.
T-irrelevant : ∀ {b : Bool} (p q : T b) → p ≡ q
T-irrelevant {true}  _ _ = refl
T-irrelevant {false} () _

-- Convert T b witness to propositional equality b ≡ true.
T→true : ∀ {b : Bool} → T b → b ≡ true
T→true {true} _ = refl

-- Given a T b witness, ifᵀ selects the true branch applied to pf.
-- Splits on b internally; avoids with-abstraction at call sites where
-- the type of `Standard rawId pf` creates a rigid dependency on b.
-- Uses η for ⊤: when b = true, pf : T true = ⊤ is definitionally tt.
ifᵀ-witness : ∀ {A : Set} {b : Bool} (f : T b → A) (e : A) (pf : T b)
  → ifᵀ b then f else e ≡ f pf
ifᵀ-witness {b = true}  f e pf = refl
ifᵀ-witness {b = false} _ _ ()

-- 8 ≤ 512 (one byte fits in max-physical-bits)
-- Defined once to avoid duplicating the 8-deep s≤s chain
8≤max-physical-bits : 8 ≤ max-physical-bits
8≤max-physical-bits = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
  where open import Data.Nat using (z≤n; s≤s)
