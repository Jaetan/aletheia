{-# OPTIONS --safe --without-K #-}

-- Common imports and utilities used throughout the Aletheia codebase.
--
-- Purpose: Centralize frequently-used standard library imports to reduce boilerplate.
-- Exports: Core types (Bool, Nat, List, Maybe, String), basic operations, proofs.
-- Role: Foundation module imported by most other Aletheia modules.
module Aletheia.Prelude where

-- Basic types
open import Data.Bool public
  using (Bool; true; false; if_then_else_; _∧_; _∨_; not)

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

open import Data.Char public
  using (Char)

open import Data.Fin public
  using (Fin; zero; suc)
  -- Note: toℕ not exported to avoid clash with Data.Char.toℕ

open import Data.Vec public
  using (Vec; []; _∷_)

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
findByPredicate : ∀ {A : Set} → (A → Bool) → List A → Maybe A
findByPredicate pred [] = nothing
findByPredicate pred (x ∷ xs) = if pred x then just x else findByPredicate pred xs

-- Look up value by string key in association list
lookupByKey : ∀ {A : Set} → String → List (String × A) → Maybe A
lookupByKey key [] = nothing
lookupByKey key ((k , v) ∷ rest) =
  if ⌊ k ≟ key ⌋ then just v else lookupByKey key rest
