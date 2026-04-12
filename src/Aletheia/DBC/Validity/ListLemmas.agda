{-# OPTIONS --safe --without-K #-}

-- List lemmas for DBC validity proofs.
--
-- Purpose: Reusable lemmas connecting list operations (++, concatMap)
-- to propositional emptiness (≡ []) and All predicates.
module Aletheia.DBC.Validity.ListLemmas where

open import Data.List using (List; []; _∷_; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (++-conicalˡ; ++-conicalʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    A B : Set

-- ============================================================================
-- APPEND AND EMPTINESS
-- ============================================================================

-- If xs ++ₗ ys ≡ [], then xs ≡ []
-- Thin wrapper around stdlib's ++-conicalˡ (which takes explicit args).
++-≡[]-left : {xs ys : List A} → xs ++ₗ ys ≡ [] → xs ≡ []
++-≡[]-left {xs = xs} {ys} = ++-conicalˡ xs ys

-- If xs ++ₗ ys ≡ [], then ys ≡ []
-- Thin wrapper around stdlib's ++-conicalʳ (which takes explicit args).
++-≡[]-right : {xs ys : List A} → xs ++ₗ ys ≡ [] → ys ≡ []
++-≡[]-right {xs = xs} {ys} = ++-conicalʳ xs ys

-- If xs ++ₗ ys ≡ [], then both are []
++-≡[]-split : {xs ys : List A} → xs ++ₗ ys ≡ [] → xs ≡ [] × ys ≡ []
++-≡[]-split eq = ++-≡[]-left eq , ++-≡[]-right eq

-- If both are [], then xs ++ₗ ys ≡ []
++-≡[]-combine : {xs ys : List A} → xs ≡ [] → ys ≡ [] → xs ++ₗ ys ≡ []
++-≡[]-combine refl refl = refl

-- ============================================================================
-- CONCATMAP AND ALL
-- ============================================================================

-- If concatMap f xs ≡ [], then f returns [] for every element
concatMap-≡[]-sound : {f : A → List B} {xs : List A} →
  concatMap f xs ≡ [] → All (λ x → f x ≡ []) xs
concatMap-≡[]-sound {xs = []}     _  = []
concatMap-≡[]-sound {xs = x ∷ xs} eq =
  ++-≡[]-left eq ∷ concatMap-≡[]-sound (++-≡[]-right eq)

-- If f returns [] for every element, then concatMap f xs ≡ []
concatMap-≡[]-complete : {f : A → List B} {xs : List A} →
  All (λ x → f x ≡ []) xs → concatMap f xs ≡ []
concatMap-≡[]-complete []         = refl
concatMap-≡[]-complete (px ∷ pxs) = ++-≡[]-combine px (concatMap-≡[]-complete pxs)

-- ============================================================================
-- ALL OVER APPEND AND CONCATMAP
-- ============================================================================

-- concatMap preserves All P (general form)
All-concatMap : {P : B → Set} {f : A → List B} {xs : List A} →
  All (λ x → All P (f x)) xs → All P (concatMap f xs)
All-concatMap []       = []
All-concatMap (p ∷ ps) = ++⁺ p (All-concatMap ps)

