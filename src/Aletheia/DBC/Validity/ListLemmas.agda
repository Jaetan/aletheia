{-# OPTIONS --safe --without-K #-}

-- List lemmas for DBC validity proofs.
--
-- Purpose: Reusable lemmas connecting list operations (++, concatMap)
-- to propositional emptiness (≡ []) and All predicates.
module Aletheia.DBC.Validity.ListLemmas where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

private
  variable
    A B : Set

-- ============================================================================
-- APPEND AND EMPTINESS
-- ============================================================================

-- If xs ++ ys ≡ [], then xs ≡ []
++-≡[]-left : {xs ys : List A} → xs ++ ys ≡ [] → xs ≡ []
++-≡[]-left {xs = []}    _  = refl
++-≡[]-left {xs = _ ∷ _} ()

-- If xs ++ ys ≡ [], then ys ≡ []
++-≡[]-right : {xs ys : List A} → xs ++ ys ≡ [] → ys ≡ []
++-≡[]-right {xs = []}    eq = eq
++-≡[]-right {xs = _ ∷ _} ()

-- If xs ++ ys ≡ [], then both are []
++-≡[]-split : {xs ys : List A} → xs ++ ys ≡ [] → xs ≡ [] × ys ≡ []
++-≡[]-split eq = ++-≡[]-left eq , ++-≡[]-right eq

-- If both are [], then xs ++ ys ≡ []
++-≡[]-combine : {xs ys : List A} → xs ≡ [] → ys ≡ [] → xs ++ ys ≡ []
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
-- ALL MAPPING (convert between equivalent All predicates)
-- ============================================================================

All-map : {P Q : A → Set} → (∀ x → P x → Q x) → ∀ {xs} → All P xs → All Q xs
All-map f []       = []
All-map f (p ∷ ps) = f _ p ∷ All-map f ps

All-map⁻ : {P Q : A → Set} → (∀ x → Q x → P x) → ∀ {xs} → All Q xs → All P xs
All-map⁻ f []       = []
All-map⁻ f (q ∷ qs) = f _ q ∷ All-map⁻ f qs

-- AllPairs mapping
AllPairs-map : {R S : A → A → Set} →
  (∀ x y → R x y → S x y) → ∀ {xs} → AllPairs R xs → AllPairs S xs
AllPairs-map f []       = []
AllPairs-map f (px ∷ pxs) = All-map (λ y → f _ y) px ∷ AllPairs-map f pxs

AllPairs-map⁻ : {R S : A → A → Set} →
  (∀ x y → S x y → R x y) → ∀ {xs} → AllPairs S xs → AllPairs R xs
AllPairs-map⁻ f []       = []
AllPairs-map⁻ f (px ∷ pxs) = All-map (λ y → f _ y) px ∷ AllPairs-map⁻ f pxs
