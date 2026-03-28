{-# OPTIONS --safe --without-K #-}

-- List lemmas for DBC validity proofs.
--
-- Purpose: Reusable lemmas connecting list operations (++, concatMap)
-- to propositional emptiness (≡ []) and All predicates.
module Aletheia.DBC.Validity.ListLemmas where

open import Data.List using (List; []; _∷_; _++_; concatMap; map; filter)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
-- ALL OVER APPEND AND CONCATMAP
-- ============================================================================

-- concatMap preserves All P (general form)
All-concatMap : {P : B → Set} {f : A → List B} {xs : List A} →
  All (λ x → All P (f x)) xs → All P (concatMap f xs)
All-concatMap []       = []
All-concatMap (p ∷ ps) = ++⁺ p (All-concatMap ps)

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

-- ============================================================================
-- MAP AND EMPTINESS
-- ============================================================================

-- If map f xs ≡ [], then xs ≡ []
map-[]-inv : (f : A → B) (xs : List A) → map f xs ≡ [] → xs ≡ []
map-[]-inv f []      _  = refl
map-[]-inv f (_ ∷ _) ()

-- ============================================================================
-- FILTER AND ALL
-- ============================================================================

-- If filter returns [], then P doesn't hold for any element
filter-[]-sound : {P : A → Set} (P? : ∀ x → Dec (P x)) (xs : List A) →
  filter P? xs ≡ [] → All (λ x → ¬ (P x)) xs
filter-[]-sound P? [] _ = []
filter-[]-sound P? (x ∷ xs) eq with P? x
filter-[]-sound P? (x ∷ xs) () | yes _
filter-[]-sound P? (x ∷ xs) eq | no ¬p = ¬p ∷ filter-[]-sound P? xs eq

-- If P doesn't hold for any element, filter returns []
filter-[]-complete : {P : A → Set} (P? : ∀ x → Dec (P x)) (xs : List A) →
  All (λ x → ¬ (P x)) xs → filter P? xs ≡ []
filter-[]-complete P? [] [] = refl
filter-[]-complete P? (x ∷ xs) (¬p ∷ rest) with P? x
... | yes p = ⊥-elim (¬p p)
... | no  _ = filter-[]-complete P? xs rest
