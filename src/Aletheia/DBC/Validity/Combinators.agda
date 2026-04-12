{-# OPTIONS --safe --without-K #-}

-- Reusable combinators for DBC check functions and their validity proofs.
--
-- Purpose: Eliminate boilerplate in check definitions (Checks.agda) and
-- check proofs (ErrorChecks, WarningChecks) by capturing common patterns:
--   1. requireDec/rejectDec — decidable check building blocks
--   2. liftConcatMap — per-element sound/complete → concatMap sound/complete
--   3. triangularCheck/liftTriangular — pairwise AllPairs checks
module Aletheia.DBC.Validity.Combinators where

open import Data.List using (List; []; _∷_; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Aletheia.DBC.Validity.ListLemmas using
  ( concatMap-≡[]-sound; concatMap-≡[]-complete
  ; ++-≡[]-split; ++-≡[]-combine )

private
  variable
    A B : Set

-- ============================================================================
-- DECIDABLE CHECK COMBINATORS
-- ============================================================================

-- Returns [] when the decidable property holds (yes branch).
-- Use for checks where "yes" means the signal/message is valid.
-- Example: requireDec (start + len ≤? dlc * 8) issue
requireDec : ∀ {P : Set} → Dec P → B → List B
requireDec (yes _) _ = []
requireDec (no  _) i = i ∷ []

requireDec-sound : ∀ {P : Set} (dec : Dec P) (i : B) →
  requireDec dec i ≡ [] → P
requireDec-sound (yes p) _ _ = p
requireDec-sound (no  _) _ ()

requireDec-complete : ∀ {P : Set} (dec : Dec P) (i : B) →
  P → requireDec dec i ≡ []
requireDec-complete (yes _) _ _ = refl
requireDec-complete (no ¬p) _ p = ⊥-elim (¬p p)

-- Returns [] when the decidable property does NOT hold (no branch).
-- Use for checks where "yes" means the signal/message is invalid.
-- Example: rejectDec (bitLength ≟ 0) issue
rejectDec : ∀ {P : Set} → Dec P → B → List B
rejectDec (yes _) i = i ∷ []
rejectDec (no  _) _ = []

rejectDec-sound : ∀ {P : Set} (dec : Dec P) (i : B) →
  rejectDec dec i ≡ [] → ¬ P
rejectDec-sound (yes _) _ ()
rejectDec-sound (no ¬p) _ _ = ¬p

rejectDec-complete : ∀ {P : Set} (dec : Dec P) (i : B) →
  ¬ P → rejectDec dec i ≡ []
rejectDec-complete (yes p) _ ¬p = ⊥-elim (¬p p)
rejectDec-complete (no  _) _ _  = refl

-- ============================================================================
-- CONCATMAP LIFTING COMBINATORS
-- ============================================================================

-- Lift a per-element sound proof to a concatMap-level All proof.
-- Given: ∀ x → f x ≡ [] → P x
-- Produces: concatMap f xs ≡ [] → All P xs
liftConcatMap-sound : {P : A → Set}
  (f : A → List B) →
  (∀ x → f x ≡ [] → P x) →
  ∀ xs → concatMap f xs ≡ [] → All P xs
liftConcatMap-sound f sound xs eq =
  All.map (λ {x} → sound x) (concatMap-≡[]-sound eq)

-- Lift a per-element complete proof to a concatMap-level proof.
-- Given: ∀ x → P x → f x ≡ []
-- Produces: All P xs → concatMap f xs ≡ []
liftConcatMap-complete : {P : A → Set}
  (f : A → List B) →
  (∀ x → P x → f x ≡ []) →
  ∀ xs → All P xs → concatMap f xs ≡ []
liftConcatMap-complete f complete xs pf =
  concatMap-≡[]-complete (All.map (λ {x} → complete x) pf)

-- ============================================================================
-- TRIANGULAR (PAIRWISE) CHECK COMBINATORS
-- ============================================================================

-- Check element x against every element in a list.
checkAgainst : (A → A → List B) → A → List A → List B
checkAgainst check x = concatMap (check x)

-- Check all pairs in a list (triangular: each element against all later ones).
triangularCheck : (A → A → List B) → List A → List B
triangularCheck _ [] = []
triangularCheck check (x ∷ xs) = checkAgainst check x xs ++ₗ triangularCheck check xs

-- Lift pairwise sound proof to triangular AllPairs proof.
liftTriangular-sound : {R : A → A → Set}
  (check : A → A → List B)
  (pair-sound : ∀ x y → check x y ≡ [] → R x y) →
  ∀ xs → triangularCheck check xs ≡ [] → AllPairs R xs
liftTriangular-sound _ _ [] _ = []
liftTriangular-sound check sound (x ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in liftConcatMap-sound (check x) (sound x) rest eq₁ ∷
     liftTriangular-sound check sound rest eq₂

-- Lift pairwise complete proof to triangular proof.
liftTriangular-complete : {R : A → A → Set}
  (check : A → A → List B)
  (pair-complete : ∀ x y → R x y → check x y ≡ []) →
  ∀ xs → AllPairs R xs → triangularCheck check xs ≡ []
liftTriangular-complete _ _ [] [] = refl
liftTriangular-complete check complete (x ∷ rest) (px ∷ prest) =
  ++-≡[]-combine (liftConcatMap-complete (check x) (complete x) rest px)
                 (liftTriangular-complete check complete rest prest)
