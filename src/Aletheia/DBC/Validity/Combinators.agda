{-# OPTIONS --safe --without-K #-}

-- Reusable combinators for lifting per-element check proofs to list-level proofs.
--
-- Purpose: Eliminate boilerplate in ErrorChecks/WarningChecks by capturing the
-- common pattern: per-element sound/complete → concatMap sound/complete.
-- Role: Used by ErrorChecks.agda and WarningChecks.agda.
module Aletheia.DBC.Validity.Combinators where

open import Data.List using (List; []; concatMap)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Aletheia.DBC.Validity.ListLemmas using
  ( concatMap-≡[]-sound; concatMap-≡[]-complete; All-map )

private
  variable
    A B : Set

-- Lift a per-element sound proof to a concatMap-level All proof.
-- Given: ∀ x → f x ≡ [] → P x
-- Produces: concatMap f xs ≡ [] → All P xs
liftConcatMap-sound : {P : A → Set}
  (f : A → List B) →
  (∀ x → f x ≡ [] → P x) →
  ∀ xs → concatMap f xs ≡ [] → All P xs
liftConcatMap-sound f sound xs eq =
  All-map (λ x → sound x) (concatMap-≡[]-sound eq)

-- Lift a per-element complete proof to a concatMap-level proof.
-- Given: ∀ x → P x → f x ≡ []
-- Produces: All P xs → concatMap f xs ≡ []
liftConcatMap-complete : {P : A → Set}
  (f : A → List B) →
  (∀ x → P x → f x ≡ []) →
  ∀ xs → All P xs → concatMap f xs ≡ []
liftConcatMap-complete f complete xs pf =
  concatMap-≡[]-complete (All-map (λ x → complete x) pf)
