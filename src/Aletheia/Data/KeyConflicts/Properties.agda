-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- `keyConflicts` reports nothing exactly when no two elements with different
-- tags share a key.
--
-- The elements are sorted by (key, tag, position) and split into runs of
-- equal keys; a run is reported when two neighbours in it conflict.  So the
-- result is empty exactly when no two neighbours of the sorted list conflict
-- (`anyAdjacentConflict`).  In a sorted list every key between two equal keys
-- is equal to them, so no neighbours conflicting means no two elements
-- conflicting; and the sorted list is a permutation of the input, which
-- carries the property back, the relation being symmetric.
module Aletheia.Data.KeyConflicts.Properties where

open import Aletheia.Data.KeyConflicts using (module Keyed)

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (∨-assoc)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.NonEmpty using (List⁺; _∷_; head; toList)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-sym) renaming (refl to ↭-refl; prep to ↭-prep; swap to ↭-swap; trans to ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (All-resp-↭; ↭-length)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.List.Relation.Unary.Linked.Properties using (AllPairs⇒Linked; Linked⇒All)
open import Data.Nat using (ℕ; _≟_; _≡ᵇ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

import Data.List.Relation.Binary.Lex.NonStrict as Lex
import Data.List.Sort.MergeSort.Base as MergeSort
import Data.List.Sort.MergeSort.Properties as MergeSortₚ

-- ============================================================================
-- Sorting facts, for any order
-- ============================================================================

-- Sorting keeps the length, so it empties only the empty list.
sort-≡[] : ∀ {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) xs → MergeSort.sort O xs ≡ [] → xs ≡ []
sort-≡[] O []       _  = refl
sort-≡[] O (x ∷ xs) eq with trans (sym (cong length eq)) (↭-length (MergeSortₚ.sort-↭ O (x ∷ xs)))
... | ()

-- A symmetric relation holding between every two elements survives a permutation.
AllPairs-resp-↭ : ∀ {A : Set} {R : A → A → Set} → (∀ {x y} → R x y → R y x)
  → ∀ {xs ys} → xs ↭ ys → AllPairs R xs → AllPairs R ys
AllPairs-resp-↭ sym′ ↭-refl          pxs = pxs
AllPairs-resp-↭ sym′ (↭-prep x p)    (px ∷ pxs) = All-resp-↭ p px ∷ AllPairs-resp-↭ sym′ p pxs
AllPairs-resp-↭ sym′ (↭-swap x y p)  ((rxy ∷ rxs) ∷ rys ∷ pxs) =
  (sym′ rxy ∷ All-resp-↭ p rys) ∷ All-resp-↭ p rxs ∷ AllPairs-resp-↭ sym′ p pxs
AllPairs-resp-↭ sym′ (↭-trans p q)   pxs = AllPairs-resp-↭ sym′ q (AllPairs-resp-↭ sym′ p pxs)

private
  ∨-false : ∀ x y → x ∨ y ≡ false → x ≡ false × y ≡ false
  ∨-false false y eq = refl , eq
  ∨-false true  y ()

  module LO = DecTotalOrder (Lex.≤-decTotalOrder ℕₚ.≤-decTotalOrder)

-- ============================================================================
-- The emptiness theorem
-- ============================================================================

module _ {E : Set} (key : E → List ℕ) (tag : E → ℕ) (pos : E → ℕ) where
  open Keyed key tag pos

  -- Two elements do not conflict: sharing a key, they share a tag.
  NoConflict : E → E → Set
  NoConflict a b = key a ≡ key b → tag a ≡ tag b

  private
    _≤ₑ_ : E → E → Set
    _≤ₑ_ = DecTotalOrder._≤_ elementOrder

    noConflict-sym : ∀ {a b} → NoConflict a b → NoConflict b a
    noConflict-sym nc k = sym (nc (sym k))

    conflictᵇ-false⇒ : ∀ a b → conflictᵇ a b ≡ false → NoConflict a b
    conflictᵇ-false⇒ a b eq k with ≡-dec _≟_ (key a) (key b) | tag a ≡ᵇ tag b in tq
    conflictᵇ-false⇒ a b eq k | yes _ | true  = ℕₚ.≡ᵇ⇒≡ (tag a) (tag b) (subst T (sym tq) _)
    conflictᵇ-false⇒ a b () k | yes _ | false
    conflictᵇ-false⇒ a b eq k | no ¬k | _     = ⊥-elim (¬k k)

    ⇒conflictᵇ-false : ∀ a b → NoConflict a b → conflictᵇ a b ≡ false
    ⇒conflictᵇ-false a b nc with ≡-dec _≟_ (key a) (key b) | tag a ≡ᵇ tag b in tq
    ... | yes _ | true  = refl
    ... | yes k | false = ⊥-elim (subst T tq (ℕₚ.≡⇒≡ᵇ (tag a) (tag b) (nc k)))
    ... | no  _ | _     = refl

    -- Whether some run holds a conflict.
    anyRuns : List (List⁺ E) → Bool
    anyRuns []       = false
    anyRuns (g ∷ gs) = anyAdjacentConflict (toList g) ∨ anyRuns gs

    -- Adding an element puts it at the head of the first run.
    joinOrStart-shape : ∀ b y g gs → Σ (List E) λ t → Σ (List (List⁺ E)) λ gs′ →
                        joinOrStart b y g gs ≡ (y ∷ t) ∷ gs′
    joinOrStart-shape true  y g gs = toList g , gs , refl
    joinOrStart-shape false y g gs = [] , g ∷ gs , refl

    addToRuns-shape : ∀ y rs → Σ (List E) λ t → Σ (List (List⁺ E)) λ gs′ →
                      addToRuns y rs ≡ (y ∷ t) ∷ gs′
    addToRuns-shape y []       = [] , [] , refl
    addToRuns-shape y (g ∷ gs) = joinOrStart-shape (sameKeyᵇ y (head g)) y g gs

    -- `x` before a run headed by `y`: joining it adds the pair (x, y) to the
    -- run; starting a run means their keys differ, so they do not conflict.
    join-step : ∀ x y t gs b → sameKeyᵇ x y ≡ b →
      conflictᵇ x y ∨ (anyAdjacentConflict (y ∷ t) ∨ anyRuns gs)
        ≡ anyRuns (joinOrStart b x (y ∷ t) gs)
    join-step x y t gs true  _  = sym (∨-assoc (conflictᵇ x y) (anyAdjacentConflict (y ∷ t)) (anyRuns gs))
    join-step x y t gs false sk =
      cong (λ s → (s ∧ not (tag x ≡ᵇ tag y)) ∨ (anyAdjacentConflict (y ∷ t) ∨ anyRuns gs)) sk

    cons-step : ∀ x y xs
      → (Σ (List E) λ t → Σ (List (List⁺ E)) λ gs → addToRuns y (runs xs) ≡ (y ∷ t) ∷ gs)
      → anyAdjacentConflict (y ∷ xs) ≡ anyRuns (runs (y ∷ xs))
      → anyAdjacentConflict (x ∷ y ∷ xs) ≡ anyRuns (runs (x ∷ y ∷ xs))
    cons-step x y xs (t , gs , eq) ih =
      trans (cong (conflictᵇ x y ∨_) (trans ih (cong anyRuns eq)))
            (trans (join-step x y t gs (sameKeyᵇ x y) refl)
                   (sym (cong (λ r → anyRuns (addToRuns x r)) eq)))

    -- The runs hold a conflict exactly when two neighbours do.
    anyAdj≡anyRuns : ∀ ys → anyAdjacentConflict ys ≡ anyRuns (runs ys)
    anyAdj≡anyRuns []           = refl
    anyAdj≡anyRuns (x ∷ [])     = refl
    anyAdj≡anyRuns (x ∷ y ∷ xs) =
      cons-step x y xs (addToRuns-shape y (runs xs)) (anyAdj≡anyRuns (y ∷ xs))

    keepIf-≡[] : ∀ b g rest → keepIf b g rest ≡ [] → b ≡ false × rest ≡ []
    keepIf-≡[] false _ _ eq = refl , eq
    keepIf-≡[] true  _ _ ()

    keepIf-false : ∀ {b} g rest → b ≡ false → keepIf b g rest ≡ rest
    keepIf-false _ _ refl = refl

    conflictingRuns-≡[] : ∀ gs → conflictingRuns gs ≡ [] → anyRuns gs ≡ false
    conflictingRuns-≡[] []       _  = refl
    conflictingRuns-≡[] (g ∷ gs) eq with keepIf-≡[] (anyAdjacentConflict (toList g)) g (conflictingRuns gs) eq
    ... | b≡f , rest≡[] = trans (cong (_∨ anyRuns gs) b≡f) (conflictingRuns-≡[] gs rest≡[])

    anyRuns-false⇒ : ∀ gs → anyRuns gs ≡ false → conflictingRuns gs ≡ []
    anyRuns-false⇒ []       _  = refl
    anyRuns-false⇒ (g ∷ gs) eq with ∨-false (anyAdjacentConflict (toList g)) (anyRuns gs) eq
    ... | b≡f , rest≡f = trans (keepIf-false g (conflictingRuns gs) b≡f) (anyRuns-false⇒ gs rest≡f)

    -- In the element order, keys never decrease.
    keyLe : ∀ {a b} → a ≤ₑ b → LO._≤_ (key a) (key b)
    keyLe (inj₁ (le , _)) = le
    keyLe (inj₂ (eq , _)) = LO.reflexive eq

    -- A key between two equal keys equals them.
    squeeze : ∀ {a b c} → a ≤ₑ b → b ≤ₑ c → key a ≡ key c → key b ≡ key a
    squeeze a≤b b≤c ka≡kc =
      Pointwise-≡⇒≡ (LO.antisym (subst (LO._≤_ _) (sym ka≡kc) (keyLe b≤c)) (keyLe a≤b))

    zLeRest : ∀ {z rest} → Linked _≤ₑ_ (z ∷ rest) → All (z ≤ₑ_) rest
    zLeRest [-]        = []
    zLeRest (z≤w ∷ lw) = Linked⇒All (DecTotalOrder.trans elementOrder) z≤w lw

    -- `y` before `z` in a sorted list, not conflicting with it, conflicts
    -- with nothing `z` does not conflict with.
    beyond : ∀ {y z rest} → y ≤ₑ z → NoConflict y z
      → All (z ≤ₑ_) rest → All (NoConflict z) rest → All (NoConflict y) rest
    beyond _   _    []          []          = []
    beyond y≤z ncyz (z≤w ∷ zws) (nczw ∷ ns) =
      (λ kyw → let kzy = squeeze y≤z z≤w kyw
               in trans (ncyz (sym kzy)) (nczw (trans kzy kyw)))
      ∷ beyond y≤z ncyz zws ns

    sorted-noConflict : ∀ {ys} → Linked _≤ₑ_ ys → anyAdjacentConflict ys ≡ false
      → AllPairs NoConflict ys
    sorted-noConflict []  _ = []
    sorted-noConflict [-] _ = [] ∷ []
    sorted-noConflict {y ∷ z ∷ rest} (y≤z ∷ lz) eq
      with ∨-false (conflictᵇ y z) (anyAdjacentConflict (z ∷ rest)) eq
    ... | cyz , eq′ with sorted-noConflict lz eq′
    ...   | ih@(ncz ∷ _) =
      (conflictᵇ-false⇒ y z cyz ∷ beyond y≤z (conflictᵇ-false⇒ y z cyz) (zLeRest lz) ncz) ∷ ih

    linked-noConflict : ∀ {ys} → Linked NoConflict ys → anyAdjacentConflict ys ≡ false
    linked-noConflict []  = refl
    linked-noConflict [-] = refl
    linked-noConflict {a ∷ b ∷ rest} (nab ∷ l) =
      trans (cong (_∨ anyAdjacentConflict (b ∷ rest)) (⇒conflictᵇ-false a b nab)) (linked-noConflict l)

  keyConflicts-sound : ∀ es → keyConflicts es ≡ [] → AllPairs NoConflict es
  keyConflicts-sound es eq =
    AllPairs-resp-↭ noConflict-sym (MergeSortₚ.sort-↭ elementOrder es)
      (sorted-noConflict (MergeSortₚ.sort-↗ elementOrder es)
        (trans (anyAdj≡anyRuns sorted)
               (conflictingRuns-≡[] (runs sorted) (sort-≡[] groupOrder _ eq))))
    where sorted = MergeSort.sort elementOrder es

  keyConflicts-complete : ∀ es → AllPairs NoConflict es → keyConflicts es ≡ []
  keyConflicts-complete es ap =
    cong (MergeSort.sort groupOrder)
      (anyRuns-false⇒ (runs sorted)
        (trans (sym (anyAdj≡anyRuns sorted))
               (linked-noConflict (AllPairs⇒Linked
                 (AllPairs-resp-↭ noConflict-sym (↭-sym (MergeSortₚ.sort-↭ elementOrder es)) ap)))))
    where sorted = MergeSort.sort elementOrder es
