-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Groups of elements that share a key under different tags, found in time
-- O(N log N).  Each element carries a key, a tag and a position; the elements
-- are sorted by (key, tag, position), each run of equal keys is a group, and
-- a group is reported when two of its elements carry different tags.  The
-- reported groups come in the order of their first element's position, and
-- each keeps its elements in (tag, position) order.
--
-- The validator uses it with a message's position as the tag, so any two
-- messages sharing a key conflict, and with the message holding a signal as
-- the tag, so a name repeated inside one message is no conflict.
-- `Aletheia.Data.KeyConflicts.Properties` proves the result is empty exactly
-- when no two elements with different tags share a key.
module Aletheia.Data.KeyConflicts where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; head; toList)
open import Data.List.Properties using (≡-dec)
open import Data.Nat using (ℕ; _≟_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-decTotalOrder)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Nullary using (does)

import Data.List.Relation.Binary.Lex.NonStrict as Lex
import Data.List.Sort.MergeSort.Base as MergeSort
import Data.Product.Relation.Binary.Lex.NonStrict as ×Lex
import Relation.Binary.Construct.On as On

-- Key, tag and position, ordered lexicographically.
keyTagPosOrder : DecTotalOrder _ _ _
keyTagPosOrder =
  ×Lex.×-decTotalOrder (Lex.≤-decTotalOrder ≤-decTotalOrder)
                       (×Lex.×-decTotalOrder ≤-decTotalOrder ≤-decTotalOrder)

-- Everything about elements of one type, keyed, tagged and positioned.
module Keyed {E : Set} (key : E → List ℕ) (tag : E → ℕ) (pos : E → ℕ) where

  -- The elements' order: by key, then tag, then position.
  elementOrder : DecTotalOrder _ _ _
  elementOrder = On.decTotalOrder keyTagPosOrder (λ e → key e , tag e , pos e)

  -- The groups' order: by their first element's position.
  groupOrder : DecTotalOrder _ _ _
  groupOrder = On.decTotalOrder ≤-decTotalOrder (pos ∘ head)

  sameKeyᵇ : E → E → Bool
  sameKeyᵇ a b = does (≡-dec _≟_ (key a) (key b))

  -- Two elements conflict when they share a key under different tags.
  conflictᵇ : E → E → Bool
  conflictᵇ a b = sameKeyᵇ a b ∧ not (tag a ≡ᵇ tag b)

  -- Whether some two neighbours in a list conflict.
  anyAdjacentConflict : List E → Bool
  anyAdjacentConflict []             = false
  anyAdjacentConflict (_ ∷ [])       = false
  anyAdjacentConflict (a ∷ b ∷ rest) = conflictᵇ a b ∨ anyAdjacentConflict (b ∷ rest)

  -- `x` joins the first run when it shares that run's key, else starts one.
  joinOrStart : Bool → E → List⁺ E → List (List⁺ E) → List (List⁺ E)
  joinOrStart true  x g gs = (x ∷⁺ g) ∷ gs
  joinOrStart false x g gs = (x ∷ []) ∷ g ∷ gs

  addToRuns : E → List (List⁺ E) → List (List⁺ E)
  addToRuns x []       = (x ∷ []) ∷ []
  addToRuns x (g ∷ gs) = joinOrStart (sameKeyᵇ x (head g)) x g gs

  -- The maximal runs of neighbours sharing a key.
  runs : List E → List (List⁺ E)
  runs []       = []
  runs (x ∷ xs) = addToRuns x (runs xs)

  keepIf : Bool → List⁺ E → List (List⁺ E) → List (List⁺ E)
  keepIf true  g gs = g ∷ gs
  keepIf false _ gs = gs

  -- The runs holding a conflict.
  conflictingRuns : List (List⁺ E) → List (List⁺ E)
  conflictingRuns []       = []
  conflictingRuns (g ∷ gs) = keepIf (anyAdjacentConflict (toList g)) g (conflictingRuns gs)

  keyConflicts : List E → List (List⁺ E)
  keyConflicts es =
    MergeSort.sort groupOrder (conflictingRuns (runs (MergeSort.sort elementOrder es)))

  -- A group with one element per tag, the first of each, in tag order.
  firstPerTag : List⁺ E → List⁺ E
  firstPerTag (x ∷ xs) = x ∷ go x xs
    where
      go : E → List E → List E
      go _    []       = []
      go prev (y ∷ ys) with tag prev ≡ᵇ tag y
      ... | true  = go prev ys
      ... | false = y ∷ go y ys
