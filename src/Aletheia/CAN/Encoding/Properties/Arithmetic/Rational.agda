-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The floor of an integer taken as a rational is the integer itself.
--
-- Purpose: the one rounding fact the encoding proofs need (a value scaled
--   out of an exact raw value is that raw value as a rational, and its floor
--   is the raw value), proved through the canonical embedding `fromℤ`, whose
--   normalization lemma `z/1≡fromℤ` lives with the raw range's arithmetic.
module Aletheia.CAN.Encoding.Properties.Arithmetic.Rational where

open import Aletheia.CAN.Encoding.Arithmetic.Range using (z/1≡fromℤ)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.DivMod as ℕ using ()
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Integer.DivMod as ℤ using ()
open import Data.Rational using (floor) renaming (_/_ to _/ᵣ_)
open import Data.Rational.Literals using (fromℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

floor-fromℤ : ∀ (z : ℤ) → floor (fromℤ z) ≡ z
floor-fromℤ (+ n) = trans (ℤ.div-pos-is-/ℕ (+ n) 1) (cong +_ (ℕ.n/1≡n n))
floor-fromℤ -[1+ n ] with ℕ.n%1≡0 (ℕ.suc n)
... | eq =
  trans (ℤ.div-pos-is-/ℕ (-[1+ n ]) 1)
        (aux eq)
  where
    aux : ℕ.suc n ℕ.% 1 ≡ 0 → (-[1+ n ]) ℤ./ℕ 1 ≡ -[1+ n ]
    aux eq rewrite eq | ℕ.n/1≡n (ℕ.suc n) = refl

floor-int : ∀ (z : ℤ) → floor (z /ᵣ 1) ≡ z
floor-int z = trans (cong floor (z/1≡fromℤ z)) (floor-fromℤ z)
