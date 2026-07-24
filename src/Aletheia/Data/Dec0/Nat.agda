-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Self-certifying ℕ equality.
--
-- Purpose: the `Dec₀` twin of `_≡ᵇ_` — `does₀` is the builtin ℕ comparison
--   (a constant-time Integer op in MAlonzo); the erased certificate pins it
--   to propositional equality via the stdlib bridges.
-- Consumers: the bit-membership twins in DBC.Decidable.Disjointness.
module Aletheia.Data.Dec0.Nat where

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Aletheia.Data.Dec0 using (Dec₀; fromBridges)

infix 4 _≟ℕ₀_

_≟ℕ₀_ : (m n : ℕ) → Dec₀ (m ≡ n)
m ≟ℕ₀ n = fromBridges (m ≡ᵇ n) (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n)
