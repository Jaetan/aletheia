-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Self-certifying ℚ comparators.
--
-- Purpose: `Dec₀` twins of the kernel's hot-path rational comparisons.  Each
--   `does₀` is built from `Rat._≤ᵇ_` (a direct ℤ comparison in MAlonzo — no
--   `Dec` proof cell per call); the erased certificate pins its meaning via
--   the stdlib `≤ᵇ` bridges (`≡` through antisymmetry on normalized ℚ).
-- Consumers: LTL.SignalPredicate.Evaluation (atom comparators),
--   CAN.SignalExtraction (mux selector match).  Lives below both so the
--   certified comparison has one home on either side of the LTL/CAN split.
module Aletheia.Data.Dec0.Rational where

open import Data.Bool using (T; _∧_; not)
open import Data.Product using (proj₁; proj₂)
open import Data.Rational as Rat using (ℚ; _≤ᵇ_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Data.Dec0 using (Dec₀; fromBridges; T-∧→; T-∧←; T-not→; T-not←)

infix 4 _≟ℚ₀_ _≤ℚ₀_ _<ℚ₀_ _>ℚ₀_ _≥ℚ₀_

_≤ℚ₀_ : (x y : ℚ) → Dec₀ (x Rat.≤ y)
x ≤ℚ₀ y = fromBridges (x ≤ᵇ y) ℚP.≤ᵇ⇒≤ ℚP.≤⇒≤ᵇ

_≟ℚ₀_ : (x y : ℚ) → Dec₀ (x ≡ y)
x ≟ℚ₀ y = fromBridges ((x ≤ᵇ y) ∧ (y ≤ᵇ x)) sound complete
  where
    @0 sound : T ((x ≤ᵇ y) ∧ (y ≤ᵇ x)) → x ≡ y
    sound t = ℚP.≤-antisym (ℚP.≤ᵇ⇒≤ (proj₁ (T-∧→ t))) (ℚP.≤ᵇ⇒≤ (proj₂ (T-∧→ t)))

    @0 complete : x ≡ y → T ((x ≤ᵇ y) ∧ (y ≤ᵇ x))
    complete refl =
      T-∧← {x ≤ᵇ x} {x ≤ᵇ x} (ℚP.≤⇒≤ᵇ (ℚP.≤-refl {x})) (ℚP.≤⇒≤ᵇ (ℚP.≤-refl {x}))

_<ℚ₀_ : (x y : ℚ) → Dec₀ (x Rat.< y)
x <ℚ₀ y = fromBridges ((x ≤ᵇ y) ∧ not (y ≤ᵇ x)) sound complete
  where
    @0 sound : T ((x ≤ᵇ y) ∧ not (y ≤ᵇ x)) → x Rat.< y
    sound t = ℚP.≰⇒> (λ y≤x → T-not→ (proj₂ (T-∧→ t)) (ℚP.≤⇒≤ᵇ y≤x))

    @0 complete : x Rat.< y → T ((x ≤ᵇ y) ∧ not (y ≤ᵇ x))
    complete x<y =
      T-∧← (ℚP.≤⇒≤ᵇ (ℚP.<⇒≤ x<y))
           (T-not← (λ t → ℚP.<⇒≢ x<y (ℚP.≤-antisym (ℚP.<⇒≤ x<y) (ℚP.≤ᵇ⇒≤ t))))

_>ℚ₀_ : (x y : ℚ) → Dec₀ (y Rat.< x)
x >ℚ₀ y = y <ℚ₀ x

_≥ℚ₀_ : (x y : ℚ) → Dec₀ (y Rat.≤ x)
x ≥ℚ₀ y = y ≤ℚ₀ x
