-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A number within the kernel's component bound: a natural at most
-- `max-rational-component-magnitude`, a `DecRat` whose reduced numerator
-- and denominator both are.  The load-time bound walk decides these for
-- every numeric field of a DBC, and the text round-trip proofs take them
-- as their premise: a literal within the bound reads back exactly, one
-- past it is refused at load.
module Aletheia.DBC.DecRat.Magnitude where

open import Data.Integer using (ℤ; ∣_∣)
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; _⊔_; _⊔′_; _*_; _^_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; ≤ᵇ⇒≤; ⊔-lub; ⊔≡⊔′)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRat; intDecRatToℤ; NatDecRat; mkNatDecRat; natDecRatToℕ; mkIntDecRatFromℤ)
open import Data.Nat using (zero; suc)
open import Data.Integer using (+_; -[1+_])
open import Aletheia.Limits using (max-rational-component-magnitude)

SmallNat : ℕ → Set
SmallNat n = n ≤ max-rational-component-magnitude

SmallInt : ℤ → Set
SmallInt z = SmallNat ∣ z ∣

-- The larger component of a value: what a refusal reports as observed.
largerComponent : DecRat → ℕ
largerComponent (mkDecRat num a b _) = ∣ num ∣ ⊔′ (2 ^ a * 5 ^ b)

SmallDecRat : DecRat → Set
SmallDecRat d = SmallNat (largerComponent d)

-- Both components of a value whose larger component is within a bound are.
components-≤ : ∀ {bound} d → largerComponent d ≤ bound →
  ∣ DecRat.numerator d ∣ ≤ bound × 2 ^ DecRat.twoExp d * 5 ^ DecRat.fiveExp d ≤ bound
components-≤ {bound} (mkDecRat num a b _) small =
  ≤-trans (m≤m⊔n ∣ num ∣ (2 ^ a * 5 ^ b)) small′ , ≤-trans (m≤n⊔m ∣ num ∣ (2 ^ a * 5 ^ b)) small′
  where
    small′ : ∣ num ∣ ⊔ (2 ^ a * 5 ^ b) ≤ bound
    small′ = subst (_≤ bound) (sym (⊔≡⊔′ ∣ num ∣ (2 ^ a * 5 ^ b))) small

-- Both components of a small value are within the component bound.
smallDecRat-components : ∀ d → SmallDecRat d →
  SmallNat ∣ DecRat.numerator d ∣ × SmallNat (2 ^ DecRat.twoExp d * 5 ^ DecRat.fiveExp d)
smallDecRat-components = components-≤

-- A number the type-checker can compare with the bound outright, such
-- as a literal the grammar fixes.
smallNat-by-eval : ∀ n → T (n ≤ᵇ max-rational-component-magnitude) → SmallNat n
smallNat-by-eval n = ≤ᵇ⇒≤ n max-rational-component-magnitude

-- A refined integer's magnitude is its value's numerator, so a value within
-- a bound gives an integer within it.
intDecRat-≤ : ∀ {bound} v → largerComponent (IntDecRat.value v) ≤ bound → ∣ intDecRatToℤ v ∣ ≤ bound
intDecRat-≤ (mkIntDecRat (mkDecRat z zero zero c) _) small =
  proj₁ (components-≤ (mkDecRat z zero zero c) small)
intDecRat-≤ (mkIntDecRat (mkDecRat _ zero    (suc _) _) ()) _
intDecRat-≤ (mkIntDecRat (mkDecRat _ (suc _) _       _) ()) _

natDecRat-≤ : ∀ {bound} v → largerComponent (NatDecRat.value v) ≤ bound → natDecRatToℕ v ≤ bound
natDecRat-≤ (mkNatDecRat (mkDecRat (+ n) zero zero c) _) small =
  proj₁ (components-≤ (mkDecRat (+ n) zero zero c) small)
natDecRat-≤ (mkNatDecRat (mkDecRat (+ _) zero    (suc _) _) ()) _
natDecRat-≤ (mkNatDecRat (mkDecRat (+ _) (suc _) _       _) ()) _
natDecRat-≤ (mkNatDecRat (mkDecRat -[1+ _ ] _ _ _) ()) _

intDecRat-small : ∀ v → SmallDecRat (IntDecRat.value v) → SmallInt (intDecRatToℤ v)
intDecRat-small = intDecRat-≤

natDecRat-small : ∀ v → SmallDecRat (NatDecRat.value v) → SmallNat (natDecRatToℕ v)
natDecRat-small = natDecRat-≤

-- A small integer lifted to a refined integer is a small value: its
-- denominator is 1.
fromℤ-small : ∀ z → SmallInt z → SmallDecRat (IntDecRat.value (mkIntDecRatFromℤ z))
fromℤ-small (+ zero)  small = subst (_≤ max-rational-component-magnitude) (⊔≡⊔′ 0 1) (⊔-lub small (smallNat-by-eval 1 tt))
fromℤ-small (+ suc n) small = subst (_≤ max-rational-component-magnitude) (⊔≡⊔′ (suc n) 1) (⊔-lub small (smallNat-by-eval 1 tt))
fromℤ-small -[1+ n ]  small = subst (_≤ max-rational-component-magnitude) (⊔≡⊔′ (suc n) 1) (⊔-lub small (smallNat-by-eval 1 tt))
