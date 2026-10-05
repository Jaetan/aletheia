-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The arithmetic of the raw range: rational, integer and natural facts only,
-- with no signal and no frame.
--
-- An integer raw value fits n bits (`RawFits`): a natural below 2^n when
-- unsigned, an n-bit two's complement value when signed; its unsigned
-- representation is then below 2^n (`RawFits-implies-bounded`).  A raw value
-- whose scaled image lies between the scaled images of the n-bit range's ends
-- lies between those ends, and so fits n bits (`scaledRawFits`), whatever the
-- sign of the non-zero factor.
--
-- DEFER-stdlib-mandate (Cat 29): the stdlib's `*-cancelʳ-≤-pos` / `-neg` take
-- `.{{_ : Positive r}}` / `.{{_ : Negative r}}` instance arguments.
-- `scaledBetween` matches the factor's numerator first, so each witness is
-- the unit, which its call site supplies explicitly as `{{_}}`.
module Aletheia.CAN.Encoding.Arithmetic.Range where

open import Aletheia.CAN.Encoding.Arithmetic using (fromSigned; applyScaling; rawRange; orderBySign)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; +≤+; -≤-)
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; zero; suc; _<_; _>_; _^_; _∸_; pred; s≤s; z≤n)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; mkℚ; _≤_)
  renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_)
open import Data.Rational.Literals using (fromℤ)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; subst; subst₂)

-- ============================================================================
-- FITTING n BITS
-- ============================================================================

-- An integer fits n bits as a two's complement value.
SignedFits : ℤ → ℕ → Set
SignedFits (+ n)    bitLength = n < 2 ^ (bitLength ∸ 1)
SignedFits -[1+ n ] bitLength = suc n ℕ.≤ 2 ^ (bitLength ∸ 1)

data RawFits (raw : ℤ) (bitLength : ℕ) : Bool → Set where
  unsigned-fits : ∀ {n} → raw ≡ + n → n < 2 ^ bitLength → RawFits raw bitLength false
  signed-fits   : SignedFits raw bitLength → RawFits raw bitLength true

-- Half the n-bit range lies below the whole of it.
half<full : ∀ bl → bl > 0 → 2 ^ (bl ∸ 1) < 2 ^ bl
half<full (suc bl) _ = ℕP.^-monoʳ-< 2 (s≤s (s≤s z≤n)) (ℕP.n<1+n bl)

SignedFits-implies-fromSigned-bounded : ∀ (raw : ℤ) (bitLength : ℕ)
  → bitLength > 0
  → SignedFits raw bitLength
  → fromSigned raw bitLength < 2 ^ bitLength
SignedFits-implies-fromSigned-bounded (+ n) bitLength bl>0 n<half =
  ℕP.<-trans n<half (half<full bitLength bl>0)
SignedFits-implies-fromSigned-bounded -[1+ n ] bitLength _ _ =
  m∸sucn<m (2 ^ bitLength) n (ℕP.m^n>0 2 bitLength)
  where
    m∸sucn<m : ∀ m n → m > 0 → m ∸ suc n < m
    m∸sucn<m (suc m) n _ = s≤s (ℕP.m∸n≤m m n)

RawFits-implies-bounded : ∀ (raw : ℤ) (bitLength : ℕ) (isSigned : Bool)
  → bitLength > 0
  → RawFits raw bitLength isSigned
  → fromSigned raw bitLength < 2 ^ bitLength
RawFits-implies-bounded .(+ n) _ false _ (unsigned-fits {n} refl n<2^bl) = n<2^bl
RawFits-implies-bounded raw bitLength true bl>0 (signed-fits sf) =
  SignedFits-implies-fromSigned-bounded raw bitLength bl>0 sf

-- ============================================================================
-- BETWEEN THE ENDS
-- ============================================================================

-- `raw / 1` is the canonical embedding, whose numerator is `raw` itself.
z/1≡fromℤ : ∀ (z : ℤ) → z /ᵣ 1 ≡ fromℤ z
z/1≡fromℤ (+ n)    = trans (ℚP.normalize-coprime (coprime-sym (1-coprimeTo n))) (ℚP.mkℚ-cong refl refl)
z/1≡fromℤ -[1+ n ] = trans (cong -ᵣ_ (ℚP.normalize-coprime (coprime-sym (1-coprimeTo (suc n)))))
                           (ℚP.mkℚ-cong refl refl)

private
  fromℤ-cancel-≤ : ∀ {i j} → fromℤ i ≤ fromℤ j → i ℤ.≤ j
  fromℤ-cancel-≤ {i} {j} le = subst₂ ℤ._≤_ (ℤP.*-identityʳ i) (ℤP.*-identityʳ j) (ℚP.drop-*≤* le)

  +-cancelʳ-≤ : ∀ o {x y : ℚ} → x +ᵣ o ≤ y +ᵣ o → x ≤ y
  +-cancelʳ-≤ o {x} {y} le = subst₂ _≤_ (cancel x) (cancel y) (ℚP.+-monoˡ-≤ (-ᵣ o) le)
    where
      cancel : ∀ z → (z +ᵣ o) +ᵣ -ᵣ o ≡ z
      cancel z = trans (ℚP.+-assoc z o (-ᵣ o)) (trans (cong (z +ᵣ_) (ℚP.+-inverseʳ o)) (ℚP.+-identityʳ z))

  ≤pred⇒< : ∀ {k m} → 0 < m → k ℕ.≤ pred m → k < m
  ≤pred⇒< {m = suc _} _ k≤ = s≤s k≤

-- A value scaled from r by a non-zero factor lies between the scaled images
-- of lo and hi only if r lies between lo and hi: dropping the offset keeps
-- the order, dividing by a positive factor keeps it, by a negative factor
-- reverses it, which `orderBySign` has already undone.
scaledBetween : ∀ (f o lo hi r : ℚ) → f ≢ 0ℚ
  → proj₁ (orderBySign f (lo *ᵣ f +ᵣ o) (hi *ᵣ f +ᵣ o)) ≤ r *ᵣ f +ᵣ o
  → r *ᵣ f +ᵣ o ≤ proj₂ (orderBySign f (lo *ᵣ f +ᵣ o) (hi *ᵣ f +ᵣ o))
  → lo ≤ r × r ≤ hi
scaledBetween (mkℚ (+ zero) _ _) _ _ _ _ f≢0 _ _ = ⊥-elim (f≢0 (ℚP.↥p≡0⇒p≡0 _ refl))
scaledBetween f@(mkℚ (+ suc _) _ _) o _ _ _ _ low high =
  ℚP.*-cancelʳ-≤-pos f {{_}} (+-cancelʳ-≤ o low) , ℚP.*-cancelʳ-≤-pos f {{_}} (+-cancelʳ-≤ o high)
scaledBetween f@(mkℚ -[1+ _ ] _ _) o _ _ _ _ low high =
  ℚP.*-cancelʳ-≤-neg f {{_}} (+-cancelʳ-≤ o high) , ℚP.*-cancelʳ-≤-neg f {{_}} (+-cancelʳ-≤ o low)

-- An integer between the ends of the n-bit range fits n bits.
private
  endsFit : ∀ (signed : Bool) (n : ℕ) (raw : ℤ)
    → proj₁ (rawRange signed n) ≤ fromℤ raw → fromℤ raw ≤ proj₂ (rawRange signed n)
    → RawFits raw n signed
  endsFit false n (+ k) _ high with fromℤ-cancel-≤ high
  ... | +≤+ k≤ = unsigned-fits refl (≤pred⇒< (ℕP.m^n>0 2 n) k≤)
  endsFit false n -[1+ _ ] low _ with fromℤ-cancel-≤ low
  ... | ()
  endsFit true n (+ k) _ high with fromℤ-cancel-≤ high
  ... | +≤+ k≤ = signed-fits (≤pred⇒< (ℕP.m^n>0 2 (n ∸ 1)) k≤)
  endsFit true n -[1+ k ] low _ with fromℤ-cancel-≤ low
  ... | -≤- k≤ = signed-fits (≤pred⇒< (ℕP.m^n>0 2 (n ∸ 1)) k≤)

-- A raw value whose scaled image lies between the scaled images of the
-- n-bit range's ends fits n bits.
scaledRawFits : ∀ (signed : Bool) (n : ℕ) (f o : ℚ) (raw : ℤ) → f ≢ 0ℚ
  → proj₁ (orderBySign f (proj₁ (rawRange signed n) *ᵣ f +ᵣ o) (proj₂ (rawRange signed n) *ᵣ f +ᵣ o))
      ≤ applyScaling raw f o
  → applyScaling raw f o
      ≤ proj₂ (orderBySign f (proj₁ (rawRange signed n) *ᵣ f +ᵣ o) (proj₂ (rawRange signed n) *ᵣ f +ᵣ o))
  → RawFits raw n signed
scaledRawFits signed n f o raw f≢0 low high =
  endsFit signed n raw (proj₁ between) (proj₂ between)
  where
    embed : applyScaling raw f o ≡ fromℤ raw *ᵣ f +ᵣ o
    embed = cong (λ q → q *ᵣ f +ᵣ o) (z/1≡fromℤ raw)
    between = scaledBetween f o (proj₁ (rawRange signed n)) (proj₂ (rawRange signed n)) (fromℤ raw) f≢0
                (subst (_ ≤_) embed low) (subst (_≤ _) embed high)
