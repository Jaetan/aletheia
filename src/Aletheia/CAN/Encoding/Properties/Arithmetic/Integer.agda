{-# OPTIONS --safe --without-K #-}

-- Layer 2 (ℕ ↔ ℤ two's complement) bridge lemmas for CAN signal encoding.
--
-- Purpose: Self-contained integer arithmetic — signed/unsigned roundtrip via
--   `fromSigned`/`toSigned`. NO rationals appear in this module.
-- Public API: fromSigned-toSigned-roundtrip; SignedFits;
--             toSigned-fromSigned-roundtrip; fromSigned-bounded-neg
-- Role: Layer 2 of the arithmetic firewall — quarantines two's-complement
--   reasoning so the rational layer (Properties.Arithmetic.Rational) and
--   composition layer (Properties.Roundtrip) never touch ℕ ↔ ℤ details.
module Aletheia.CAN.Encoding.Properties.Arithmetic.Integer where

open import Aletheia.CAN.Encoding.Arithmetic using (toSigned; fromSigned)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _^_; _>_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using
  ( m∸[m∸n]≡n; <⇒≤; m>n⇒m∸n≢0; <⇒≱; ≤ᵇ⇒≤; m+n≤o⇒m≤o∸n; +-monoʳ-≤
  ; +-identityʳ; *-zeroˡ; ≤⇒≤ᵇ; ≤-<-trans; ^-monoʳ-<; n<1+n; *-monoʳ-<
  ; ≤-refl; <-trans
  )
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using ()

-- ============================================================================
-- LAYER 2: INTEGER CONVERSION PROPERTIES (no ℚ)
-- ============================================================================
-- These proofs work with ℕ ↔ ℤ conversion (two's complement).
-- Still no rational arithmetic.

-- ✅ fromSigned-toSigned-roundtrip PROVEN
-- Property: Converting to signed then back to unsigned preserves value
-- (for values that fit in the bit width)
fromSigned-toSigned-roundtrip : ∀ (raw : ℕ) (bitLength : ℕ) (isSigned : Bool)
  → (bitLength > 0)
  → (raw < 2 ^ bitLength)
  → fromSigned (toSigned raw bitLength isSigned) bitLength ≡ raw
fromSigned-toSigned-roundtrip raw bitLength false bitLength>0 raw-bounded =
  -- Unsigned case: toSigned returns + raw, fromSigned (+ raw) returns raw
  refl
fromSigned-toSigned-roundtrip raw bitLength true bitLength>0 raw-bounded
  with (2 ^ (bitLength ∸ 1)) ≤ᵇ raw
... | false =
  -- Not negative: toSigned returns + raw, fromSigned (+ raw) returns raw
  refl
... | true =
  -- Negative case: prove (2 ^ bitLength) ∸ (suc ((2 ^ bitLength) ∸ raw ∸ 1)) ≡ raw
  -- Key insight: suc (x ∸ 1) ≡ x when x > 0
  -- We have: (2 ^ bitLength) ∸ raw > 0 since raw < 2 ^ bitLength
  trans (cong ((2 ^ bitLength) ∸_) suc-m∸1≡m) (m∸[m∸n]≡n (<⇒≤ raw-bounded))
  where
    -- Prove: suc ((2 ^ bitLength) ∸ raw ∸ 1) ≡ (2 ^ bitLength) ∸ raw
    -- By cases on (2 ^ bitLength) ∸ raw
    suc-m∸1≡m : suc ((2 ^ bitLength) ∸ raw ∸ 1) ≡ (2 ^ bitLength) ∸ raw
    suc-m∸1≡m with (2 ^ bitLength) ∸ raw | m>n⇒m∸n≢0 raw-bounded
    ... | zero | ≢0 = ⊥-elim (≢0 refl)  -- Contradiction: can't be zero
    ... | suc n | _ = refl  -- suc (suc n ∸ 1) = suc n ∸ 0 = suc n ✓

-- Sign-aware bounds for signed interpretation
-- This captures the semantic constraint: values must fit in their signed range
SignedFits : ℤ → ℕ → Set
SignedFits (+ n) bitLength = n < 2 ^ (bitLength ∸ 1)  -- Positive: fits in positive range
SignedFits -[1+ n ] bitLength = suc n ≤ 2 ^ (bitLength ∸ 1)  -- Negative: fits in negative range

-- Property: Converting signed to unsigned then back to signed preserves value
-- The precondition is now sign-aware: positive values need positive range, negatives need negative range
toSigned-fromSigned-roundtrip : ∀ (z : ℤ) (bitLength : ℕ)
  → (bitLength > 0)
  → SignedFits z bitLength
  → toSigned (fromSigned z bitLength) bitLength true ≡ z
toSigned-fromSigned-roundtrip (+ n) bitLength bitLength>0 n-fits
  with (2 ^ (bitLength ∸ 1)) ≤ᵇ n in eq
... | true =
  -- Contradiction: ≤ᵇ returned true means signBitMask ≤ n, but we have n < signBitMask
  ⊥-elim (<⇒≱ n-fits (≤ᵇ⇒≤ (2 ^ (bitLength ∸ 1)) n (subst T (sym eq) tt)))
... | false =
  -- isNegative = false, so toSigned returns + n
  refl
toSigned-fromSigned-roundtrip -[1+ n ] bitLength bitLength>0 n-fits
  with (2 ^ (bitLength ∸ 1)) ≤ᵇ ((2 ^ bitLength) ∸ (suc n)) in eq
... | false =
  -- Contradiction: should be in negative range
  ⊥-elim (≤ᵇ-false⇒¬≤ eq (fromSigned-≥-signBit n bitLength bitLength>0 n-fits))
  where
    -- fromSigned for negative produces value ≥ signBitMask
    fromSigned-≥-signBit : ∀ n bitLength → bitLength > 0 → suc n ≤ 2 ^ (bitLength ∸ 1)
      → 2 ^ (bitLength ∸ 1) ≤ (2 ^ bitLength) ∸ (suc n)
    fromSigned-≥-signBit n (suc bitLength) bitLen>0 n-fits =
      -- Goal: 2 ^ bitLength ≤ (2 ^ suc bitLength) ∸ (suc n)
      -- Strategy: Use m+n≤o⇒m≤o∸n with m = 2 ^ bitLength, n = suc n, o = 2 ^ suc bitLength
      -- Need: 2 ^ bitLength + suc n ≤ 2 ^ suc bitLength
      m+n≤o⇒m≤o∸n (2 ^ bitLength) sum-bounded
      where
        -- Power-of-two lemma: 2^(n+1) = 2 * 2^n = 2^n + 2^n
        -- This is a basic fact about powers of two—we state it once and use it
        pow2-double : ∀ n → 2 ^ n + 2 ^ n ≡ 2 ^ suc n
        pow2-double n =
          trans (cong (λ x → 2 ^ n + x) (sym (+-identityʳ (2 ^ n))))
                (cong (λ x → 2 ^ n + (2 ^ n + x)) (*-zeroˡ (2 ^ n)))
          -- 2 ^ suc n = 2 * 2 ^ n = 2 ^ n + 2 ^ n + 0 * 2 ^ n (by definition of *)
          -- Step 1: 2 ^ n + 2 ^ n ≡ 2 ^ n + (2 ^ n + 0) by cong and sym +-identityʳ
          -- Step 2: 2 ^ n + (2 ^ n + 0) ≡ 2 ^ n + (2 ^ n + 0 * 2 ^ n) by cong and *-zeroˡ

        -- Show: 2 ^ bitLength + suc n ≤ 2 ^ suc bitLength
        -- Since suc n ≤ 2 ^ bitLength and 2 ^ suc bitLength = 2 ^ bitLength + 2 ^ bitLength
        sum-bounded : 2 ^ bitLength + suc n ≤ 2 ^ suc bitLength
        sum-bounded = subst ((2 ^ bitLength + suc n) ≤_) (pow2-double bitLength) (+-monoʳ-≤ (2 ^ bitLength) n-fits)

    -- If ≤ᵇ returns false, then ¬ ≤
    ≤ᵇ-false⇒¬≤ : ∀ {m n} → (m ≤ᵇ n) ≡ false → m ≤ n → ⊥
    ≤ᵇ-false⇒¬≤ {m} {n} eq m≤n = subst T eq (≤⇒≤ᵇ m≤n)
        -- ≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)
        -- We have: T (m ≤ᵇ n) from m≤n
        -- We have: m ≤ᵇ n ≡ false from eq
        -- So: subst T eq : T (m ≤ᵇ n) → T false
        -- And T false = ⊥
... | true =
  -- isNegative = true, so toSigned takes negative branch
  -- Need to show: -[1+ ((2 ^ bitLength) ∸ ((2 ^ bitLength) ∸ (suc n)) ∸ 1) ] ≡ -[1+ n ]
  cong -[1+_] (trans (cong (_∸ 1) (m∸[m∸n]≡n (<⇒≤ suc-n-bounded))) refl)
  where
    -- suc n ∸ 1 = n by definition, so second trans step is refl

    -- suc n < 2 ^ bitLength (from n-fits: suc n ≤ 2 ^ (bitLength ∸ 1) and bitLength > 0)
    suc-n-bounded : suc n < 2 ^ bitLength
    suc-n-bounded = pow2-upper bitLength (suc n) bitLength>0 n-fits
      where
        -- Infrastructure: values fitting in lower half fit strictly in full range
        pow2-upper : ∀ m x → m > 0 → x ≤ 2 ^ (m ∸ 1) → x < 2 ^ m
        pow2-upper zero _ () _
        pow2-upper (suc m) x _ x-fits =
          -- x ≤ 2^m, and 2^m < 2^(suc m) by monotonicity, so x < 2^(suc m)
          ≤-<-trans x-fits (^-monoʳ-< 2 (s≤s (s≤s z≤n)) (n<1+n m))

-- Property: fromSigned produces bounded results (for negative numbers)
-- Note: For positive numbers, the caller must ensure the input fits
fromSigned-bounded-neg : ∀ (n : ℕ) (bitLength : ℕ)
  → (bitLength > 0)
  → fromSigned -[1+ n ] bitLength < 2 ^ bitLength
fromSigned-bounded-neg n bitLength bitLength>0 =
  -- Need to show: (2 ^ bitLength) ∸ (suc n) < 2 ^ bitLength
  m∸1+n<m (2 ^ bitLength) n (^-positive bitLength)
  where
    -- 2 ^ bitLength > 0 for any bitLength
    ^-positive : ∀ m → 2 ^ m > 0
    ^-positive zero = s≤s z≤n
    ^-positive (suc m) = *-monoʳ-< 2 (^-positive m)

    -- m ∸ (suc n) < m when m > 0
    -- Proof: Via auxiliary lemma without m>0 constraint
    m∸1+n<m : ∀ m n → m > 0 → m ∸ suc n < m
    m∸1+n<m (suc m) n _ = aux m n
      where
        -- Auxiliary: works for all m, n
        aux : ∀ m n → suc m ∸ suc n < suc m
        aux m zero = s≤s ≤-refl  -- suc m ∸ 1 = m < suc m
        aux zero (suc n) = s≤s z≤n  -- 1 ∸ suc (suc n) = 0 < 1
        aux (suc m) (suc n) = <-trans (aux m n) (s≤s ≤-refl)  -- IH + transitivity
