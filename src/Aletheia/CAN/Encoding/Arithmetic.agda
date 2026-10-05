-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The arithmetic of raw and physical values, with no signal and no frame.
--
-- Purpose: Two's complement sign conversion, scaling/offset application,
--          and bounds checking of a value.
-- Operations: toSigned (unsigned → signed), fromSigned (signed → unsigned),
--             applyScaling (raw → physical), inBounds (range check), and the
--             raw range and scaling direction (rawRange, orderBySign).
-- Role: Used by the extraction path (Aletheia.CAN.Encoding), value encoding
--   (Aletheia.CAN.Encoding.Value), the raw range's arithmetic
--   (Aletheia.CAN.Encoding.Arithmetic.Range) and the validator.
module Aletheia.CAN.Encoding.Arithmetic where

open import Data.Nat using (ℕ; suc; _∸_; _^_; pred)
open import Data.Rational as Rat using (ℚ; _≤ᵇ_; _/_) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; T; true; false; if_then_else_; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Rational.Properties as ℚP
open import Data.Rational.Literals using (fromℤ)

open import Aletheia.Data.Dec0 using (Dec₀; fromBridges; does₀; T-∧→; T-∧←)

-- Two's complement helpers: sign bit mask and full range for a given bit length
signBitMask : ℕ → ℕ
signBitMask bitLength = 2 ^ (bitLength ∸ 1)

fullRange : ℕ → ℕ
fullRange bitLength = 2 ^ bitLength

-- Convert a natural number to a signed integer based on bit length.
-- Two's complement per CAN 2.0B / ISO 11898-1 §8.4.2.2.
toSigned : ℕ → ℕ → Bool → ℤ
toSigned raw _ false = + raw
toSigned raw bitLength true =
  let isNegative = signBitMask bitLength Data.Nat.≤ᵇ raw
  in if isNegative
     then -[1+ (fullRange bitLength ∸ raw ∸ 1) ]
     else + raw

-- Convert an integer back to unsigned representation
fromSigned : ℤ → ℕ → ℕ
fromSigned (+ n) _ = n
fromSigned -[1+ n ] bitLength = fullRange bitLength ∸ suc n

-- Apply scaling and offset to convert a raw value to a physical value
applyScaling : ℤ → ℚ → ℚ → ℚ
applyScaling raw factor offset =
  let rawℚ = raw / 1
  in (rawℚ *ᵣ factor) +ᵣ offset

-- Self-certifying bounds check: `does₀` is the Bool fast path (two direct ℤ
-- comparisons via `_≤ᵇ_`); the erased certificate pins its meaning as the
-- conjunction `minVal ≤ value × value ≤ maxVal`.  MAlonzo erases the
-- certificate (Dec₀ is a newtype over Bool).
inBounds₀ : (value minVal maxVal : ℚ) → Dec₀ ((minVal Rat.≤ value) × (value Rat.≤ maxVal))
inBounds₀ value minVal maxVal =
  fromBridges ((minVal ≤ᵇ value) ∧ (value ≤ᵇ maxVal)) sound complete
  where
    @0 sound : T ((minVal ≤ᵇ value) ∧ (value ≤ᵇ maxVal))
             → (minVal Rat.≤ value) × (value Rat.≤ maxVal)
    sound t = ℚP.≤ᵇ⇒≤ (proj₁ (T-∧→ t)) , ℚP.≤ᵇ⇒≤ (proj₂ (T-∧→ t))

    @0 complete : (minVal Rat.≤ value) × (value Rat.≤ maxVal)
                → T ((minVal ≤ᵇ value) ∧ (value ≤ᵇ maxVal))
    complete (lo , hi) = T-∧← (ℚP.≤⇒≤ᵇ lo) (ℚP.≤⇒≤ᵇ hi)

-- Whether a value lies within bounds: the definitional projection of
-- `inBounds₀`.
inBounds : ℚ → ℚ → ℚ → Bool
inBounds value minVal maxVal = does₀ (inBounds₀ value minVal maxVal)

-- ============================================================================
-- RAW RANGE AND SCALING DIRECTION
-- ============================================================================

-- Whether a rational is below zero, read off its numerator.
isNegativeℚ : ℚ → Bool
isNegativeℚ q with ℚ.numerator q
... | (+ _)     = false
... | (-[1+ _ ]) = true

-- The least and the greatest raw value of n bits.
-- Signed: two's complement, [−2^(n−1), 2^(n−1)−1].
-- Unsigned: [0, 2^n − 1].
rawRange : Bool → ℕ → ℚ × ℚ
rawRange true  n = fromℤ (-[1+ pred (2 ^ (n ∸ 1)) ]) , fromℤ (+ pred (2 ^ (n ∸ 1)))
rawRange false n = fromℤ (+ 0) , fromℤ (+ pred (2 ^ n))

-- The images of two ends under scaling, least first: a negative factor
-- reverses them.
orderBySign : ℚ → ℚ → ℚ → ℚ × ℚ
orderBySign factor a b = if isNegativeℚ factor then (b , a) else (a , b)
