-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Numeric conversion utilities for CAN signal encoding/decoding.
--
-- Purpose: Two's complement sign conversion, scaling/offset application,
--          and bounds checking for signal values.
-- Operations: toSigned (unsigned → signed), fromSigned (signed → unsigned),
--             applyScaling (raw → physical), removeScaling (physical → raw),
--             inBounds (range check).
-- Role: Used by Encoding for signal extraction/injection pipeline.
module Aletheia.CAN.Encoding.Arithmetic where

open import Data.Nat using (ℕ; zero; suc; _∸_; _^_)
open import Data.Rational as Rat using (ℚ; _≤ᵇ_; _/_; floor; 0ℚ) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; T; true; false; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Rational.Properties as ℚP

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

-- Apply scaling and offset to convert raw value to signal value
applyScaling : ℤ → ℚ → ℚ → ℚ
applyScaling raw factor offset =
  let rawℚ = raw / 1
  in (rawℚ *ᵣ factor) +ᵣ offset

-- Inverse of applyScaling: convert signal value back to raw integer
-- Formula: raw = floor((signalValue - offset) / factor)
-- Returns Nothing if factor is zero (malformed DBC file)
removeScaling : ℚ → ℚ → ℚ → Maybe ℤ
removeScaling signalValue factor offset =
  if isZero factor
  then nothing  -- Cannot divide by zero
  else just (floor (divideByFactor (signalValue -ᵣ offset) factor))
  where
    -- Check if rational is zero via the Bool-valued `_≤ᵇ_`, which compiles to
    -- a direct ℤ comparison without allocating a Dec proof term per call.
    isZero : ℚ → Bool
    isZero q = (q ≤ᵇ 0ℚ) ∧ (0ℚ ≤ᵇ q)

    -- Divide by factor (only called when factor ≠ 0, but Agda can't prove this)
    -- We work with unnormalized rationals to avoid coprimality proofs
    divideByFactor : ℚ → ℚ → ℚ
    divideByFactor numer denom =
      Rat.fromℚᵘ (divideUnnorm (Rat.toℚᵘ numer) (Rat.toℚᵘ denom))
      where
        -- Divide unnormalized rationals by pattern matching to expose nonzero structure.
        --
        -- Dead branch: the `(+ zero)` case is unreachable because `removeScaling`
        -- guards with `if isZero factor then nothing` above (line 54), so this
        -- helper is only ever called on a non-zero `factor`. Retained to satisfy
        -- Agda's pattern coverage checker — returning `0ℚᵘ` keeps the branch
        -- total without requiring a proof-carrying NonZero instance through the
        -- call chain from `removeScaling`.
        divideUnnorm : ℚᵘ → ℚᵘ → ℚᵘ
        divideUnnorm n (ℚᵘ.mkℚᵘ (+ zero) _) = ℚᵘ.0ℚᵘ  -- Dead branch, see comment above.
        divideUnnorm n (ℚᵘ.mkℚᵘ (+ suc num) denom) =  -- Explicit nonzero pattern, instance exists!
          n ℚᵘ.÷ (ℚᵘ.mkℚᵘ (+ suc num) denom)
        divideUnnorm n (ℚᵘ.mkℚᵘ -[1+ num ] denom) =    -- Explicit nonzero pattern, instance exists!
          n ℚᵘ.÷ (ℚᵘ.mkℚᵘ -[1+ num ] denom)

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

-- Check if a signal value is within bounds — definitional projection of
-- `inBounds₀` (runtime shape unchanged).
inBounds : ℚ → ℚ → ℚ → Bool
inBounds value minVal maxVal = does₀ (inBounds₀ value minVal maxVal)
