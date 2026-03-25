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
open import Data.Rational as Rat using (ℚ; _≤ᵇ_; _/_; floor; 0ℚ; _≟_; toℚᵘ; fromℚᵘ) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; _÷_; 0ℚᵘ)
open import Relation.Nullary.Decidable as Dec using (⌊_⌋)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)

-- Convert a natural number to a signed integer based on bit length
-- Interprets as two's complement if isSigned is true
toSigned : ℕ → ℕ → Bool → ℤ
toSigned raw bitLength false = + raw
toSigned raw bitLength true =
  let signBitMask = 2 ^ (bitLength ∸ 1)
      isNegative = signBitMask Data.Nat.≤ᵇ raw
  in if isNegative
     then -[1+ ((2 ^ bitLength) ∸ raw ∸ 1) ]
     else + raw

-- Convert an integer back to unsigned representation
fromSigned : ℤ → ℕ → ℕ
fromSigned (+ n) _ = n
fromSigned -[1+ n ] bitLength = (2 ^ bitLength) ∸ (suc n)

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
    -- Check if rational is zero
    isZero : ℚ → Bool
    isZero q = Dec.⌊ q Rat.≟ 0ℚ ⌋

    -- Divide by factor (only called when factor ≠ 0, but Agda can't prove this)
    -- We work with unnormalized rationals to avoid coprimality proofs
    divideByFactor : ℚ → ℚ → ℚ
    divideByFactor numer denom =
      Rat.fromℚᵘ (divideUnnorm (Rat.toℚᵘ numer) (Rat.toℚᵘ denom))
      where
        -- Divide unnormalized rationals by pattern matching to expose nonzero structure
        divideUnnorm : ℚᵘ → ℚᵘ → ℚᵘ
        divideUnnorm n (ℚᵘ.mkℚᵘ (+ zero) _) = ℚᵘ.0ℚᵘ  -- Unreachable (isZero check prevents), but needed for coverage
        divideUnnorm n (ℚᵘ.mkℚᵘ (+ suc num) denom) =  -- Explicit nonzero pattern, instance exists!
          n ℚᵘ.÷ (ℚᵘ.mkℚᵘ (+ suc num) denom)
        divideUnnorm n (ℚᵘ.mkℚᵘ -[1+ num ] denom) =    -- Explicit nonzero pattern, instance exists!
          n ℚᵘ.÷ (ℚᵘ.mkℚᵘ -[1+ num ] denom)

-- Check if a signal value is within bounds
inBounds : ℚ → ℚ → ℚ → Bool
inBounds value minVal maxVal = (minVal ≤ᵇ value) ∧ (value ≤ᵇ maxVal)
