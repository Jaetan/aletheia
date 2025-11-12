{-# OPTIONS --safe --without-K #-}

module Aletheia.CAN.Encoding where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≥_; _^_)
open import Data.Fin using (Fin; toℕ)
open import Data.Rational as Rat using (ℚ; _≤ᵇ_; _/_; floor; 0ℚ; _≟_; toℚᵘ; fromℚᵘ)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; _÷_; 0ℚᵘ; ↥_)
open import Data.Rational using () renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_)
open import Relation.Nullary.Decidable as Dec using (True; toWitness)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

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
  where
    open import Data.Nat using (_≤ᵇ_)

-- Convert an integer back to unsigned representation
fromSigned : ℤ → ℕ → ℕ
fromSigned (+ n) _ = n
fromSigned -[1+ n ] bitLength = (2 ^ bitLength) ∸ (suc n)

-- Apply scaling and offset to convert raw value to signal value
applyScaling : ℤ → ℚ → ℚ → ℚ
applyScaling raw factor offset =
  let rawℚ = raw / 1
  in (rawℚ *ℚ factor) +ℚ offset

-- Inverse of applyScaling: convert signal value back to raw integer
-- Formula: raw = floor((signalValue - offset) / factor)
-- Returns Nothing if factor is zero (malformed DBC file)
removeScaling : ℚ → ℚ → ℚ → Maybe ℤ
removeScaling signalValue factor offset =
  if isZero factor
  then nothing  -- Cannot divide by zero
  else just (floor (divideByFactor (signalValue -ℚ offset) factor))
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

-- Extract a signal from a CAN frame
extractSignal : CANFrame → SignalDef → ByteOrder → Maybe SignalValue
extractSignal frame signalDef byteOrder =
  let open CANFrame frame
      open SignalDef signalDef
      -- Apply byte swapping if needed
      bytes : Data.Vec.Vec Byte 8
      bytes = if isBigEndian byteOrder
              then swapBytes payload
              else payload
      -- Extract raw bits
      rawBits : ℕ
      rawBits = extractBits bytes (toℕ startBit) (toℕ bitLength)
      -- Convert to signed if needed
      signedValue : ℤ
      signedValue = toSigned rawBits (toℕ bitLength) isSigned
      -- Apply scaling
      scaledValue : ℚ
      scaledValue = applyScaling signedValue factor offset
      -- Check bounds
      valid : Bool
      valid = inBounds scaledValue minimum maximum
  in if valid then just scaledValue else nothing
  where
    open import Data.Vec using (Vec)
    isBigEndian : ByteOrder → Bool
    isBigEndian BigEndian = true
    isBigEndian LittleEndian = false

-- Inject a signal value into a CAN frame
injectSignal : SignalValue → SignalDef → ByteOrder → CANFrame → Maybe CANFrame
injectSignal value signalDef byteOrder frame =
  let open CANFrame frame
      open SignalDef signalDef
      -- Check bounds
      valid : Bool
      valid = inBounds value minimum maximum
  in if valid
     then injectHelper value signalDef byteOrder frame
     else nothing
  where
    open import Data.Vec using (Vec)
    open import Data.Maybe using (_>>=_)

    isBigEndian : ByteOrder → Bool
    isBigEndian BigEndian = true
    isBigEndian LittleEndian = false

    injectHelper : SignalValue → SignalDef → ByteOrder → CANFrame → Maybe CANFrame
    injectHelper value signalDef byteOrder frame =
      let open CANFrame frame
          open SignalDef signalDef
      in removeScaling value factor offset >>= λ rawSigned →
         let -- Convert to unsigned
             rawUnsigned : ℕ
             rawUnsigned = fromSigned rawSigned (toℕ bitLength)
             -- Inject bits
             bytes : Vec Byte 8
             bytes = if isBigEndian byteOrder
                     then swapBytes payload
                     else payload
             updatedBytes : Vec Byte 8
             updatedBytes = injectBits bytes (toℕ startBit) rawUnsigned (toℕ bitLength)
             finalBytes : Vec Byte 8
             finalBytes = if isBigEndian byteOrder
                          then swapBytes updatedBytes
                          else updatedBytes
         in just (record frame { payload = finalBytes })

-- Round-trip properties (TODO for Phase 5: prove these)
-- These state the correctness of encoding/decoding:
-- 1. Extracting after injecting gives back the original value
-- 2. The frame payload is preserved through inject/extract cycles
--
-- Note: Cannot use postulate with --safe flag, so proofs must be completed
-- before this can be fully verified. For now, these properties are documented
-- but not formally stated in the type system.
