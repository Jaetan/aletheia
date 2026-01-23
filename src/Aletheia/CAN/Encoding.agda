{-# OPTIONS --safe --without-K #-}

-- Signal encoding/decoding with runtime bounds checking (no postulates)

-- Signal extraction and injection from CAN frames (bit-level operations).
--
-- Purpose: Extract/inject signal values from 8-byte CAN frames using DBC definitions.
-- Operations: extractSignal (frame + signal → physical value with scaling),
--             injectSignal (physical value + signal → frame with updated bits).
-- Role: Core CAN processing, used by protocol handlers and verification.
--
-- Algorithm: Bit extraction → endianness conversion → sign extension → scaling (factor/offset).
-- Verified: All bit manipulations use bounded types (Fin) for safety.
module Aletheia.CAN.Encoding where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Aletheia.Data.BitVec
open import Aletheia.Data.BitVec.Conversion
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≥_; _^_; _<_; _<?_)
open import Data.Fin using (Fin; toℕ)
open import Data.Rational as Rat using (ℚ; _≤ᵇ_; _/_; floor; 0ℚ; _≟_; toℚᵘ; fromℚᵘ)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; _÷_; 0ℚᵘ; ↥_)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_)
open import Relation.Nullary.Decidable as Dec using (True; toWitness)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Vec using (Vec)
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

-- ============================================================================
-- COMPUTATIONAL CORE: Pure functions for proof ergonomics
-- ============================================================================
-- These are factored out from extractSignal to enable clean rewriting in proofs.
-- No Maybe, no with, no Dec - just math.

-- Extract raw signed integer from bytes (no bounds check, no scaling)
extractSignalCore : Vec Byte 8 → SignalDef → ℤ
extractSignalCore bytes sig =
  let open SignalDef sig in
  toSigned
    (bitVecToℕ (extractBits {toℕ bitLength} bytes (toℕ startBit)))
    (toℕ bitLength)
    isSigned

-- Apply scaling to raw extracted value
scaleExtracted : ℤ → SignalDef → ℚ
scaleExtracted raw sig = applyScaling raw (SignalDef.factor sig) (SignalDef.offset sig)

-- Get the bytes to extract from (handles byte order)
extractionBytes : CANFrame → ByteOrder → Vec Byte 8
extractionBytes frame LittleEndian = CANFrame.payload frame
extractionBytes frame BigEndian = swapBytes (CANFrame.payload frame)

-- ============================================================================

-- Extract a signal from a CAN frame
-- Now a thin wrapper around the computational core
extractSignal : CANFrame → SignalDef → ByteOrder → Maybe SignalValue
extractSignal frame sig byteOrder =
  let bytes = extractionBytes frame byteOrder
      raw = extractSignalCore bytes sig
      value = scaleExtracted raw sig
  in if inBounds value (SignalDef.minimum sig) (SignalDef.maximum sig)
     then just value
     else nothing

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

    injectHelper : SignalValue → SignalDef → ByteOrder → CANFrame → Maybe CANFrame
    injectHelper value signalDef byteOrder frame
      with removeScaling value factor offset
         where open SignalDef signalDef
    ... | nothing = nothing
    ... | just rawSigned
      with fromSigned rawSigned (toℕ bitLength) <? 2 ^ toℕ bitLength
         where open SignalDef signalDef
    ...   | no _ = nothing  -- Raw value doesn't fit in bitLength bits
    ...   | yes bounded =
      let open CANFrame frame
          open SignalDef signalDef
          -- Convert to unsigned with proof
          rawUnsigned : ℕ
          rawUnsigned = fromSigned rawSigned (toℕ bitLength)
          -- Convert ℕ → BitVec with proof
          rawBitVec : BitVec (toℕ bitLength)
          rawBitVec = ℕToBitVec rawUnsigned bounded
          -- Inject bits
          bytes : Vec Byte 8
          bytes = if isBigEndian byteOrder
                  then swapBytes payload
                  else payload
          updatedBytes : Vec Byte 8
          updatedBytes = injectBits bytes (toℕ startBit) rawBitVec
          finalBytes : Vec Byte 8
          finalBytes = if isBigEndian byteOrder
                       then swapBytes updatedBytes
                       else updatedBytes
      in just (record frame { payload = finalBytes })

-- Round-trip correctness properties defined in Aletheia.CAN.Encoding.Properties:
-- 1. extractBits-injectBits-roundtrip: Bit-level roundtrip (no ℚ)
-- 2. fromSigned-toSigned-roundtrip: Integer conversion roundtrip (no ℚ)
-- 3. removeScaling-applyScaling-roundtrip: Scaling roundtrip (isolated ℚ)
-- 4. extractSignal-injectSignal-roundtrip: Full pipeline roundtrip
-- 5. SignalsDisjoint: Non-overlapping signals commute and don't interfere
--
-- Strategy: Two-level proof architecture keeps ℚ proofs isolated and small.
