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
-- Verified: All bit manipulations use structural BitVec proofs for safety.
module Aletheia.CAN.Encoding where

open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.CAN.Signal using (SignalDef; SignalValue)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; isBigEndian; swapBytes; extractBits; injectBits; payloadIso; payloadIso-involutive; injectBits-preserves-disjoint; injectBits-preserves-outside; physicalBitPos; physicalBitPos-BE-involutive; physicalBitPos-BE-bounded; extractBits-swap-inject-preserves; not-in-interval; _≟-ByteOrder_)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ; ℕToBitVec)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _^_; _<_; _<?_; _≤_; z≤n; s≤s)
open import Data.Rational as Rat using (ℚ; _≤ᵇ_; _/_; floor; 0ℚ; _≟_; toℚᵘ; fromℚᵘ)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; _÷_; 0ℚᵘ)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_)
open import Relation.Nullary.Decidable as Dec using (⌊_⌋)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using () renaming (_≢_ to _≢ₚ_)
open import Function using (case_of_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (<-≤-trans; m<m+n)

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
    (bitVecToℕ (extractBits {bitLength} bytes (startBit)))
    (bitLength)
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
    injectHelper : SignalValue → SignalDef → ByteOrder → CANFrame → Maybe CANFrame
    injectHelper value signalDef byteOrder frame
      with removeScaling value factor offset
         where open SignalDef signalDef
    ... | nothing = nothing
    ... | just rawSigned
      with fromSigned rawSigned (bitLength) <? 2 ^ bitLength
         where open SignalDef signalDef
    ...   | no _ = nothing  -- Raw value doesn't fit in bitLength bits
    ...   | yes bounded =
      let open CANFrame frame
          open SignalDef signalDef
          -- Convert to unsigned with proof
          rawUnsigned : ℕ
          rawUnsigned = fromSigned rawSigned (bitLength)
          -- Convert ℕ → BitVec with proof
          rawBitVec : BitVec (bitLength)
          rawBitVec = ℕToBitVec rawUnsigned bounded
          -- Inject bits
          bytes : Vec Byte 8
          bytes = if isBigEndian byteOrder
                  then swapBytes payload
                  else payload
          updatedBytes : Vec Byte 8
          updatedBytes = injectBits bytes (startBit) rawBitVec
          finalBytes : Vec Byte 8
          finalBytes = if isBigEndian byteOrder
                       then swapBytes updatedBytes
                       else updatedBytes
      in just (record frame { payload = finalBytes })

-- ============================================================================
-- STRUCTURAL LEMMA: injectSignal payload form
-- ============================================================================

-- When injectSignal succeeds, the payload has the form:
--   injectPayload startBit rawBitVec bo (payload frame)
-- for some rawBitVec : BitVec (bitLength)
--
-- This is captured by showing that extraction at a disjoint position is preserved.

-- Helper: extractionBytes equals payloadIso (definitional by cases)
extractionBytes≡payloadIso : ∀ frame bo → extractionBytes frame bo ≡ payloadIso bo (CANFrame.payload frame)
extractionBytes≡payloadIso frame LittleEndian = refl
extractionBytes≡payloadIso frame BigEndian = refl

-- Key structural lemma: when injectSignal succeeds, bits at disjoint positions are preserved
-- The proof mirrors injectSignal's structure using plain with-patterns (no rewrite, no in)
injectSignal-preserves-disjoint-bits :
  ∀ {len₂} (v : ℚ) (sig : SignalDef) (bo : ByteOrder) (frame frame' : CANFrame)
    (start₂ : ℕ)
  → injectSignal v sig bo frame ≡ just frame'
  → SignalDef.startBit sig + SignalDef.bitLength sig ≤ start₂
    ⊎ start₂ + len₂ ≤ SignalDef.startBit sig  -- disjoint ranges
  → SignalDef.startBit sig + SignalDef.bitLength sig ≤ 64
  → start₂ + len₂ ≤ 64
  → extractBits {len₂} (extractionBytes frame' bo) start₂
    ≡ extractBits {len₂} (extractionBytes frame bo) start₂
injectSignal-preserves-disjoint-bits {len₂} v sig bo frame frame' start₂ eq disj fits₁ fits₂
  with inBounds v (SignalDef.minimum sig) (SignalDef.maximum sig)
... | false = case eq of λ ()
... | true with removeScaling v (SignalDef.factor sig) (SignalDef.offset sig)
...   | nothing = case eq of λ ()
...   | just rawSigned with fromSigned rawSigned (SignalDef.bitLength sig) <? 2 ^ SignalDef.bitLength sig
...     | no _ = case eq of λ ()
...     | yes bounded = core-proof (just-injective (sym eq))
  where
    open SignalDef sig
    open ≡-Reasoning

    origPayload = CANFrame.payload frame
    start₁ = startBit
    len₁ = bitLength

    -- Define the computed values matching injectSignal's definition exactly
    rawBitVec = ℕToBitVec (fromSigned rawSigned len₁) bounded
    bytes = payloadIso bo origPayload
    updatedBytes = injectBits bytes start₁ rawBitVec
    finalBytes = payloadIso bo updatedBytes

    -- The frame returned by injectSignal when all conditions succeed
    expectedFrame = record frame { payload = finalBytes }

    -- Core proof using the fact that frame' = expectedFrame
    core-proof : frame' ≡ expectedFrame
               → extractBits {len₂} (extractionBytes frame' bo) start₂
                 ≡ extractBits {len₂} (extractionBytes frame bo) start₂
    core-proof frame'-eq =
      begin
        extractBits (extractionBytes frame' bo) start₂
      ≡⟨ cong (λ f → extractBits (extractionBytes f bo) start₂) frame'-eq ⟩
        extractBits (extractionBytes expectedFrame bo) start₂
      ≡⟨ cong (λ x → extractBits x start₂) (extractionBytes≡payloadIso expectedFrame bo) ⟩
        extractBits (payloadIso bo finalBytes) start₂
      ≡⟨⟩  -- finalBytes = payloadIso bo updatedBytes, unfolds to payloadIso bo (payloadIso bo ...)
        extractBits (payloadIso bo (payloadIso bo updatedBytes)) start₂
      ≡⟨ cong (λ x → extractBits x start₂) (payloadIso-involutive bo updatedBytes) ⟩
        extractBits updatedBytes start₂
      ≡⟨⟩  -- updatedBytes = injectBits bytes start₁ rawBitVec
        extractBits (injectBits bytes start₁ rawBitVec) start₂
      ≡⟨ injectBits-preserves-disjoint bytes start₁ start₂ rawBitVec disj fits₁ fits₂ ⟩
        extractBits bytes start₂
      ≡⟨⟩  -- bytes = payloadIso bo origPayload
        extractBits (payloadIso bo origPayload) start₂
      ≡⟨ cong (λ x → extractBits x start₂) (sym (extractionBytes≡payloadIso frame bo)) ⟩
        extractBits (extractionBytes frame bo) start₂
      ∎

-- ============================================================================
-- MIXED BYTE ORDER: Physical disjointness preservation
-- ============================================================================

-- When injectSignal succeeds, bits at physically disjoint positions are preserved,
-- even when injection and extraction use different byte orders.
-- The physical disjointness condition ensures that the sets of physical bits
-- touched by each signal don't overlap in the original payload.
injectSignal-preserves-disjoint-bits-physical :
  ∀ {len₂} (v : ℚ) (sig : SignalDef) (bo₁ bo₂ : ByteOrder) (frame frame' : CANFrame)
    (start₂ : ℕ)
  → injectSignal v sig bo₁ frame ≡ just frame'
  → (∀ k₁ → k₁ < SignalDef.bitLength sig
     → ∀ k₂ → k₂ < len₂
     → physicalBitPos bo₁ (SignalDef.startBit sig + k₁)
       ≢ₚ physicalBitPos bo₂ (start₂ + k₂))
  → SignalDef.startBit sig + SignalDef.bitLength sig ≤ 64
  → start₂ + len₂ ≤ 64
  → extractBits {len₂} (extractionBytes frame' bo₂) start₂
    ≡ extractBits {len₂} (extractionBytes frame bo₂) start₂
injectSignal-preserves-disjoint-bits-physical {len₂} v sig bo₁ bo₂ frame frame' start₂ eq physDisj fits₁ fits₂
  with inBounds v (SignalDef.minimum sig) (SignalDef.maximum sig)
... | false = case eq of λ ()
... | true with removeScaling v (SignalDef.factor sig) (SignalDef.offset sig)
...   | nothing = case eq of λ ()
...   | just rawSigned with fromSigned rawSigned (SignalDef.bitLength sig) <? 2 ^ SignalDef.bitLength sig
...     | no _ = case eq of λ ()
...     | yes bounded = core-proof (just-injective (sym eq))
  where
    open SignalDef sig
    open ≡-Reasoning

    origPayload = CANFrame.payload frame
    s₁ = startBit
    l₁ = bitLength

    rawBitVec = ℕToBitVec {l₁} (fromSigned rawSigned l₁) bounded
    bytes = payloadIso bo₁ origPayload
    updatedBytes = injectBits bytes s₁ rawBitVec
    finalBytes = payloadIso bo₁ updatedBytes

    expectedFrame = record frame { payload = finalBytes }

    core-proof : frame' ≡ expectedFrame
               → extractBits {len₂} (extractionBytes frame' bo₂) start₂
                 ≡ extractBits {len₂} (extractionBytes frame bo₂) start₂
    core-proof frame'-eq =
      begin
        extractBits (extractionBytes frame' bo₂) start₂
      ≡⟨ cong (λ f → extractBits (extractionBytes f bo₂) start₂) frame'-eq ⟩
        extractBits (extractionBytes expectedFrame bo₂) start₂
      ≡⟨ cong (λ x → extractBits x start₂) (extractionBytes≡payloadIso expectedFrame bo₂) ⟩
        extractBits (payloadIso bo₂ finalBytes) start₂
      ≡⟨ go bo₁ bo₂ refl refl ⟩
        extractBits (payloadIso bo₂ origPayload) start₂
      ≡⟨ cong (λ x → extractBits x start₂) (sym (extractionBytes≡payloadIso frame bo₂)) ⟩
        extractBits (extractionBytes frame bo₂) start₂
      ∎
      where
        -- Dispatch on concrete byte orders via refl-passing to avoid WithOnFreeVariable
        go : (b₁ b₂ : ByteOrder) → b₁ ≡ bo₁ → b₂ ≡ bo₂
           → extractBits (payloadIso bo₂ finalBytes) start₂
             ≡ extractBits (payloadIso bo₂ origPayload) start₂
        -- Same byte order (LE/LE): involutive + preserves-outside
        go LittleEndian LittleEndian refl refl =
          begin
            extractBits (payloadIso LittleEndian finalBytes) start₂
          ≡⟨ cong (λ x → extractBits x start₂) (payloadIso-involutive LittleEndian updatedBytes) ⟩
            extractBits updatedBytes start₂
          ≡⟨ injectBits-preserves-outside bytes s₁ start₂ rawBitVec logical-outside fits₁ fits₂ ⟩
            extractBits bytes start₂
          ∎
          where
            logical-outside : ∀ k₂' → k₂' < len₂ → start₂ + k₂' < s₁ ⊎ s₁ + l₁ ≤ start₂ + k₂'
            logical-outside k₂' k₂'<len₂ = not-in-interval s₁ l₁ (start₂ + k₂') pw
              where
                pw : ∀ k₁ → k₁ < l₁ → start₂ + k₂' ≢ₚ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂' k₂'<len₂
                  (cong (physicalBitPos LittleEndian) (sym eq₀))
        -- Same byte order (BE/BE): involutive + preserves-outside
        go BigEndian BigEndian refl refl =
          begin
            extractBits (payloadIso BigEndian finalBytes) start₂
          ≡⟨ cong (λ x → extractBits x start₂) (payloadIso-involutive BigEndian updatedBytes) ⟩
            extractBits updatedBytes start₂
          ≡⟨ injectBits-preserves-outside bytes s₁ start₂ rawBitVec logical-outside fits₁ fits₂ ⟩
            extractBits bytes start₂
          ∎
          where
            logical-outside : ∀ k₂' → k₂' < len₂ → start₂ + k₂' < s₁ ⊎ s₁ + l₁ ≤ start₂ + k₂'
            logical-outside k₂' k₂'<len₂ = not-in-interval s₁ l₁ (start₂ + k₂') pw
              where
                pw : ∀ k₁ → k₁ < l₁ → start₂ + k₂' ≢ₚ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂' k₂'<len₂
                  (cong (physicalBitPos BigEndian) (sym eq₀))
        -- LE inject, BE extract: payloadIso BE (payloadIso LE x) ≡ swapBytes x
        go LittleEndian BigEndian refl refl =
          extractBits-swap-inject-preserves origPayload s₁ start₂ rawBitVec
            outside-LE-BE fits₁ fits₂
          where
            outside-LE-BE : ∀ k → k < len₂ → physicalBitPos BigEndian (start₂ + k) < s₁
                          ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian (start₂ + k)
            outside-LE-BE k₂ k₂<len₂ =
              not-in-interval s₁ l₁ (physicalBitPos BigEndian (start₂ + k₂)) pw
              where
                pw : ∀ k₁ → k₁ < l₁ → physicalBitPos BigEndian (start₂ + k₂) ≢ₚ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂ k₂<len₂ (sym eq₀)
        -- BE inject, LE extract: payloadIso LE (payloadIso BE x) ≡ swapBytes x
        go BigEndian LittleEndian refl refl =
          begin
            extractBits (swapBytes updatedBytes) start₂
          ≡⟨⟩
            extractBits (swapBytes (injectBits (swapBytes origPayload) s₁ rawBitVec)) start₂
          ≡⟨ extractBits-swap-inject-preserves (swapBytes origPayload) s₁ start₂ rawBitVec
               outside-BE fits₁ fits₂ ⟩
            extractBits (swapBytes (swapBytes origPayload)) start₂
          ≡⟨ cong (λ x → extractBits x start₂) (payloadIso-involutive BigEndian origPayload) ⟩
            extractBits origPayload start₂
          ∎
          where
            outside-BE : ∀ k → k < len₂ → physicalBitPos BigEndian (start₂ + k) < s₁
                       ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian (start₂ + k)
            outside-BE k₂ k₂<len₂ = not-in-interval s₁ l₁ (physicalBitPos BigEndian (start₂ + k₂)) pw
              where
                open import Data.Nat.Properties using (+-monoʳ-<)
                start₂k₂<64 : start₂ + k₂ < 64
                start₂k₂<64 = <-≤-trans (+-monoʳ-< start₂ k₂<len₂) fits₂
                pw : ∀ k₁ → k₁ < l₁ → physicalBitPos BigEndian (start₂ + k₂) ≢ₚ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂ k₂<len₂ inner
                  where
                    inner : physicalBitPos BigEndian (s₁ + k₁) ≡ start₂ + k₂
                    inner = trans (sym (cong (physicalBitPos BigEndian) eq₀))
                                  (physicalBitPos-BE-involutive (start₂ + k₂) start₂k₂<64)

-- Round-trip correctness properties defined in Aletheia.CAN.Encoding.Properties:
-- 1. extractBits-injectBits-roundtrip: Bit-level roundtrip (no ℚ)
-- 2. fromSigned-toSigned-roundtrip: Integer conversion roundtrip (no ℚ)
-- 3. removeScaling-applyScaling-roundtrip: Scaling roundtrip (isolated ℚ)
-- 4. extractSignal-injectSignal-roundtrip: Full pipeline roundtrip
-- 5. SignalsDisjoint: Non-overlapping signals commute and don't interfere
--
-- Strategy: Two-level proof architecture keeps ℚ proofs isolated and small.
