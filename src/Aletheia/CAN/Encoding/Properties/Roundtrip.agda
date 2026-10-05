-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Extracting a signal whose raw value's bits were written into a frame.
--
-- Purpose: composes the bit-level roundtrip (Endianness.Properties), the
--   ℕ ↔ ℤ signed/unsigned bridge (Arithmetic) and the scaling of the raw
--   value: the frame the writer `withInjected` makes from a raw value's bits
--   (`injectedFrame`) extracts back to the value that raw value scales to
--   (`extractSignal-reduces-unsigned` / `-signed`).  The value-level theorem
--   built on these, that an accepted value's frame extracts back to it, is
--   `Aletheia.CAN.Encoding.Properties.Value.extractSignal-encodedBits`.
--
-- Layering (this file):
--   * Layer 4A (core bytes-level roundtrip, private): raw → ℕToBitVec →
--     injectBits → extractBits → bitVecToℕ → toSigned chains for unsigned
--     and signed cases. No Maybe, no guards — pure bytes-level reasoning.
--   * Layer 4: `injectedFrame`, `extractSignal-reduces-unsigned`.
--   * Layer 4B (signed variant): `extractSignal-reduces-signed`, with
--     `SignedFits` instead of `n < 2^bl` and `toSigned _ true` at the end.
module Aletheia.CAN.Encoding.Properties.Roundtrip where

open import Aletheia.CAN.Encoding using (extractSignalCore; scaleExtracted; extractSignal; withInjected)
open import Aletheia.CAN.Encoding.Arithmetic using (toSigned; fromSigned; inBounds)
open import Aletheia.CAN.Encoding.Properties.Arithmetic using (SignedFits; toSigned-fromSigned-roundtrip)
open import Aletheia.CAN.Encoding.Arithmetic.Range using
  (SignedFits-implies-fromSigned-bounded)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; extractBits; injectBits; swapBytes)
open import Aletheia.CAN.Endianness.Properties using (extractBits-injectBits-roundtrip; swapBytes-involutive)
open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ; ℕToBitVec; bitVec-roundtrip)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _^_; _>_)
open import Data.Integer using (ℤ; +_)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.DecRat using (toℚ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER 4A: Core roundtrip (pure bytes level, no Maybe/guards)
-- ═══════════════════════════════════════════════════════════════════════════
-- Chain: extractBits ∘ injectBits → bitVecToℕ ∘ ℕToBitVec → toSigned ∘ fromSigned

private
  -- Core roundtrip: at the bytes level, extraction recovers the original raw value
  -- No Maybe, no guards - just the pure mathematical roundtrip
  --
  -- Pipeline:
  --   raw → fromSigned → ℕToBitVec → injectBits → extractBits → bitVecToℕ → toSigned → raw
  --
  -- Unsigned case: raw = + n
  signal-roundtrip-unsigned :
    ∀ {m} (n : ℕ) (bytes : Vec Byte m) (startBit bitLength : ℕ)
    → (fits-in-frame : startBit + bitLength ≤ m * 8)
    → (n<2^bl : n < 2 ^ bitLength)
    → toSigned (bitVecToℕ (extractBits {bitLength}
        (injectBits {bitLength} bytes startBit (ℕToBitVec {bitLength} n n<2^bl))
        startBit)) bitLength false ≡ + n
  signal-roundtrip-unsigned n bytes startBit bitLength fits-in-frame n<2^bl =
    cong +_ unsigned-roundtrip
    where
      -- Abbreviation for the BitVec
      bv : BitVec bitLength
      bv = ℕToBitVec {bitLength} n n<2^bl

      -- Chain: extractBits ∘ injectBits = id (Layer 1)
      bits-roundtrip : extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit ≡ bv
      bits-roundtrip = extractBits-injectBits-roundtrip {bitLength} bytes startBit bv fits-in-frame

      -- Chain: bitVecToℕ ∘ ℕToBitVec = id (Layer 1.5)
      nat-roundtrip : bitVecToℕ bv ≡ n
      nat-roundtrip = bitVec-roundtrip bitLength n n<2^bl

      -- Combined: extractedUnsigned ≡ n
      unsigned-roundtrip : bitVecToℕ (extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit) ≡ n
      unsigned-roundtrip = trans (cong bitVecToℕ bits-roundtrip) nat-roundtrip

  -- Signed case: use toSigned-fromSigned-roundtrip
  signal-roundtrip-signed :
    ∀ {m} (raw : ℤ) (bytes : Vec Byte m) (startBit bitLength : ℕ)
    → (bitLength>0 : bitLength > 0)
    → (fits-in-frame : startBit + bitLength ≤ m * 8)
    → (sf : SignedFits raw bitLength)
    → (fits-in-bits : fromSigned raw bitLength < 2 ^ bitLength)
    → toSigned (bitVecToℕ (extractBits {bitLength}
        (injectBits {bitLength} bytes startBit (ℕToBitVec {bitLength} (fromSigned raw bitLength) fits-in-bits))
        startBit)) bitLength true ≡ raw
  signal-roundtrip-signed raw bytes startBit bitLength bitLength>0 fits-in-frame sf fits-in-bits =
    signed-proof
    where
      -- Abbreviation for the BitVec
      bv : BitVec bitLength
      bv = ℕToBitVec {bitLength} (fromSigned raw bitLength) fits-in-bits

      -- Chain: extractBits ∘ injectBits = id (Layer 1)
      bits-roundtrip : extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit ≡ bv
      bits-roundtrip = extractBits-injectBits-roundtrip {bitLength} bytes startBit bv fits-in-frame

      -- Chain: bitVecToℕ ∘ ℕToBitVec = id (Layer 1.5)
      nat-roundtrip : bitVecToℕ bv ≡ fromSigned raw bitLength
      nat-roundtrip = bitVec-roundtrip bitLength (fromSigned raw bitLength) fits-in-bits

      -- Combined: extractedUnsigned ≡ fromSigned raw bitLength
      unsigned-roundtrip : bitVecToℕ (extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit) ≡ fromSigned raw bitLength
      unsigned-roundtrip = trans (cong bitVecToℕ bits-roundtrip) nat-roundtrip

      -- Chain: toSigned ∘ fromSigned = id (Layer 2)
      signed-proof : toSigned (bitVecToℕ (extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit)) bitLength true ≡ raw
      signed-proof = trans (cong (λ x → toSigned x bitLength true) unsigned-roundtrip)
                           (toSigned-fromSigned-roundtrip raw bitLength bitLength>0 sf)

-- ============================================================================
-- LAYER 4: A WRITTEN RAW VALUE READS BACK (through Maybe)
-- ============================================================================
-- Lifts the bytes-level roundtrip through extractSignal's bounds check and
-- scaling: the frame written with a raw value's bits extracts back to the
-- value the raw value scales to.  Big-endian: swapBytes is involutive, so the
-- swap around the write cancels the swap before the read.

-- ============================================================================
-- REDUCTION LEMMAS: what extractSignal computes on a written frame
-- ============================================================================

-- The frame `withInjected` writes from the raw value `n`'s bits, placed in
-- the payload by `injectPayload`, which handles the byte order.
injectedFrame : ∀ {m} (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → n < 2 ^ SignalDef.bitLength sig
  → CANFrame m
injectedFrame n sig byteOrder frame n<2^bl =
  withInjected (SignalDef.startBit sig) (ℕToBitVec {SignalDef.bitLength sig} n n<2^bl) byteOrder frame

-- Unsigned: extractSignal on injectedFrame returns the value `n` scales to.
extractSignal-reduces-unsigned :
  ∀ {m} (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (scaleExtracted (+ n) sig) (toℚ (SignalDef.minimum sig)) (toℚ (SignalDef.maximum sig)) ≡ true)
  → (unsigned : SignalDef.isSigned sig ≡ false)
  → (fits-in-frame : SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8)
  → (n<2^bl : n < 2 ^ SignalDef.bitLength sig)
  → extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just (scaleExtracted (+ n) sig)

-- LittleEndian case: no byte swapping
extractSignal-reduces-unsigned n sig LittleEndian frame bounds-ok unsigned fits-in-frame n<2^bl =
  helper core-eq bounds-ok
  where
    open SignalDef sig
      using (startBit; bitLength; isSigned)
      renaming (factor to factorᵈ; offset to offsetᵈ; minimum to minimumᵈ; maximum to maximumᵈ)
    open CANFrame frame

    factor = toℚ factorᵈ
    offset = toℚ offsetᵈ
    minimum = toℚ minimumᵈ
    maximum = toℚ maximumᵈ

    value : ℚ
    value = scaleExtracted (+ n) sig

    -- The bytes extracted from: for LittleEndian, `injectPayload` writes them
    -- with no swap.
    injectedBytes : Vec Byte _
    injectedBytes = injectBits {bitLength} payload startBit (ℕToBitVec {bitLength} n n<2^bl)

    -- Core roundtrip: extractSignalCore returns + n for unsigned signals
    core-eq : extractSignalCore injectedBytes sig ≡ + n
    core-eq rewrite unsigned = signal-roundtrip-unsigned n payload startBit (bitLength) fits-in-frame n<2^bl

    -- Factor out: what extractSignal returns given a raw value
    resultOf : ℤ → Maybe ℚ
    resultOf raw = let v = scaleExtracted raw sig
                   in if inBounds v minimum maximum then just v else nothing

    -- Helper: prove via composition
    -- Step 1: extractSignal computes resultOf applied to extractSignalCore
    -- Step 2: core-eq shows extractSignalCore gives + n
    -- Step 3: resultOf (+ n) = just value (by bounds-ok)
    helper : extractSignalCore injectedBytes sig ≡ + n
           → inBounds value minimum maximum ≡ true
           → extractSignal (injectedFrame n sig LittleEndian frame n<2^bl) sig LittleEndian ≡ just value
    helper core-eq' bounds-eq = trans step1 step2
      where
        -- extractSignal computes to resultOf (extractSignalCore injectedBytes sig)
        step1 : extractSignal (injectedFrame n sig LittleEndian frame n<2^bl) sig LittleEndian
              ≡ resultOf (extractSignalCore injectedBytes sig)
        step1 = refl

        -- resultOf (extractSignalCore ...) = resultOf (+ n) = just value
        step2 : resultOf (extractSignalCore injectedBytes sig) ≡ just value
        step2 rewrite core-eq' | bounds-eq = refl

-- BigEndian case: byte swapping cancels
extractSignal-reduces-unsigned n sig BigEndian frame bounds-ok unsigned fits-in-frame n<2^bl =
  helper swap-cancel core-eq bounds-ok
  where
    open SignalDef sig
      using (startBit; bitLength; isSigned)
      renaming (factor to factorᵈ; offset to offsetᵈ; minimum to minimumᵈ; maximum to maximumᵈ)
    open CANFrame frame

    factor = toℚ factorᵈ
    offset = toℚ offsetᵈ
    minimum = toℚ minimumᵈ
    maximum = toℚ maximumᵈ

    value : ℚ
    value = scaleExtracted (+ n) sig

    -- For BigEndian, injectedFrame's payload = swapBytes (injectBits (swapBytes payload) startBit bv)
    swappedPayload : Vec Byte _
    swappedPayload = swapBytes payload

    injectedBytesSwapped : Vec Byte _
    injectedBytesSwapped = injectBits {bitLength} swappedPayload startBit (ℕToBitVec {bitLength} n n<2^bl)

    -- extractionBytes (injectedFrame ...) BigEndian = swapBytes (swapBytes injectedBytesSwapped) = injectedBytesSwapped
    swap-cancel : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
    swap-cancel = swapBytes-involutive injectedBytesSwapped

    -- Core roundtrip on the swapped payload
    core-eq : extractSignalCore injectedBytesSwapped sig ≡ + n
    core-eq rewrite unsigned = signal-roundtrip-unsigned n swappedPayload startBit (bitLength) fits-in-frame n<2^bl

    -- Factor out: what extractSignal returns given bytes to extract from
    resultOf : Vec Byte _ → Maybe ℚ
    resultOf bytes = let raw = extractSignalCore bytes sig
                         v = scaleExtracted raw sig
                     in if inBounds v minimum maximum then just v else nothing

    -- Helper: compose the equality proofs
    helper : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
           → extractSignalCore injectedBytesSwapped sig ≡ + n
           → inBounds value minimum maximum ≡ true
           → extractSignal (injectedFrame n sig BigEndian frame n<2^bl) sig BigEndian ≡ just value
    helper swap-eq core-eq' bounds-eq = trans step1 (trans step2 step3)
      where
        -- extractSignal for BigEndian extracts from swapBytes of the payload
        -- payload of injectedFrame = swapBytes injectedBytesSwapped
        -- extractionBytes (injectedFrame ...) BigEndian = swapBytes (swapBytes injectedBytesSwapped)
        step1 : extractSignal (injectedFrame n sig BigEndian frame n<2^bl) sig BigEndian
              ≡ resultOf (swapBytes (swapBytes injectedBytesSwapped))
        step1 = refl

        -- swapBytes (swapBytes x) = x
        step2 : resultOf (swapBytes (swapBytes injectedBytesSwapped)) ≡ resultOf injectedBytesSwapped
        step2 = cong resultOf swap-eq

        -- resultOf injectedBytesSwapped = just value (via core-eq and bounds-ok)
        step3 : resultOf injectedBytesSwapped ≡ just value
        step3 rewrite core-eq' | bounds-eq = refl

-- ============================================================================
-- LAYER 4B: SIGNED SIGNAL ROUNDTRIP
-- ============================================================================
-- Same pattern as unsigned, but uses SignedFits constraint and toSigned true

-- Signed: extractSignal on injectedFrame returns the value `z` scales to,
-- through signal-roundtrip-signed (toSigned with isSigned = true).
extractSignal-reduces-signed :
  ∀ {m} (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (scaleExtracted z sig) (toℚ (SignalDef.minimum sig)) (toℚ (SignalDef.maximum sig)) ≡ true)
  → (signed : SignalDef.isSigned sig ≡ true)
  → (bl>0 : SignalDef.bitLength sig > 0)
  → (sf : SignedFits z (SignalDef.bitLength sig))
  → (fits-in-frame : SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8)
  → let n = fromSigned z (SignalDef.bitLength sig)
        n<2^bl = SignedFits-implies-fromSigned-bounded z (SignalDef.bitLength sig) bl>0 sf
    in extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just (scaleExtracted z sig)

-- LittleEndian case: no byte swapping
extractSignal-reduces-signed z sig LittleEndian frame bounds-ok signed bl>0 sf fits-in-frame =
  helper core-eq bounds-ok
  where
    open SignalDef sig
      using (startBit; bitLength; isSigned)
      renaming (factor to factorᵈ; offset to offsetᵈ; minimum to minimumᵈ; maximum to maximumᵈ)
    open CANFrame frame

    factor = toℚ factorᵈ
    offset = toℚ offsetᵈ
    minimum = toℚ minimumᵈ
    maximum = toℚ maximumᵈ

    value : ℚ
    value = scaleExtracted z sig

    n : ℕ
    n = fromSigned z (bitLength)

    n<2^bl : n < 2 ^ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (bitLength) bl>0 sf

    -- The bytes we extract from
    injectedBytes : Vec Byte _
    injectedBytes = injectBits {bitLength} payload startBit (ℕToBitVec {bitLength} n n<2^bl)

    -- Core roundtrip: extractSignalCore returns z for signed signals
    core-eq : extractSignalCore injectedBytes sig ≡ z
    core-eq rewrite signed = signal-roundtrip-signed z payload startBit (bitLength) bl>0 fits-in-frame sf n<2^bl

    -- Factor out: what extractSignal returns given a raw value
    resultOf : ℤ → Maybe ℚ
    resultOf raw = let v = scaleExtracted raw sig
                   in if inBounds v minimum maximum then just v else nothing

    -- Helper: prove via composition
    helper : extractSignalCore injectedBytes sig ≡ z
           → inBounds value minimum maximum ≡ true
           → extractSignal (injectedFrame n sig LittleEndian frame n<2^bl) sig LittleEndian ≡ just value
    helper core-eq' bounds-eq = trans step1 step2
      where
        step1 : extractSignal (injectedFrame n sig LittleEndian frame n<2^bl) sig LittleEndian
              ≡ resultOf (extractSignalCore injectedBytes sig)
        step1 = refl

        step2 : resultOf (extractSignalCore injectedBytes sig) ≡ just value
        step2 rewrite core-eq' | bounds-eq = refl

-- BigEndian case: byte swapping cancels
extractSignal-reduces-signed z sig BigEndian frame bounds-ok signed bl>0 sf fits-in-frame =
  helper swap-cancel core-eq bounds-ok
  where
    open SignalDef sig
      using (startBit; bitLength; isSigned)
      renaming (factor to factorᵈ; offset to offsetᵈ; minimum to minimumᵈ; maximum to maximumᵈ)
    open CANFrame frame

    factor = toℚ factorᵈ
    offset = toℚ offsetᵈ
    minimum = toℚ minimumᵈ
    maximum = toℚ maximumᵈ

    value : ℚ
    value = scaleExtracted z sig

    n : ℕ
    n = fromSigned z (bitLength)

    n<2^bl : n < 2 ^ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (bitLength) bl>0 sf

    -- For BigEndian, injectedFrame's payload = swapBytes (injectBits (swapBytes payload) startBit bv)
    swappedPayload : Vec Byte _
    swappedPayload = swapBytes payload

    injectedBytesSwapped : Vec Byte _
    injectedBytesSwapped = injectBits {bitLength} swappedPayload startBit (ℕToBitVec {bitLength} n n<2^bl)

    -- extractionBytes (injectedFrame ...) BigEndian = swapBytes (swapBytes injectedBytesSwapped) = injectedBytesSwapped
    swap-cancel : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
    swap-cancel = swapBytes-involutive injectedBytesSwapped

    -- Core roundtrip on the swapped payload
    core-eq : extractSignalCore injectedBytesSwapped sig ≡ z
    core-eq rewrite signed = signal-roundtrip-signed z swappedPayload startBit (bitLength) bl>0 fits-in-frame sf n<2^bl

    -- Factor out: what extractSignal returns given bytes to extract from
    resultOf : Vec Byte _ → Maybe ℚ
    resultOf bytes = let raw = extractSignalCore bytes sig
                         v = scaleExtracted raw sig
                     in if inBounds v minimum maximum then just v else nothing

    -- Helper: compose the equality proofs
    helper : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
           → extractSignalCore injectedBytesSwapped sig ≡ z
           → inBounds value minimum maximum ≡ true
           → extractSignal (injectedFrame n sig BigEndian frame n<2^bl) sig BigEndian ≡ just value
    helper swap-eq core-eq' bounds-eq = trans step1 (trans step2 step3)
      where
        step1 : extractSignal (injectedFrame n sig BigEndian frame n<2^bl) sig BigEndian
              ≡ resultOf (swapBytes (swapBytes injectedBytesSwapped))
        step1 = refl

        step2 : resultOf (swapBytes (swapBytes injectedBytesSwapped)) ≡ resultOf injectedBytesSwapped
        step2 = cong resultOf swap-eq

        step3 : resultOf injectedBytesSwapped ≡ just value
        step3 rewrite core-eq' | bounds-eq = refl
