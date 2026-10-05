-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Reading a signal from a CAN frame, and writing a signal's bits into one.
--
-- Operations: extractSignal (frame + signal → physical value with scaling),
--             withInjected (frame layer: a bit vector written at a start bit
--             in a byte order, nothing else known of it).
-- Encoding a value into those bits is Aletheia.CAN.Encoding.Value's.
-- Role: Core CAN processing, used by protocol handlers and verification.
--
-- Algorithm: Bit extraction → endianness conversion → sign extension → scaling (factor/offset).
-- Verified: All bit manipulations use structural BitVec proofs for safety.
module Aletheia.CAN.Encoding where

open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.CAN.Signal using (SignalDef; SignalValue)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; swapBytes; extractBits; extractRaw; extractRaw-extractBits; injectPayload; injectPayload-below256)
open import Aletheia.CAN.Encoding.Arithmetic using (toSigned; applyScaling; inBounds)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ)
open import Data.Rational using (ℚ)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.Bool using (if_then_else_)
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

-- ============================================================================
-- COMPUTATIONAL CORE: Pure functions for proof ergonomics
-- ============================================================================
-- These are factored out from extractSignal to enable clean rewriting in proofs.
-- No Maybe, no with, no Dec - just math.

-- Extract raw signed integer from bytes (no bounds check, no scaling)
extractSignalCore : ∀ {m} → Vec Byte m → SignalDef → ℤ
extractSignalCore bytes sig =
  let open SignalDef sig in
  toSigned
    (bitVecToℕ (extractBits {bitLength} bytes (startBit)))
    (bitLength)
    isSigned

-- Byte-at-a-time signal extraction (efficient for MAlonzo: ~8x fewer Vec walks)
-- Same result as extractSignalCore but uses extractRaw instead of extractBits.
extractSignalCoreFast : ∀ {m} → Vec Byte m → SignalDef → ℤ
extractSignalCoreFast {m} bytes sig =
  let open SignalDef sig in
  toSigned (extractRaw m bytes startBit bitLength) bitLength isSigned

-- Correctness: extractSignalCoreFast computes the same value as extractSignalCore
extractSignalCoreFast-equiv : ∀ {m} (bytes : Vec Byte m) (sig : SignalDef)
  → extractSignalCoreFast bytes sig ≡ extractSignalCore bytes sig
extractSignalCoreFast-equiv {m} bytes sig =
  let open SignalDef sig in
  cong (λ v → toSigned v bitLength isSigned) (extractRaw-extractBits m bytes startBit bitLength)

-- Apply scaling to raw extracted value.  SignalDef.factor / offset are
-- stored as `DecRat` for exact DBC text roundtrip; `applyScaling` is
-- ℚ-algebra, so the conversion happens once per signal per frame at
-- this boundary.
scaleExtracted : ℤ → SignalDef → ℚ
scaleExtracted raw sig = applyScaling raw (toℚ (SignalDef.factor sig)) (toℚ (SignalDef.offset sig))

-- Get the bytes to extract from (handles byte order)
extractionBytes : ∀ {m} → CANFrame m → ByteOrder → Vec Byte m
extractionBytes frame LittleEndian = CANFrame.payload frame
extractionBytes frame BigEndian = swapBytes (CANFrame.payload frame)

-- ============================================================================

-- Extract a signal from a CAN frame: a thin wrapper around the computational
-- core.
extractSignal : ∀ {m} → CANFrame m → SignalDef → ByteOrder → Maybe SignalValue
extractSignal frame sig byteOrder =
  let bytes = extractionBytes frame byteOrder
      raw = extractSignalCore bytes sig
      value = scaleExtracted raw sig
  in if inBounds value (toℚ (SignalDef.minimum sig)) (toℚ (SignalDef.maximum sig))
     then just value
     -- Value outside [minimum, maximum].  The streaming hot path
     -- (`extractSignalDirect`) bypasses this helper entirely — it calls
     -- `extractSignalCoreFast` + `scaleExtracted` + `inBounds` directly
     -- and routes the out-of-bounds case as `ValueOutOfBounds`.
     -- At run time this `nothing` is reached only from `matchMuxValue`,
     -- which reports a multiplexor value outside its declared range as
     -- `MuxExtractionFailed`.
     else nothing

-- The frame with `bits` written at `s` in the given byte order; the bytes
-- written keep the frame's byte range (`injectPayload-below256`).
withInjected : ∀ {len m} → ℕ → BitVec len → ByteOrder → CANFrame m → CANFrame m
withInjected s bits bo record { id = i ; dlc = d ; payload = v ; below256 = ok } =
  record { id = i ; dlc = d ; payload = injectPayload s bits bo v ; below256 = injectPayload-below256 s bits bo ok }
