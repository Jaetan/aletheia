{-# OPTIONS --safe --without-K #-}

-- Signal extraction and injection from CAN frames (bit-level operations).
--
-- Purpose: Extract/inject signal values from CAN frames using DBC definitions.
-- Operations: extractSignal (frame + signal → physical value with scaling),
--             injectSignal (physical value + signal → frame with updated bits).
-- Role: Core CAN processing, used by protocol handlers and verification.
--
-- Algorithm: Bit extraction → endianness conversion → sign extension → scaling (factor/offset).
-- Verified: All bit manipulations use structural BitVec proofs for safety.
module Aletheia.CAN.Encoding where

open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.CAN.Signal using (SignalDef; SignalValue)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; isBigEndian; swapBytes; extractBits; extractRaw; extractRaw-extractBits; injectBits; _≟-ByteOrder_)
open import Aletheia.CAN.Encoding.Arithmetic using (toSigned; fromSigned; applyScaling; removeScaling; inBounds)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ; ℕToBitVec)
open import Data.Nat using (ℕ; _^_; _<_; _<?_)
open import Data.Rational using (ℚ)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

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

-- Apply scaling to raw extracted value
scaleExtracted : ℤ → SignalDef → ℚ
scaleExtracted raw sig = applyScaling raw (SignalDef.factor sig) (SignalDef.offset sig)

-- Get the bytes to extract from (handles byte order)
extractionBytes : ∀ {m} → CANFrame m → ByteOrder → Vec Byte m
extractionBytes frame LittleEndian = CANFrame.payload frame
extractionBytes frame BigEndian = swapBytes (CANFrame.payload frame)

-- ============================================================================

-- Extract a signal from a CAN frame
-- Now a thin wrapper around the computational core
extractSignal : ∀ {m} → CANFrame m → SignalDef → ByteOrder → Maybe SignalValue
extractSignal frame sig byteOrder =
  let bytes = extractionBytes frame byteOrder
      raw = extractSignalCore bytes sig
      value = scaleExtracted raw sig
  in if inBounds value (SignalDef.minimum sig) (SignalDef.maximum sig)
     then just value
     -- Value outside [minimum, maximum]: reachable via matchMuxValue (mux
     -- selector value doesn't match any expected value) and via
     -- extractSignalDirect (which handles this case separately as
     -- ValueOutOfBounds). The main batch extraction path
     -- (extractSignalDirect) never sees this nothing — it calls
     -- extractSignalCoreFast + scaleExtracted + inBounds directly.
     else nothing

-- Inject a signal value into a CAN frame
injectSignal : ∀ {m} → SignalValue → SignalDef → ByteOrder → CANFrame m → Maybe (CANFrame m)
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
    -- Deferred Bool fast path (AA-16.5): the `_<?_` guard below builds a
    -- `Dec (fromSigned … < 2 ^ bitLength)` per signal per frame-build.
    -- A `_<ᵇ_` + `<ᵇ⇒<` refactor would avoid the per-call Dec allocation,
    -- but the proof files `Encoding/Properties/Roundtrip.agda` (via the
    -- `fits-check` / `dec-yes-irr` / `inject-reduces` lemmas) and
    -- `Encoding/Properties/Disjoint.agda` (via `with … <? … | yes bounded`
    -- patterns at lines 68 and 138) structurally pattern-match on this
    -- `Dec`. Switching the guard requires rewriting those proofs to use
    -- `with … <ᵇ … in eq` plus a `<ᵇ⇒<` bridge in every lemma, which
    -- is a larger proof refactor than the marginal `removeScaling`-dominated
    -- frame-build throughput gain justifies. Left as-is pending a measured
    -- Frame Building regression or a dedicated proof-refactor pass.
    -- (Post-Round-8 Batch 1 benchmarks: Frame Building +1.5%/+4.3% for
    -- C++/CAN-FD; -2.7%/+1.8% for Go; within noise of the 5% gate.)
    injectHelper : ∀ {m} → SignalValue → SignalDef → ByteOrder → CANFrame m → Maybe (CANFrame m)
    injectHelper {m} value signalDef byteOrder frame
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
          bytes : Vec Byte m
          bytes = if isBigEndian byteOrder
                  then swapBytes payload
                  else payload
          updatedBytes : Vec Byte m
          updatedBytes = injectBits bytes (startBit) rawBitVec
          finalBytes : Vec Byte m
          finalBytes = if isBigEndian byteOrder
                       then swapBytes updatedBytes
                       else updatedBytes
      in just (record frame { payload = finalBytes })

-- Disjoint bit preservation proofs moved to CAN/Encoding/Properties.agda:
-- extractionBytes≡payloadIso, injectSignal-preserves-disjoint-bits,
-- injectSignal-preserves-disjoint-bits-physical
