-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
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
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; isBigEndian; swapBytes; extractBits; extractRaw; extractRaw-extractBits; injectBits)
open import Aletheia.CAN.Encoding.Arithmetic using (toSigned; fromSigned; applyScaling; removeScaling; inBounds)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.Data.BitVec using ()
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ; mkBoundedBitVec)
open import Data.Rational using (ℚ)
open import Data.Integer using (ℤ)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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

-- Extract a signal from a CAN frame
-- Now a thin wrapper around the computational core
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
     -- This `nothing` is reachable only from `matchMuxValue` (mux selector
     -- value doesn't match any expected value).
     else nothing

-- Helper for injectSignal: actual injection given that the ℚ-level
-- bounds check has already passed.  Lifted from a where-block in
-- `injectSignal` to top-level so proofs can name it directly and reason
-- about its body in isolation — instead of mirroring `injectSignal`'s
-- full 3-deep `with`-chain (bounds + removeScaling + Dec), proofs
-- compose `injectSignal-bounds-true` with `injectHelper-reduces-*`.
--
-- Bool fast path: bounds-fits check uses `mkBoundedBitVec` (Bool dispatch
-- via `<ᵇ-reflects-<` from stdlib), not the previous `_<?_` (Dec).
-- MAlonzo allocation per frame-build drops from one `Dec` constructor
-- (yes/no + bound-witness slot, where the slot is `@0`-erased per R19
-- cluster D) to one `Maybe` constructor (just/nothing).  The bound proof
-- needed by `ℕToBitVec` is constructed in `mkBoundedBitVec`'s `ofʸ` arm
-- from the `Reflects` payload and flows into ℕToBitVec's @0-erased slot —
-- structurally cleaner than the prior `<?`-based form.
--
-- See `Aletheia.Data.BitVec.Conversion.mkBoundedBitVec` for the smart
-- constructor and `mkBoundedBitVec-just` for its reduction equation
-- (consumed by `injectHelper-reduces-*` in Encoding/Properties/Roundtrip).
injectHelper : ∀ {m} → SignalValue → SignalDef → ByteOrder → CANFrame m → Maybe (CANFrame m)
injectHelper {m} value signalDef byteOrder frame
  with removeScaling value (toℚ (SignalDef.factor signalDef)) (toℚ (SignalDef.offset signalDef))
... | nothing = nothing
... | just rawSigned
  with mkBoundedBitVec (fromSigned rawSigned (SignalDef.bitLength signalDef)) (SignalDef.bitLength signalDef)
-- AGDA-B-18.3 — STRUCTURAL DEAD BRANCH — DO NOT RE-RAISE IN REVIEW.
-- The `nothing` arm below is structurally required by Agda's coverage
-- checker (`mkBoundedBitVec`'s codomain is `Maybe (BitVec _)`, so both
-- ctors must be handled) but is provably unreachable from any call site:
-- the only producer of `rawSigned` here is `removeScaling`, whose output
-- (when `just`) is bound to fit `2 ^ bitLength` by the upstream
-- `inBounds` guard composed with `SignalDef`'s well-formedness invariants
-- (`factor-nonzero` + `ranges-consistent`, both consumed by
-- `removeScaling-applyScaling-exact` in proofs).  Encoding the branch
-- as unreachable at the type level would require either (a) a refined
-- `Maybe`-with-conditional-emptiness type that no stdlib primitive
-- consumes, or (b) threading a `WellFormedSignal` precondition through
-- every call site (CAN/BatchFrameBuilding, Protocol/Handlers, …) —
-- ~30+ call sites, cascading proof refactor, no runtime impact.
-- The branch is dead-code-eliminable by GHC's strictness analyzer
-- (it returns `Nothing` without further work).
...   | nothing = nothing
...   | just rawBitVec =
  let open CANFrame frame
      open SignalDef signalDef
      -- Inject bits
      bytes : Vec Byte m
      bytes = if isBigEndian byteOrder
              then swapBytes payload
              else payload
      updatedBytes : Vec Byte m
      updatedBytes = injectBits bytes startBit rawBitVec
      finalBytes : Vec Byte m
      finalBytes = if isBigEndian byteOrder
                   then swapBytes updatedBytes
                   else updatedBytes
  in just (record frame { payload = finalBytes })

-- Inject a signal value into a CAN frame
injectSignal : ∀ {m} → SignalValue → SignalDef → ByteOrder → CANFrame m → Maybe (CANFrame m)
injectSignal value signalDef byteOrder frame =
  if inBounds value (toℚ (SignalDef.minimum signalDef)) (toℚ (SignalDef.maximum signalDef))
  then injectHelper value signalDef byteOrder frame
  else nothing

-- Reduction lemma: when bounds check passes, `injectSignal` is `injectHelper`.
-- Used by proofs to dispatch the outer `inBounds` guard in one rewrite
-- instead of opening a `with`-abstraction.
injectSignal-bounds-true : ∀ {m} (v : SignalValue) (sig : SignalDef) (bo : ByteOrder) (f : CANFrame m)
  → inBounds v (toℚ (SignalDef.minimum sig)) (toℚ (SignalDef.maximum sig)) ≡ true
  → injectSignal v sig bo f ≡ injectHelper v sig bo f
injectSignal-bounds-true v sig bo f bounds-eq rewrite bounds-eq = refl

-- Reduction lemma: when bounds check fails, `injectSignal` is `nothing`.
injectSignal-bounds-false : ∀ {m} (v : SignalValue) (sig : SignalDef) (bo : ByteOrder) (f : CANFrame m)
  → inBounds v (toℚ (SignalDef.minimum sig)) (toℚ (SignalDef.maximum sig)) ≡ false
  → injectSignal v sig bo f ≡ nothing
injectSignal-bounds-false v sig bo f bounds-eq rewrite bounds-eq = refl

-- Disjoint bit preservation proofs moved to CAN/Encoding/Properties.agda:
-- extractionBytes≡payloadIso, injectSignal-preserves-disjoint-bits,
-- injectSignal-preserves-disjoint-bits-physical
