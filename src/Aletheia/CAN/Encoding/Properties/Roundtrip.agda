{-# OPTIONS --safe --without-K #-}

-- Full signal encoding/decoding roundtrip proofs.
--
-- Purpose: Layer 4 composition — combines the bit-level roundtrip
--   (Endianness.Properties), the ℕ ↔ ℤ signed/unsigned bridge (Arithmetic),
--   and the ℚ scaling roundtrip (Arithmetic) into the headline theorems
--   `extractSignal-injectSignal-roundtrip-unsigned` / `-signed`, which state
--   that `extractSignal ∘ injectSignal` is the identity on well-formed
--   signals/frames.
--
-- Layering (this file):
--   * Layer 4A (core bytes-level roundtrip, private): raw → ℕToBitVec →
--     injectBits → extractBits → bitVecToℕ → toSigned chains for unsigned
--     and signed cases. No Maybe, no guards — pure bytes-level reasoning.
--   * Layer 4 (full Maybe-threaded roundtrip): `signalValue`, `injectedFrame`,
--     reduction lemmas `injectSignal-reduces-*` and `extractSignal-reduces-*`,
--     and the composed `extractSignal-injectSignal-roundtrip-*` theorems.
--   * Layer 4B (signed variant): mirrors Layer 4 with `SignedFits` instead
--     of `n < 2^bl` and `toSigned _ true` at the end.
--
-- Imports from Arithmetic sibling: SignedFits, toSigned-fromSigned-roundtrip,
--   removeScaling-applyScaling-exact. No other files in the project need the
--   private Layer 4A helpers.
module Aletheia.CAN.Encoding.Properties.Roundtrip where

open import Aletheia.CAN.Encoding using (extractSignalCore; scaleExtracted; extractionBytes; extractSignal; injectSignal)
open import Aletheia.CAN.Encoding.Arithmetic using (toSigned; fromSigned; applyScaling; removeScaling; inBounds)
open import Aletheia.CAN.Encoding.Properties.Arithmetic using (SignedFits; toSigned-fromSigned-roundtrip; removeScaling-applyScaling-exact)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; extractBits; injectBits; swapBytes; injectPayload; payloadIso)
open import Aletheia.CAN.Endianness.Properties using (extractBits-injectBits-roundtrip; swapBytes-involutive; payloadIso-involutive)
open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ; ℕToBitVec; bitVec-roundtrip)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _<?_; _≤_; _^_; _>_; z≤n; s≤s)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)

-- ============================================================================
-- LAYER 4: COMPOSITION - FULL ROUNDTRIP
-- ============================================================================
-- Combine all layers into the full signal extraction/injection proof

-- Helper: Define when a signal definition is well-formed
record WellFormedSignal (sig : SignalDef) : Set where
  field
    startBit-bounded : SignalDef.startBit sig < 64
    bitLength-positive : SignalDef.bitLength sig > 0
    bitLength-fits : SignalDef.startBit sig + SignalDef.bitLength sig ≤ 64
    factor-nonzero : ¬ (SignalDef.factor sig ≡ 0ℚ)
    ranges-consistent : SignalDef.minimum sig Data.Rational.≤ SignalDef.maximum sig

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER 4A: Core roundtrip (pure bytes level, no Maybe/guards)
-- ═══════════════════════════════════════════════════════════════════════════
-- Chain: extractBits ∘ injectBits → bitVecToℕ ∘ ℕToBitVec → toSigned ∘ fromSigned

private
  -- Helper: SignedFits implies fromSigned is bounded
  -- This is the direction we need for injectSignal's guard
  SignedFits-implies-fromSigned-bounded : ∀ (raw : ℤ) (bitLength : ℕ)
    → bitLength > 0
    → SignedFits raw bitLength
    → fromSigned raw bitLength < 2 ^ bitLength
  SignedFits-implies-fromSigned-bounded (+ n) bitLength bl>0 n<half =
    -- n < 2^(bl-1) < 2^bl
    <-trans n<half (half<full bitLength bl>0)
    where
      open import Data.Nat.Properties as ℕP using (<-trans; ^-monoʳ-<; n<1+n; ≤-refl)
      -- 2^(bl-1) < 2^bl follows from 1<2 and bl-1 < bl
      half<full : ∀ bl → bl > 0 → 2 ^ (bl ∸ 1) < 2 ^ bl
      half<full (suc bl) _ = ^-monoʳ-< 2 1<2 (n<1+n bl)
        where
          1<2 : 1 < 2
          1<2 = s≤s (s≤s z≤n)
  SignedFits-implies-fromSigned-bounded -[1+ n ] bitLength bl>0 sucn≤half =
    -- fromSigned -[1+ n] bl = 2^bl - suc n
    -- Need: 2^bl - suc n < 2^bl, which is always true when 2^bl > 0
    m∸sucn<m (2 ^ bitLength) n (m^n>0 2 bitLength)
    where
      open import Data.Nat.Properties using (m∸n≤m; m^n>0)
      -- m ∸ suc n < m when m > 0
      m∸sucn<m : ∀ m n → m > 0 → m ∸ suc n < m
      m∸sucn<m (suc m) n _ = s≤s (m∸n≤m m n)

  -- Unified constraint: combines what we need for roundtrip
  -- For unsigned: raw is non-negative
  -- For signed: raw satisfies SignedFits
  data RawFits (raw : ℤ) (bitLength : ℕ) : Bool → Set where
    unsigned-fits : ∀ {n} → raw ≡ + n → n < 2 ^ bitLength → RawFits raw bitLength false
    signed-fits : SignedFits raw bitLength → RawFits raw bitLength true

  -- Derive fromSigned bound from RawFits
  RawFits-implies-bounded : ∀ (raw : ℤ) (bitLength : ℕ) (isSigned : Bool)
    → bitLength > 0
    → RawFits raw bitLength isSigned
    → fromSigned raw bitLength < 2 ^ bitLength
  RawFits-implies-bounded .(+ n) bitLength false bl>0 (unsigned-fits {n} refl n<2^bl) = n<2^bl
  RawFits-implies-bounded raw bitLength true bl>0 (signed-fits sf) =
    SignedFits-implies-fromSigned-bounded raw bitLength bl>0 sf

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
-- LAYER 4: FULL SIGNAL ROUNDTRIP (through Maybe)
-- ============================================================================
-- The full composition: extractSignal ∘ injectSignal = id
-- This lifts the pure bytes-level roundtrip through Maybe and handles:
-- - Bounds checking guards
-- - Scaling operations
-- - Byte order swapping

{-
  Strategy: The full roundtrip proof requires showing that:
  1. injectSignal value sig byteOrder frame = just frame'
     (when bounds pass, removeScaling succeeds, and raw fits)
  2. extractSignal frame' sig byteOrder = just value
     (because we extract the same bits → same raw → same value)

  The key insight is that for a value = applyScaling raw factor offset,
  removeScaling will return exactly raw (no floor precision loss).

  Endianness handling: swapBytes is involutive, so:
  - Big-endian: swap → inject → swap → extract → swap
    The first swap-swap pair cancels, leaving inject → extract
-}

-- Full roundtrip theorem: extractSignal ∘ injectSignal = id
-- Preconditions:
-- 1. value = applyScaling raw factor offset (ensures removeScaling recovers raw exactly)
-- 2. inBounds value min max ≡ true (bounds check passes)
-- 3. factor ≢ 0 (well-formed signal)
-- 4. fits-in-bits: fromSigned raw bitLength < 2^bitLength

-- For now, we state the theorem for the unsigned case (isSigned = false)
-- The signed case follows the same structure with SignedFits constraint

-- Helper: compute signal value from raw integer
signalValue : ℤ → SignalDef → ℚ
signalValue raw sig = applyScaling raw (SignalDef.factor sig) (SignalDef.offset sig)

-- ============================================================================
-- REDUCTION LEMMAS: State exactly what injectSignal/extractSignal compute
-- ============================================================================

-- Helper: compute the frame that injectSignal produces
-- Uses injectPayload abstraction to factor out byte order handling
injectedFrame : ∀ {m} (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → n < 2 ^ SignalDef.bitLength sig
  → CANFrame m
injectedFrame n sig byteOrder frame n<2^bl =
  record frame { payload = injectPayload (SignalDef.startBit sig) (ℕToBitVec {SignalDef.bitLength sig} n n<2^bl) byteOrder (CANFrame.payload frame) }

-- Reduction Lemma A: injectSignal reduces to a known frame
-- This is more useful than existence because it eliminates ∃ from proofs
injectSignal-reduces-unsigned :
  ∀ {m} (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (signalValue (+ n) sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (n<2^bl : n < 2 ^ SignalDef.bitLength sig)
  → injectSignal (signalValue (+ n) sig) sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
injectSignal-reduces-unsigned n sig byteOrder frame bounds-ok factor≢0 n<2^bl =
  helper bounds-ok remove-eq fits-check
  where
    open SignalDef sig
    open CANFrame frame
    open import Relation.Nullary.Decidable using (dec-yes-irr)
    open import Data.Nat.Properties using (<-irrelevant)

    value : ℚ
    value = signalValue (+ n) sig

    remove-eq : removeScaling value factor offset ≡ just (+ n)
    remove-eq = removeScaling-applyScaling-exact (+ n) factor offset factor≢0

    fits-check : (n Data.Nat.<? 2 ^ bitLength) ≡ yes n<2^bl
    fits-check = dec-yes-irr (n Data.Nat.<? 2 ^ bitLength) <-irrelevant n<2^bl

    helper : inBounds value minimum maximum ≡ true
           → removeScaling value factor offset ≡ just (+ n)
           → (n Data.Nat.<? 2 ^ bitLength) ≡ yes n<2^bl
           → injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    helper bounds-eq remove-eq' fits-eq
      with inBounds value minimum maximum
    helper bounds-eq remove-eq' fits-eq | true
      with removeScaling value factor offset | remove-eq'
    ... | just .(+ n) | refl
      with n Data.Nat.<? 2 ^ bitLength | fits-eq
    ... | yes .n<2^bl | refl = refl
    helper () _ _ | false

-- Reduction Lemma B: extractSignal on injectedFrame returns the original value
-- Now uses the refactored extractSignal with computational core
extractSignal-reduces-unsigned :
  ∀ {m} (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (signalValue (+ n) sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (unsigned : SignalDef.isSigned sig ≡ false)
  → (fits-in-frame : SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8)
  → (n<2^bl : n < 2 ^ SignalDef.bitLength sig)
  → extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just (signalValue (+ n) sig)

-- LittleEndian case: no byte swapping
extractSignal-reduces-unsigned n sig LittleEndian frame bounds-ok unsigned fits-in-frame n<2^bl =
  helper core-eq bounds-ok
  where
    open SignalDef sig
    open CANFrame frame
    value : ℚ
    value = signalValue (+ n) sig

    -- The bytes we extract from (definitional for LittleEndian via injectPayload)
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
    open CANFrame frame
    value : ℚ
    value = signalValue (+ n) sig

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

extractSignal-injectSignal-roundtrip-unsigned :
  ∀ {m} (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (signalValue (+ n) sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (unsigned : SignalDef.isSigned sig ≡ false)
  → (fits-in-frame : SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8)
  → (n<2^bl : n < 2 ^ SignalDef.bitLength sig)
  → (injectSignal (signalValue (+ n) sig) sig byteOrder frame >>= λ frame' →
       extractSignal frame' sig byteOrder) ≡ just (signalValue (+ n) sig)
extractSignal-injectSignal-roundtrip-unsigned n sig byteOrder frame bounds-ok factor≢0 unsigned fits-in-frame n<2^bl =
  proof
  where
    value : ℚ
    value = signalValue (+ n) sig

    -- Reduction lemma: injectSignal computes to just (injectedFrame ...)
    inject-reduces : injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    inject-reduces = injectSignal-reduces-unsigned n sig byteOrder frame bounds-ok factor≢0 n<2^bl

    -- Reduction lemma: extractSignal on injectedFrame returns just value
    extract-reduces : extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just value
    extract-reduces = extractSignal-reduces-unsigned n sig byteOrder frame bounds-ok unsigned fits-in-frame n<2^bl

    -- Compose by rewriting: inject >>= extract = just injectedFrame >>= extract = extract injectedFrame = just value
    proof : (injectSignal value sig byteOrder frame >>= λ f → extractSignal f sig byteOrder) ≡ just value
    proof rewrite inject-reduces = extract-reduces

-- ============================================================================
-- LAYER 4B: SIGNED SIGNAL ROUNDTRIP
-- ============================================================================
-- Same pattern as unsigned, but uses SignedFits constraint and toSigned true

-- Reduction Lemma A (Signed): injectSignal reduces to a known frame
-- The raw value is fromSigned z bitLength, which we prove fits in bitLength bits
injectSignal-reduces-signed :
  ∀ {m} (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (signalValue z sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (bl>0 : SignalDef.bitLength sig > 0)
  → (sf : SignedFits z (SignalDef.bitLength sig))
  → let n = fromSigned z (SignalDef.bitLength sig)
        n<2^bl = SignedFits-implies-fromSigned-bounded z (SignalDef.bitLength sig) bl>0 sf
    in injectSignal (signalValue z sig) sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
injectSignal-reduces-signed z sig byteOrder frame bounds-ok factor≢0 bl>0 sf =
  helper bounds-ok remove-eq fits-check
  where
    open SignalDef sig
    open CANFrame frame
    open import Relation.Nullary.Decidable using (dec-yes-irr)
    open import Data.Nat.Properties using (<-irrelevant)

    value : ℚ
    value = signalValue z sig

    n : ℕ
    n = fromSigned z (bitLength)

    n<2^bl : n < 2 ^ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (bitLength) bl>0 sf

    remove-eq : removeScaling value factor offset ≡ just z
    remove-eq = removeScaling-applyScaling-exact z factor offset factor≢0

    fits-check : (n Data.Nat.<? 2 ^ bitLength) ≡ yes n<2^bl
    fits-check = dec-yes-irr (n Data.Nat.<? 2 ^ bitLength) <-irrelevant n<2^bl

    helper : inBounds value minimum maximum ≡ true
           → removeScaling value factor offset ≡ just z
           → (n Data.Nat.<? 2 ^ bitLength) ≡ yes n<2^bl
           → injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    helper bounds-eq remove-eq' fits-eq
      with inBounds value minimum maximum
    helper bounds-eq remove-eq' fits-eq | true
      with removeScaling value factor offset | remove-eq'
    ... | just .z | refl
      with n Data.Nat.<? 2 ^ bitLength | fits-eq
    ... | yes .n<2^bl | refl = refl
    helper () _ _ | false

-- Reduction Lemma B (Signed): extractSignal on injectedFrame returns the original value
-- Uses signal-roundtrip-signed which uses toSigned with isSigned = true
extractSignal-reduces-signed :
  ∀ {m} (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (signalValue z sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (signed : SignalDef.isSigned sig ≡ true)
  → (bl>0 : SignalDef.bitLength sig > 0)
  → (sf : SignedFits z (SignalDef.bitLength sig))
  → (fits-in-frame : SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8)
  → let n = fromSigned z (SignalDef.bitLength sig)
        n<2^bl = SignedFits-implies-fromSigned-bounded z (SignalDef.bitLength sig) bl>0 sf
    in extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just (signalValue z sig)

-- LittleEndian case: no byte swapping
extractSignal-reduces-signed z sig LittleEndian frame bounds-ok signed bl>0 sf fits-in-frame =
  helper core-eq bounds-ok
  where
    open SignalDef sig
    open CANFrame frame
    value : ℚ
    value = signalValue z sig

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
    open CANFrame frame
    value : ℚ
    value = signalValue z sig

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

-- Main theorem (Signed): inject then extract returns original value
extractSignal-injectSignal-roundtrip-signed :
  ∀ {m} (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame m)
  → (bounds-ok : inBounds (signalValue z sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (signed : SignalDef.isSigned sig ≡ true)
  → (bl>0 : SignalDef.bitLength sig > 0)
  → (sf : SignedFits z (SignalDef.bitLength sig))
  → (fits-in-frame : SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8)
  → (injectSignal (signalValue z sig) sig byteOrder frame >>= λ frame' →
       extractSignal frame' sig byteOrder) ≡ just (signalValue z sig)
extractSignal-injectSignal-roundtrip-signed z sig byteOrder frame bounds-ok factor≢0 signed bl>0 sf fits-in-frame =
  proof
  where
    open SignalDef sig
    value : ℚ
    value = signalValue z sig

    n : ℕ
    n = fromSigned z (bitLength)

    n<2^bl : n < 2 ^ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (bitLength) bl>0 sf

    -- Reduction lemma: injectSignal computes to just (injectedFrame ...)
    inject-reduces : injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    inject-reduces = injectSignal-reduces-signed z sig byteOrder frame bounds-ok factor≢0 bl>0 sf

    -- Reduction lemma: extractSignal on injectedFrame returns just value
    extract-reduces : extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just value
    extract-reduces = extractSignal-reduces-signed z sig byteOrder frame bounds-ok signed bl>0 sf fits-in-frame

    -- Compose by rewriting
    proof : (injectSignal value sig byteOrder frame >>= λ f → extractSignal f sig byteOrder) ≡ just value
    proof rewrite inject-reduces = extract-reduces
