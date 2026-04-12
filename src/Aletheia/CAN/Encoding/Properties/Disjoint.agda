{-# OPTIONS --safe --without-K #-}

-- Disjoint bit preservation properties for CAN signal encoding.
--
-- Purpose: Prove that successful injectSignal calls preserve bits at
--   disjoint positions, both logically (same byte order) and physically
--   (mixed byte orders).
--
-- Structure:
--   1. extractionBytes≡payloadIso                  — structural equality
--   2. injectSignal-preserves-disjoint-bits        — same byte order
--   3. injectSignal-preserves-disjoint-bits-physical — mixed byte orders
--
-- These theorems are the structural core of the Batch frame-building
-- correctness proofs in Aletheia.Protocol.BatchFrameBuilding.Properties:
-- they justify that writing signal A then signal B to a frame leaves
-- signal A's bits intact, provided the two signals' bit ranges are
-- disjoint (logically when byte orders match, physically when they
-- differ).
module Aletheia.CAN.Encoding.Properties.Disjoint where

open import Aletheia.CAN.Encoding using (extractionBytes; injectSignal)
open import Aletheia.CAN.Encoding.Arithmetic using (fromSigned; removeScaling; inBounds)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; extractBits; injectBits; swapBytes; payloadIso; physicalBitPos; not-in-interval)
open import Aletheia.CAN.Endianness.Properties using (payloadIso-involutive; injectBits-preserves-disjoint; injectBits-preserves-outside; physicalBitPos-BE-involutive; extractBits-swap-inject-preserves)
open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _<?_; _≤_; _^_)
open import Data.Nat.Properties using (<-≤-trans; +-monoʳ-<)
open import Data.Rational using (ℚ)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (yes; no)
open import Function using (case_of_)

-- ============================================================================
-- DISJOINT BIT PRESERVATION
-- ============================================================================

-- Helper: extractionBytes equals payloadIso (definitional by cases)
extractionBytes≡payloadIso : ∀ {m} (frame : CANFrame m) (bo : ByteOrder) → extractionBytes frame bo ≡ payloadIso bo (CANFrame.payload frame)
extractionBytes≡payloadIso frame LittleEndian = refl
extractionBytes≡payloadIso frame BigEndian = refl

-- Key structural lemma: when injectSignal succeeds, bits at disjoint positions are preserved
-- The proof mirrors injectSignal's structure using plain with-patterns (no rewrite, no in)
injectSignal-preserves-disjoint-bits :
  ∀ {m} {len₂} (v : ℚ) (sig : SignalDef) (bo : ByteOrder) (frame frame' : CANFrame m)
    (start₂ : ℕ)
  → injectSignal v sig bo frame ≡ just frame'
  → SignalDef.startBit sig + SignalDef.bitLength sig ≤ start₂
    ⊎ start₂ + len₂ ≤ SignalDef.startBit sig  -- disjoint ranges
  → SignalDef.startBit sig + SignalDef.bitLength sig ≤ m * 8
  → start₂ + len₂ ≤ m * 8
  → extractBits {len₂} (extractionBytes frame' bo) start₂
    ≡ extractBits {len₂} (extractionBytes frame bo) start₂
injectSignal-preserves-disjoint-bits {m} {len₂} v sig bo frame frame' start₂ eq disj fits₁ fits₂
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
  ∀ {n} {len₂} (v : ℚ) (sig : SignalDef) (bo₁ bo₂ : ByteOrder) (frame frame' : CANFrame n)
    (start₂ : ℕ)
  → injectSignal v sig bo₁ frame ≡ just frame'
  → (∀ k₁ → k₁ < SignalDef.bitLength sig
     → ∀ k₂ → k₂ < len₂
     → physicalBitPos n bo₁ (SignalDef.startBit sig + k₁)
       ≢ physicalBitPos n bo₂ (start₂ + k₂))
  → SignalDef.startBit sig + SignalDef.bitLength sig ≤ n * 8
  → start₂ + len₂ ≤ n * 8
  → extractBits {len₂} (extractionBytes frame' bo₂) start₂
    ≡ extractBits {len₂} (extractionBytes frame bo₂) start₂
injectSignal-preserves-disjoint-bits-physical {n} {len₂} v sig bo₁ bo₂ frame frame' start₂ eq physDisj fits₁ fits₂
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
                pw : ∀ k₁ → k₁ < l₁ → start₂ + k₂' ≢ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂' k₂'<len₂
                  (cong (physicalBitPos n LittleEndian) (sym eq₀))
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
                pw : ∀ k₁ → k₁ < l₁ → start₂ + k₂' ≢ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂' k₂'<len₂
                  (cong (physicalBitPos n BigEndian) (sym eq₀))
        -- LE inject, BE extract: payloadIso BE (payloadIso LE x) ≡ swapBytes x
        go LittleEndian BigEndian refl refl =
          extractBits-swap-inject-preserves origPayload s₁ start₂ rawBitVec
            outside-LE-BE fits₁ fits₂
          where
            outside-LE-BE : ∀ k → k < len₂ → physicalBitPos n BigEndian (start₂ + k) < s₁
                          ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian (start₂ + k)
            outside-LE-BE k₂ k₂<len₂ =
              not-in-interval s₁ l₁ (physicalBitPos n BigEndian (start₂ + k₂)) pw
              where
                pw : ∀ k₁ → k₁ < l₁ → physicalBitPos n BigEndian (start₂ + k₂) ≢ s₁ + k₁
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
            outside-BE : ∀ k → k < len₂ → physicalBitPos n BigEndian (start₂ + k) < s₁
                       ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian (start₂ + k)
            outside-BE k₂ k₂<len₂ = not-in-interval s₁ l₁ (physicalBitPos n BigEndian (start₂ + k₂)) pw
              where
                start₂k₂<n*8 : start₂ + k₂ < n * 8
                start₂k₂<n*8 = <-≤-trans (+-monoʳ-< start₂ k₂<len₂) fits₂
                pw : ∀ k₁ → k₁ < l₁ → physicalBitPos n BigEndian (start₂ + k₂) ≢ s₁ + k₁
                pw k₁ k₁<l₁ eq₀ = physDisj k₁ k₁<l₁ k₂ k₂<len₂ inner
                  where
                    inner : physicalBitPos n BigEndian (s₁ + k₁) ≡ start₂ + k₂
                    inner = trans (sym (cong (physicalBitPos n BigEndian) eq₀))
                                  (physicalBitPos-BE-involutive n (start₂ + k₂) start₂k₂<n*8)
