-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Disjoint bit preservation for the frame writer.
--
-- Purpose: writing bits at one position of a frame (`withInjected`) leaves
--   every disjoint position's bits as they were: logically disjoint
--   positions under one byte order, physically disjoint ones under any two.
--   Frame layer only: no value and no signal definition.
--
-- Structure:
--   1. extractionBytes≡payloadIso                       — structural equality
--   2. withInjected-preserves-disjoint-bits            — one byte order
--   3. withInjected-preserves-disjoint-bits-physical   — any two byte orders
--
-- These are the structural core of the batch frame-building correctness
-- story (Aletheia.CAN.BatchFrameBuilding, whose overlap check decides the
-- disjointness): writing signal A then signal B leaves A's bits intact.
module Aletheia.CAN.Encoding.Properties.Disjoint where

open import Aletheia.CAN.Encoding using (extractionBytes; withInjected)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; extractBits; injectBits; swapBytes; payloadIso; physicalBitPos; not-in-interval)
open import Aletheia.CAN.Endianness.Properties using (payloadIso-involutive; injectBits-preserves-disjoint; injectBits-preserves-outside; physicalBitPos-BE-involutive; extractBits-swap-inject-preserves)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.Data.BitVec using (BitVec)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_)
open import Data.Nat.Properties using (<-≤-trans; +-monoʳ-<)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

-- ============================================================================
-- DISJOINT BIT PRESERVATION
-- ============================================================================

-- Helper: extractionBytes equals payloadIso (definitional by cases)
extractionBytes≡payloadIso : ∀ {m} (frame : CANFrame m) (bo : ByteOrder) → extractionBytes frame bo ≡ payloadIso bo (CANFrame.payload frame)
extractionBytes≡payloadIso frame LittleEndian = refl
extractionBytes≡payloadIso frame BigEndian = refl

-- Writing bits at s₁ under one byte order leaves the bits of a disjoint
-- range, read under the same byte order, as they were.
withInjected-preserves-disjoint-bits :
  ∀ {m len₁ len₂} (s₁ : ℕ) (bits : BitVec len₁) (bo : ByteOrder) (frame : CANFrame m) (start₂ : ℕ)
  → s₁ + len₁ ≤ start₂ ⊎ start₂ + len₂ ≤ s₁
  → s₁ + len₁ ≤ m * 8
  → start₂ + len₂ ≤ m * 8
  → extractBits {len₂} (extractionBytes (withInjected s₁ bits bo frame) bo) start₂
    ≡ extractBits {len₂} (extractionBytes frame bo) start₂
withInjected-preserves-disjoint-bits {len₂ = len₂} s₁ bits bo frame start₂ disj fits₁ fits₂ =
  begin
    extractBits (extractionBytes (withInjected s₁ bits bo frame) bo) start₂
  ≡⟨ cong (λ x → extractBits x start₂) (extractionBytes≡payloadIso (withInjected s₁ bits bo frame) bo) ⟩
    extractBits (payloadIso bo (payloadIso bo updatedBytes)) start₂
  ≡⟨ cong (λ x → extractBits x start₂) (payloadIso-involutive bo updatedBytes) ⟩
    extractBits (injectBits bytes s₁ bits) start₂
  ≡⟨ injectBits-preserves-disjoint bytes s₁ start₂ bits disj fits₁ fits₂ ⟩
    extractBits (payloadIso bo (CANFrame.payload frame)) start₂
  ≡⟨ cong (λ x → extractBits x start₂) (sym (extractionBytes≡payloadIso frame bo)) ⟩
    extractBits (extractionBytes frame bo) start₂
  ∎
  where
    bytes = payloadIso bo (CANFrame.payload frame)
    updatedBytes = injectBits bytes s₁ bits

-- ============================================================================
-- MIXED BYTE ORDER: Physical disjointness preservation
-- ============================================================================

-- Writing bits at s₁ under one byte order leaves the bits of a range read
-- under any byte order as they were, when no physical bit of the one is a
-- physical bit of the other.
withInjected-preserves-disjoint-bits-physical :
  ∀ {n len₁ len₂} (s₁ : ℕ) (bits : BitVec len₁) (bo₁ bo₂ : ByteOrder) (frame : CANFrame n) (start₂ : ℕ)
  → (∀ k₁ → k₁ < len₁
     → ∀ k₂ → k₂ < len₂
     → physicalBitPos n bo₁ (s₁ + k₁) ≢ physicalBitPos n bo₂ (start₂ + k₂))
  → s₁ + len₁ ≤ n * 8
  → start₂ + len₂ ≤ n * 8
  → extractBits {len₂} (extractionBytes (withInjected s₁ bits bo₁ frame) bo₂) start₂
    ≡ extractBits {len₂} (extractionBytes frame bo₂) start₂
withInjected-preserves-disjoint-bits-physical {n} {len₁} {len₂} s₁ rawBitVec bo₁ bo₂ frame start₂ physDisj fits₁ fits₂ =
  begin
    extractBits (extractionBytes (withInjected s₁ rawBitVec bo₁ frame) bo₂) start₂
  ≡⟨ cong (λ x → extractBits x start₂) (extractionBytes≡payloadIso (withInjected s₁ rawBitVec bo₁ frame) bo₂) ⟩
    extractBits (payloadIso bo₂ finalBytes) start₂
  ≡⟨ go bo₁ bo₂ refl refl ⟩
    extractBits (payloadIso bo₂ origPayload) start₂
  ≡⟨ cong (λ x → extractBits x start₂) (sym (extractionBytes≡payloadIso frame bo₂)) ⟩
    extractBits (extractionBytes frame bo₂) start₂
  ∎
  where
    origPayload = CANFrame.payload frame
    l₁ = len₁
    bytes = payloadIso bo₁ origPayload
    updatedBytes = injectBits bytes s₁ rawBitVec
    finalBytes = payloadIso bo₁ updatedBytes

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
