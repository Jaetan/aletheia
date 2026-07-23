-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Reason parity between the two extraction categorizers, and wire-code
-- distinctness.
--
-- Purpose: Prove (1) the indexed (binary-wire) categorizer carries exactly
--   the reason strings the string-keyed (JSON) categorizer produces — the
--   binary path can never be less informative than, or drift from, the JSON
--   path; (2) the u8 wire encoding of ExtractionErrorCode is injective — no
--   two distinguishable error conditions share a wire code.
-- Key results: reason-parity, fromℕ∘toℕ, extractionErrorCodeToℕ-injective.
module Aletheia.CAN.Batch.Properties.ReasonParity where

open import Aletheia.CAN.ExtractionResult using
  (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.Error using
  (MuxValueMismatch; MuxSignalNotFound; MuxChainCycle; MuxExtractionFailed;
   BitExtractionFailed; ValueExceedsWireRange; InContext)
open import Aletheia.CAN.BatchExtraction using
  ( PartitionedResults; categorizeResult; categorizeIndexed
  ; ExtractionErrorCode; extractionErrorCodeToℕ
  ; NotInDBC; OutOfBounds; BitExtractionFailed; ValueExceedsWireRange
  ; MuxSignalNotFound; MuxChainCycle; MuxExtractionFailed; MuxValueMismatch
  )

open import Data.List using (map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- ============================================================================
-- REASON PARITY (binary wire ≡ JSON wire, per result)
-- ============================================================================

-- THEOREM: for every extraction result, the reason strings in the indexed
-- categorizer's error partition are exactly those of the string-keyed
-- categorizer.  Both derive from the shared resultToString, so every arm is
-- definitional — this pin makes the sharing a checked invariant rather than
-- a code-review convention.
reason-parity : ∀ (name : String) (idx : ℕ) (r : ExtractionResult) →
  map proj₂ (PartitionedResults.errors (categorizeResult name r))
  ≡ map (λ e → proj₂ (proj₂ e)) (PartitionedResults.errors (categorizeIndexed name idx r))
reason-parity _ _ (Success _)                            = refl
reason-parity _ _ SignalNotInDBC                         = refl
reason-parity _ _ (SignalNotPresent MuxValueMismatch)    = refl
reason-parity _ _ (SignalNotPresent (MuxSignalNotFound _))   = refl
reason-parity _ _ (SignalNotPresent MuxChainCycle)       = refl
reason-parity _ _ (SignalNotPresent (MuxExtractionFailed _)) = refl
reason-parity _ _ (SignalNotPresent (BitExtractionFailed _)) = refl
reason-parity _ _ (SignalNotPresent ValueExceedsWireRange)   = refl
reason-parity _ _ (SignalNotPresent (InContext _ _))     = refl
reason-parity _ _ (ValueOutOfBounds _ _ _)               = refl
reason-parity _ _ (ExtractionFailed _)                   = refl

-- ============================================================================
-- WIRE-CODE DISTINCTNESS (u8 encoding is injective)
-- ============================================================================

-- Partial inverse of the u8 wire encoding.  Proof-only — the runtime wire
-- decoder lives in each language binding; this function exists to state the
-- round-trip below.
extractionErrorCodeFromℕ : ℕ → Maybe ExtractionErrorCode
extractionErrorCodeFromℕ 0 = just NotInDBC
extractionErrorCodeFromℕ 1 = just OutOfBounds
extractionErrorCodeFromℕ 2 = just BitExtractionFailed
extractionErrorCodeFromℕ 3 = just ValueExceedsWireRange
extractionErrorCodeFromℕ 4 = just MuxSignalNotFound
extractionErrorCodeFromℕ 5 = just MuxChainCycle
extractionErrorCodeFromℕ 6 = just MuxExtractionFailed
extractionErrorCodeFromℕ 7 = just MuxValueMismatch
extractionErrorCodeFromℕ _ = nothing

-- Round-trip: every code decodes back to itself — the wire assignment is
-- collision-free by construction.
fromℕ∘toℕ : ∀ c → extractionErrorCodeFromℕ (extractionErrorCodeToℕ c) ≡ just c
fromℕ∘toℕ NotInDBC              = refl
fromℕ∘toℕ OutOfBounds           = refl
fromℕ∘toℕ BitExtractionFailed   = refl
fromℕ∘toℕ ValueExceedsWireRange = refl
fromℕ∘toℕ MuxSignalNotFound     = refl
fromℕ∘toℕ MuxChainCycle         = refl
fromℕ∘toℕ MuxExtractionFailed   = refl
fromℕ∘toℕ MuxValueMismatch      = refl

-- COROLLARY: no two error codes share a u8 wire value.
extractionErrorCodeToℕ-injective : ∀ a b
  → extractionErrorCodeToℕ a ≡ extractionErrorCodeToℕ b → a ≡ b
extractionErrorCodeToℕ-injective a b eq =
  just-injective
    (trans (sym (fromℕ∘toℕ a)) (trans (cong extractionErrorCodeFromℕ eq) (fromℕ∘toℕ b)))
