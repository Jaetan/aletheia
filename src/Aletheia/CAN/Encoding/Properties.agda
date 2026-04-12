{-# OPTIONS --safe --without-K #-}

-- Correctness properties for CAN signal encoding/decoding (curated facade).
--
-- Purpose: Re-export the round-trip and disjoint-bit theorems used by
--   downstream proofs (Aletheia.CAN.Batch.Properties), grouped by topic.
--
-- The actual proofs live in three sibling submodules so that IDE
-- jump-to-definition stays fast and each layer can be re-checked
-- independently:
--
--   Properties.Arithmetic — Layer 2 (ℕ ↔ ℤ two's complement) and
--                            Layer 3 (ℤ ↔ ℚ scaling) algebraic lemmas.
--   Properties.Roundtrip  — Layer 4 composition: signal-level
--                            extract ∘ inject ≡ id, both unsigned and
--                            signed, plus the WellFormedSignal record.
--   Properties.Disjoint   — Bit preservation under disjoint injection,
--                            including mixed-byte-order physical disjointness.
--
-- Strategy: BitVec-based architecture - structural proofs, not arithmetic:
--   Layer 0: BitVec operations (structural) - PROVEN in BitVec module
--   Layer 1: BitVec ↔ ℕ conversion - proven ONCE in Conversion module
--   Layer 2: Integer conversion (ℕ ↔ ℤ) - no ℚ
--   Layer 3: Scaling (ℤ ↔ ℚ) - isolated ℚ lemmas
--   Layer 4: Composition - combine all layers
--
-- Philosophy: Bit independence is structural, not arithmetic.
-- The hard proofs (testBit-setBit) are now trivial because we use the right representation.
module Aletheia.CAN.Encoding.Properties where

-- ============================================================================
-- LAYER 2 + LAYER 3: ARITHMETIC LEMMAS
-- ============================================================================
-- Two's-complement (ℕ ↔ ℤ) and scaling (ℤ ↔ ℚ) bridge lemmas. These are
-- the algebraic primitives consumed by Layer 4 composition proofs.
open import Aletheia.CAN.Encoding.Properties.Arithmetic public
  using ( fromSigned-toSigned-roundtrip
        ; SignedFits
        ; toSigned-fromSigned-roundtrip
        ; fromSigned-bounded-neg
        ; removeScaling-zero⇒nothing
        ; removeScaling-nothing⇒zero
        ; removeScaling-factor-zero-iff-nothing
        ; removeScaling-applyScaling-exact
        ; applyScaling-injective
        ; applyScaling-removeScaling-bounded
        )

-- ============================================================================
-- LAYER 4: SIGNAL-LEVEL ROUND-TRIP THEOREMS
-- ============================================================================
-- Composition of all lower layers: extract ∘ inject ≡ id at the signal
-- level, for both unsigned and signed signals. Includes the
-- WellFormedSignal record that captures the precondition.
open import Aletheia.CAN.Encoding.Properties.Roundtrip public
  using ( WellFormedSignal
        ; signalValue
        ; injectedFrame
        ; injectSignal-reduces-unsigned
        ; extractSignal-reduces-unsigned
        ; extractSignal-injectSignal-roundtrip-unsigned
        ; injectSignal-reduces-signed
        ; extractSignal-reduces-signed
        ; extractSignal-injectSignal-roundtrip-signed
        )

-- ============================================================================
-- DISJOINT BIT PRESERVATION
-- ============================================================================
-- Bit-level theorems used by BatchFrameBuilding to prove that writing
-- one signal does not corrupt the bits of disjoint signals — even when
-- injection and extraction use different byte orders.
open import Aletheia.CAN.Encoding.Properties.Disjoint public
  using ( extractionBytes≡payloadIso
        ; injectSignal-preserves-disjoint-bits
        ; injectSignal-preserves-disjoint-bits-physical
        )
