{-# OPTIONS --safe --without-K #-}

-- Arithmetic bridge lemmas for CAN signal encoding (curated facade).
--
-- Purpose: Re-export Layer 2 (integer two's-complement) and Layer 3+
--   (rational scaling, floor bounds, algebraic chain, structural bridge)
--   lemmas grouped by topic. The actual proofs live in two sibling
--   submodules so that IDE jump-to-definition stays fast and each layer
--   can be re-checked independently:
--
--   Properties.Arithmetic.Integer  — Layer 2: ℕ ↔ ℤ two's-complement
--                                    roundtrips. NO rationals.
--   Properties.Arithmetic.Rational — Layers 3, A, A', C, D: ℚ scaling,
--                                    floor bounds, algebraic normalization,
--                                    semantic chain, structural bridge.
--
-- Layering (arithmetic firewall — each lower layer is quarantined):
--   * Layer 2: Integer conversion (ℕ ↔ ℤ). Signed/unsigned roundtrip via
--     `fromSigned`/`toSigned`. No rationals.
--   * Layer 3: ℚ scaling. The ONLY place rational field laws are used. The
--     `ℚ-cancel` lemma and `÷-via-ℚᵘ` bridge localize representation details
--     so Layers 4+ never see `mkℚᵘ` / `toℚᵘ`.
--   * Layer A (floor bounds): `floor-lower`/`floor-upper` quarantine division.
--   * Layer A' (algebraic normalization): coercions, field identities,
--     distributivity — shifts/unshifts offsets, cancels subtractions.
--   * Layer C (algebraic chain): semantic core of the reverse direction.
--     Uses ONLY floor bounds, stdlib monotonicity, and Layer A' helpers.
--     NO begin…∎ chains, NO cong at this layer.
--   * Layer D (structural bridge): pattern-matches on factor's sign to
--     select positive/negative scaling bounds.
--
-- Public API:
--   Layer 2: fromSigned-toSigned-roundtrip; SignedFits;
--            toSigned-fromSigned-roundtrip; fromSigned-bounded-neg
--   Layer 3: removeScaling-zero⇒nothing; removeScaling-nothing⇒zero;
--            removeScaling-factor-zero-iff-nothing;
--            removeScaling-applyScaling-exact; applyScaling-injective
--   Layer D: applyScaling-removeScaling-bounded
module Aletheia.CAN.Encoding.Properties.Arithmetic where

-- ============================================================================
-- LAYER 2: INTEGER CONVERSION (no ℚ)
-- ============================================================================
open import Aletheia.CAN.Encoding.Properties.Arithmetic.Integer public
  using ( fromSigned-toSigned-roundtrip
        ; SignedFits
        ; toSigned-fromSigned-roundtrip
        ; fromSigned-bounded-neg
        )

-- ============================================================================
-- LAYER 3 + LAYERS A/A'/C/D: RATIONAL SCALING + BOUNDS
-- ============================================================================
open import Aletheia.CAN.Encoding.Properties.Arithmetic.Rational public
  using ( removeScaling-zero⇒nothing
        ; removeScaling-nothing⇒zero
        ; removeScaling-factor-zero-iff-nothing
        ; removeScaling-applyScaling-exact
        ; applyScaling-injective
        ; applyScaling-removeScaling-bounded
        )
