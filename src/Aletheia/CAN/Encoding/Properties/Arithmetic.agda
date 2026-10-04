-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Arithmetic bridge lemmas for CAN signal encoding (curated facade).
--
-- Purpose: Re-export the integer two's-complement lemmas and the rounding
--   fact the encoding proofs use, from two sibling submodules:
--
--   Properties.Arithmetic.Integer  — ℕ ↔ ℤ two's-complement roundtrips.
--                                    NO rationals.
--   Properties.Arithmetic.Rational — the floor of an integer as a rational.
--
-- Public API:
--   fromSigned-toSigned-roundtrip; SignedFits; toSigned-fromSigned-roundtrip;
--   floor-int
module Aletheia.CAN.Encoding.Properties.Arithmetic where

-- ============================================================================
-- LAYER 2: INTEGER CONVERSION (no ℚ)
-- ============================================================================
open import Aletheia.CAN.Encoding.Properties.Arithmetic.Integer public
  using ( fromSigned-toSigned-roundtrip
        ; SignedFits
        ; toSigned-fromSigned-roundtrip
        )

-- ============================================================================
-- ROUNDING
-- ============================================================================
open import Aletheia.CAN.Encoding.Properties.Arithmetic.Rational public
  using ( floor-int )
