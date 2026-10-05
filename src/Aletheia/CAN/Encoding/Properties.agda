-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for CAN signal encoding/decoding (curated facade).
--
-- Purpose: Gather the encoding theorems in one place, grouped by layer;
--   `check-properties` type-checks this module as the root of the encoding
--   proofs.
--
-- The proofs live in sibling submodules, one per layer, so each can be
-- re-checked on its own:
--
--   Properties.Arithmetic — ℕ ↔ ℤ two's complement and the floor of an integer.
--   Properties.Roundtrip  — a raw value's bits written into a frame extract
--                            back to the value it scales to (frame + decoding).
--   Properties.Value      — what checking and encoding a value guarantee: each
--                            refusal's condition, and an accepted value's frame
--                            extracting back to exactly that value.
--   Properties.Disjoint   — the frame writer leaves disjoint bits as they
--                            were, including across byte orders.
--
-- Philosophy: Bit independence is structural, not arithmetic.
module Aletheia.CAN.Encoding.Properties where

-- ============================================================================
-- ARITHMETIC
-- ============================================================================

open import Aletheia.CAN.Encoding.Properties.Arithmetic public
  using ( SignedFits )

-- ============================================================================
-- A WRITTEN RAW VALUE READS BACK
-- ============================================================================

open import Aletheia.CAN.Encoding.Properties.Roundtrip public
  using ( extractSignal-reduces-unsigned
        ; extractSignal-reduces-signed
        )

-- ============================================================================
-- CHECKING AND ENCODING A VALUE
-- ============================================================================

open import Aletheia.CAN.Encoding.Properties.Value public
  using ( checkValue-accepted
        ; checkValue-out-of-range
        ; checkValue-not-representable
        ; extractSignal-encodedBits
        ; encodedBits-irrelevant
        )

-- ============================================================================
-- DISJOINT BIT PRESERVATION
-- ============================================================================

open import Aletheia.CAN.Encoding.Properties.Disjoint public
  using ( withInjected-preserves-disjoint-bits
        ; withInjected-preserves-disjoint-bits-physical
        )
