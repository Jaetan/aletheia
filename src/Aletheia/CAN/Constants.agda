{-# OPTIONS --safe --without-K #-}

-- CAN domain constants (ID bounds, physical bit limits).
--
-- Purpose: Single source of truth for CAN numeric limits.
-- Design: Depends only on stdlib (no Prelude), so CAN/Frame.agda
-- can import these without creating a circular dependency.
module Aletheia.CAN.Constants where

open import Data.Nat using (ℕ; _≤_)

-- CAN ID bounds (used for validation and type constraints)
standard-can-id-max : ℕ
standard-can-id-max = 2048  -- 2^11 (11-bit standard CAN IDs: 0x000-0x7FF)

extended-can-id-max : ℕ
extended-can-id-max = 536870912  -- 2^29 (29-bit extended CAN IDs: 0x00000000-0x1FFFFFFF)

-- Maximum physical bits in a CAN-FD frame (64 bytes × 8 bits)
max-physical-bits : ℕ
max-physical-bits = 512

-- 8 ≤ 512 (one byte fits in max-physical-bits)
-- Defined once to avoid duplicating the 8-deep s≤s chain
8≤max-physical-bits : 8 ≤ max-physical-bits
8≤max-physical-bits = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
  where open import Data.Nat using (z≤n; s≤s)
