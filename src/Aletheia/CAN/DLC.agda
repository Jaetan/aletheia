{-# OPTIONS --safe --without-K #-}

-- CAN-FD Data Length Code (DLC) to payload byte count mapping.
--
-- Purpose: Convert between DLC field values and actual payload sizes.
-- CAN 2.0B: DLC 0–8 maps directly to 0–8 bytes.
-- CAN-FD:   DLC 9–15 maps to 12, 16, 20, 24, 32, 48, 64 bytes.
-- Role: Used by frame construction, validation, and protocol layers.
-- Properties: See CAN/DLC/Properties.agda for roundtrip, bound, and injectivity proofs.
module Aletheia.CAN.DLC where

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

-- CAN-FD DLC to payload byte count.
-- DLC 0–8: identity mapping (CAN 2.0B compatible).
-- DLC 9–15: non-linear mapping per ISO 11898-1:2015.
-- DLC > 15: returns the value unchanged (invalid, caught by validation).
dlcToBytes : ℕ → ℕ
dlcToBytes 9  = 12
dlcToBytes 10 = 16
dlcToBytes 11 = 20
dlcToBytes 12 = 24
dlcToBytes 13 = 32
dlcToBytes 14 = 48
dlcToBytes 15 = 64
dlcToBytes n  = n

-- Inverse: payload byte count to DLC.
-- Returns nothing for byte counts that don't correspond to valid DLC values.
-- Uses ≡ᵇ for large literals (≥20) to avoid LiteralTooBig / suc pile-ups.
bytesToDlc : ℕ → Maybe ℕ
bytesToDlc 0  = just 0
bytesToDlc 1  = just 1
bytesToDlc 2  = just 2
bytesToDlc 3  = just 3
bytesToDlc 4  = just 4
bytesToDlc 5  = just 5
bytesToDlc 6  = just 6
bytesToDlc 7  = just 7
bytesToDlc 8  = just 8
bytesToDlc 12 = just 9
bytesToDlc 16 = just 10
bytesToDlc n  =
  if n ≡ᵇ 20 then just 11
  else if n ≡ᵇ 24 then just 12
  else if n ≡ᵇ 32 then just 13
  else if n ≡ᵇ 48 then just 14
  else if n ≡ᵇ 64 then just 15
  else nothing

-- Maximum DLC value for CAN 2.0B
maxDLC-2B : ℕ
maxDLC-2B = 8

-- Maximum DLC value for CAN-FD
maxDLC-FD : ℕ
maxDLC-FD = 15
