{-# OPTIONS --safe --without-K #-}

-- CAN-FD Data Length Code (DLC) to payload byte count mapping.
--
-- Purpose: Convert between DLC field values and actual payload sizes.
-- CAN 2.0B: DLC 0–8 maps directly to 0–8 bytes.
-- CAN-FD:   DLC 9–15 maps to 12, 16, 20, 24, 32, 48, 64 bytes.
-- Role: Used by frame construction, validation, and protocol layers.
-- Properties: See CAN/DLC/Properties.agda for roundtrip, bound, and injectivity proofs.
module Aletheia.CAN.DLC where

open import Data.Nat using (ℕ; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; T; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)

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
-- Catch-all: structurally required by Agda's totality checker because ℕ is
-- open (0–8 also land here as identity). Unreachable from validated code paths:
-- DLC.bounded ensures code < 16, so only 0–15 are constructed.
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
  -- Reached for byte counts not in the CAN-FD mapping table (e.g., 3, 9–11,
  -- 13–15, 17–19, 21–23, 25–31, 33–47, 49–63, ≥65). Callers: Routing.agda
  -- parses user-supplied byte arrays, so invalid counts are possible.
  else nothing

-- Maximum DLC value for CAN 2.0B
maxDLC-2B : ℕ
maxDLC-2B = 8

-- Maximum DLC value for CAN-FD
maxDLC-FD : ℕ
maxDLC-FD = 15

-- Validated DLC code: 0–15, with @0 erased bound proof.
-- Follows the CANId pattern (Standard/Extended carry T (n <ᵇ max) proof).
-- MAlonzo erases the @0 field — zero runtime cost.
record DLC : Set where
  constructor mkDLC
  field
    code : ℕ
    @0 bounded : T (code <ᵇ suc maxDLC-FD)

-- Extract byte count from a validated DLC code.
dlcBytes : DLC → ℕ
dlcBytes d = dlcToBytes (DLC.code d)

-- Construct a validated DLC from a byte count.
-- Returns nothing for byte counts that don't correspond to valid DLC values.
-- Parallels bytesToDlc but returns a DLC record with @0 bound proof.
bytesToValidDLC : ℕ → Maybe DLC
bytesToValidDLC 0  = just (mkDLC 0 tt)
bytesToValidDLC 1  = just (mkDLC 1 tt)
bytesToValidDLC 2  = just (mkDLC 2 tt)
bytesToValidDLC 3  = just (mkDLC 3 tt)
bytesToValidDLC 4  = just (mkDLC 4 tt)
bytesToValidDLC 5  = just (mkDLC 5 tt)
bytesToValidDLC 6  = just (mkDLC 6 tt)
bytesToValidDLC 7  = just (mkDLC 7 tt)
bytesToValidDLC 8  = just (mkDLC 8 tt)
bytesToValidDLC 12 = just (mkDLC 9 tt)
bytesToValidDLC 16 = just (mkDLC 10 tt)
bytesToValidDLC n  =
  if n ≡ᵇ 20 then just (mkDLC 11 tt)
  else if n ≡ᵇ 24 then just (mkDLC 12 tt)
  else if n ≡ᵇ 32 then just (mkDLC 13 tt)
  else if n ≡ᵇ 48 then just (mkDLC 14 tt)
  else if n ≡ᵇ 64 then just (mkDLC 15 tt)
  else nothing
