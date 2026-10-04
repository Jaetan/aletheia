-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The kernel's parser for what the binary entries receive: frame fields and
-- signal values as a C caller hands them in, to kernel values whose
-- invariants are decided here.
--
-- A data frame's fields are checked in a fixed order, identifier, DLC, then
-- the payload walked byte by byte, and the first that fails is the refusal: a
-- typed `ParseError` carrying the offending value.  The records built here
-- hold their invariants as irrelevant or erased fields (`CANId`'s range,
-- `DLC`'s bound, `CANFrame`'s byte range, `TimedFrame.dlcValid`), so every
-- frame past this module satisfies them by construction.  Signal values
-- arrive as three parallel arrays and leave as `(index , ℚ)` pairs, each ℚ
-- normalised by the standard library's `_/_`.
module Aletheia.CAN.Frame.Parse where

open import Data.Bool using (Bool; true; false; T)
open import Data.Integer using (ℤ; +_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational using (ℚ; _/_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)
open import Aletheia.CAN.DLC using (DLC; mkDLC; dlcBytes; maxDLC-FD)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended; CANFrame; Byte; IsByte; AllBytes; []; _∷_)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.Trace.Time using (mkTs)
open import Aletheia.Error using
  ( ParseError; StdCANIdOutOfRange; ExtCANIdOutOfRange; DLCCodeOutOfRange
  ; PayloadLengthMismatch; PayloadByteOutOfRange; NonPositiveDenominator
  ; SignalArrayLengthMismatch )

-- The refusal when the test fails, the continuation given its evidence
-- (`tt`, the one inhabitant of `T true`) when it holds.
check : ∀ {A B : Set} (b : Bool) → A → (T b → A ⊎ B) → A ⊎ B
check true  _ k = k tt
check false e _ = inj₁ e

parseCANId : (raw : ℕ) → (extended : Bool) → ParseError ⊎ CANId
parseCANId raw false =
  check (raw <ᵇ standard-can-id-max) (StdCANIdOutOfRange raw) λ p → inj₂ (Standard raw p)
parseCANId raw true  =
  check (raw <ᵇ extended-can-id-max) (ExtCANIdOutOfRange raw) λ p → inj₂ (Extended raw p)

parseDLC : (code : ℕ) → ParseError ⊎ DLC
parseDLC code = check (code <ᵇ suc maxDLC-FD) (DLCCodeOutOfRange code) λ p → inj₂ (mkDLC code p)

-- Exactly `n` bytes, each below 256.
record Payload (n : ℕ) : Set where
  constructor payload
  field
    bytes     : Vec Byte n
    .below256 : AllBytes bytes

-- One pass over the list: the first byte at or above 256 is refused at its
-- position, and a list that ends before position `n` or runs past it is a
-- length mismatch reporting the whole list's length (`observed`, a thunk
-- the success path never forces).
-- The payload with one more byte in front, or the refusal already met.
consByte : ∀ {n} (b : Byte) → IsByte b → ParseError ⊎ Payload n → ParseError ⊎ Payload (suc n)
consByte _ _ (inj₁ e)              = inj₁ e
consByte b p (inj₂ (payload v ok)) = inj₂ (payload (b ∷ v) (p ∷ ok))

walk : (n position : ℕ) → List ℕ → (expected observed : ℕ) → ParseError ⊎ Payload n
walk zero    _ []       _   _   = inj₂ (payload [] [])
walk zero    _ (_ ∷ _)  exp obs = inj₁ (PayloadLengthMismatch exp obs)
walk (suc n) _ []       exp obs = inj₁ (PayloadLengthMismatch exp obs)
walk (suc n) i (b ∷ bs) exp obs =
  check (b <ᵇ 256) (PayloadByteOutOfRange i b) λ p → consByte b p (walk n (suc i) bs exp obs)

parsePayload : (dlc : DLC) → List ℕ → ParseError ⊎ Payload (dlcBytes dlc)
parsePayload dlc bs = walk (dlcBytes dlc) 0 bs (dlcBytes dlc) (List.length bs)

-- The three decided fields of a data frame, its payload sized by its DLC.
record Parts : Set where
  constructor parts
  field
    canId : CANId
    dlc   : DLC
    body  : Payload (dlcBytes dlc)

parseParts : (raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ) → ParseError ⊎ Parts
parseParts raw ext code bs with parseCANId raw ext
... | inj₁ e = inj₁ e
... | inj₂ canId with parseDLC code
...   | inj₁ e = inj₁ e
...   | inj₂ dlc with parsePayload dlc bs
...     | inj₁ e = inj₁ e
...     | inj₂ body = inj₂ (parts canId dlc body)

frameOf : (p : Parts) → CANFrame (dlcBytes (Parts.dlc p))
frameOf (parts canId dlc (payload v ok)) =
  record { id = canId ; dlc = dlc ; payload = v ; below256 = ok }

-- A frame of the size its DLC names, from the raw identifier, DLC code and
-- bytes.
parseCANFrame : (raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ)
              → ParseError ⊎ Σ DLC (λ dlc → CANFrame (dlcBytes dlc))
parseCANFrame raw ext code bs with parseParts raw ext code bs
... | inj₁ e = inj₁ e
... | inj₂ p = inj₂ (Parts.dlc p , frameOf p)

-- A timestamped data frame, its size fixed by its DLC.
parseTimedFrame
  : (timestamp raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ) (brs esi : Maybe Bool)
  → ParseError ⊎ TimedFrame
parseTimedFrame ts raw ext code bs brs esi with parseParts raw ext code bs
... | inj₁ e = inj₁ e
... | inj₂ (parts canId dlc body) = inj₂ record
  { timestamp   = mkTs ts
  ; payloadSize = dlcBytes dlc
  ; frame       = frameOf (parts canId dlc body)
  ; dlcValid    = refl
  ; brs         = brs
  ; esi         = esi
  }

-- An exact rational from a numerator and a positive denominator.
parseRational : ℤ → ℤ → ParseError ⊎ ℚ
parseRational n (+ suc d) = inj₂ (n / suc d)
parseRational _ d         = inj₁ (NonPositiveDenominator d)

-- In step over the three arrays; `mismatch` (the three whole lengths, a
-- thunk the success path never forces) is the refusal when one ends first.
pairs : List ℕ → List ℤ → List ℤ → (mismatch : ParseError) → ParseError ⊎ List (ℕ × ℚ)
pairs [] [] [] _ = inj₂ []
pairs (i ∷ is) (n ∷ ns) (d ∷ ds) mismatch with parseRational n d
... | inj₁ e = inj₁ e
... | inj₂ q with pairs is ns ds mismatch
...   | inj₁ e  = inj₁ e
...   | inj₂ ps = inj₂ ((i , q) ∷ ps)
pairs _ _ _ mismatch = inj₁ mismatch

-- Signal values as three parallel arrays (indices, numerators,
-- denominators), refused when their lengths differ.
parseSignalValues : List ℕ → List ℤ → List ℤ → ParseError ⊎ List (ℕ × ℚ)
parseSignalValues is ns ds =
  pairs is ns ds (SignalArrayLengthMismatch (List.length is) (List.length ns) (List.length ds))
