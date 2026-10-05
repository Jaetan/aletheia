-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The values a signal's bits carry, and the facts a valid DBC states of a
-- signal that encoding its value needs.  Both encoding a value
-- (`Aletheia.CAN.Encoding.Value`) and the proof that an encodable raw value
-- fits its bits (`Aletheia.CAN.Encoding.Properties.Fits`) build on these; the
-- validator reads `bitsRange` for its range checks.
module Aletheia.CAN.Encoding.Value.Facts where

open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding.Arithmetic using (rawRange; orderBySign)
open import Aletheia.DBC.DecRat using (toℚ)
open import Data.Nat using (_>_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _≤_) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- The least and the greatest physical value a signal's bits carry: the raw
-- range scaled by the factor and shifted by the offset.
bitsRange : SignalDef → ℚ × ℚ
bitsRange sd =
  let factor = toℚ (SignalDef.factor sd)
      offset = toℚ (SignalDef.offset sd)
      raw    = rawRange (SignalDef.isSigned sd) (SignalDef.bitLength sd)
  in orderBySign factor (proj₁ raw *ᵣ factor +ᵣ offset) (proj₂ raw *ᵣ factor +ᵣ offset)

-- What a valid DBC states of a signal, and what encoding it needs.
record SignalFacts (sd : SignalDef) : Set where
  field
    factor≢0    : toℚ (SignalDef.factor sd) ≢ 0ℚ
    bitLength>0 : SignalDef.bitLength sd > 0
    lowWithin   : proj₁ (bitsRange sd) ≤ toℚ (SignalDef.minimum sd)
    highWithin  : toℚ (SignalDef.maximum sd) ≤ proj₂ (bitsRange sd)
