-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- An encodable value's raw value fits its signal's bits.
--
-- The proofs use `rawFits` relevantly (they match on how the raw value fits);
-- the runtime's `Aletheia.CAN.Encoding.Value.fitBound` uses it only in an
-- erased position, so the compiled runtime neither calls nor imports this
-- module.
module Aletheia.CAN.Encoding.Properties.Fits where

open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding.Arithmetic using (applyScaling)
open import Aletheia.CAN.Encoding.Arithmetic.Range using (RawFits; scaledRawFits)
open import Aletheia.CAN.Encoding.Value.Facts using (SignalFacts)
open import Aletheia.DBC.DecRat using (toℚ)
open import Data.Integer using (ℤ)
open import Data.Rational using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

-- A raw value that scales exactly to a value within the declared range, which
-- lies within the values the bits carry, fits the bits.
rawFits : ∀ {sd : SignalDef} {v : ℚ} (raw : ℤ)
  → toℚ (SignalDef.minimum sd) ≤ v → v ≤ toℚ (SignalDef.maximum sd)
  → applyScaling raw (toℚ (SignalDef.factor sd)) (toℚ (SignalDef.offset sd)) ≡ v
  → SignalFacts sd
  → RawFits raw (SignalDef.bitLength sd) (SignalDef.isSigned sd)
rawFits {sd} raw lowOk highOk exact facts =
  scaledRawFits (SignalDef.isSigned sd) (SignalDef.bitLength sd)
    (toℚ (SignalDef.factor sd)) (toℚ (SignalDef.offset sd)) raw (SignalFacts.factor≢0 facts)
    (subst (_ ≤_) (sym exact) (ℚP.≤-trans (SignalFacts.lowWithin facts) lowOk))
    (subst (_≤ _) (sym exact) (ℚP.≤-trans highOk (SignalFacts.highWithin facts)))
