-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Encoding one signal's value: from a physical value to the signal's bits,
-- with no frame in sight (writing the bits into a frame is the frame layer's,
-- `Aletheia.CAN.Encoding.withInjected`).
--
-- A requested value is checked twice (`checkValue`): it lies in the declared
-- [minimum, maximum], and it scales exactly from an integer raw value; each
-- failure is a typed refusal.  A value that passes is `Encodable`, carrying
-- its raw value and both facts.  The facts a valid DBC states of the signal
-- (`SignalFacts`: a non-zero factor, a non-zero bit length, a declared range
-- within the values its bits carry) then prove the raw value fits the bits
-- (`Aletheia.CAN.Encoding.Properties.Fits.rawFits`, used only erased here),
-- and `encodedBits` builds them from that proof without checking anything.
--
-- DEFER-stdlib-mandate (Cat 29): `candidateRaw` divides by the factor with the
-- stdlib's `_÷_`, which takes a `.{{_ : NonZero q}}` instance argument; the
-- call site supplies it explicitly as `{{nonZeroOf …}}`, so instance
-- resolution is trivial.
module Aletheia.CAN.Encoding.Value where

open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding.Arithmetic using (applyScaling; fromSigned; inBounds₀)
open import Aletheia.CAN.Encoding.Arithmetic.Range using (RawFits-implies-bounded)
open import Aletheia.CAN.Encoding.Value.Facts using (SignalFacts)
open import Aletheia.CAN.Encoding.Properties.Fits using (rawFits)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec)
open import Aletheia.Data.Dec0 using (_because₀_; absurd₀)
open import Aletheia.Data.Dec0.Rational using (_≟ℚ₀_)
open import Aletheia.DBC.DecRat using (toℚ)
open import Data.Bool using (true; false)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Nat using (zero; suc; _<_; _^_)
open import Data.Product using (proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; mkℚ; _≤_; floor)
  renaming (_-_ to _-ᵣ_; _÷_ to _÷ᵣ_)
import Data.Rational.Properties as ℚP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Reflects using (invert)

-- ============================================================================
-- CHECKING A REQUESTED VALUE
-- ============================================================================

data EncodeRefusal : Set where
  OutOfRange       : EncodeRefusal   -- outside [minimum, maximum]
  NotRepresentable : EncodeRefusal   -- scales from no integer raw value

-- A value that passed both checks: its raw value, the value lying in the
-- declared range, and the raw value scaling back to it exactly.
record Encodable (sd : SignalDef) (v : ℚ) : Set where
  constructor encodable
  field
    raw        : ℤ
    @0 lowOk   : toℚ (SignalDef.minimum sd) ≤ v
    @0 highOk  : v ≤ toℚ (SignalDef.maximum sd)
    @0 exact   : applyScaling raw (toℚ (SignalDef.factor sd)) (toℚ (SignalDef.offset sd)) ≡ v

-- The non-zero instance division asks for, read off the numerator; the
-- erased proof closes the zero case.  The library's `≢-nonZero` takes the
-- proof relevantly, which the erased factor fact cannot supply.
nonZeroOf : (q : ℚ) → @0 q ≢ 0ℚ → ℚ.NonZero q
nonZeroOf (mkℚ (+ zero) _ _)  q≢0 = absurd₀ (q≢0 (ℚP.↥p≡0⇒p≡0 _ refl))
nonZeroOf (mkℚ (+ suc _) _ _) _   = _
nonZeroOf (mkℚ -[1+ _ ] _ _)  _   = _

-- The candidate raw value: the scaled-out value rounded down.  Exactness is
-- decided by scaling it back, so the rounding never reaches a frame.
candidateRaw : (sd : SignalDef) → @0 toℚ (SignalDef.factor sd) ≢ 0ℚ → ℚ → ℤ
candidateRaw sd factor≢0 v =
  floor (_÷ᵣ_ (v -ᵣ toℚ (SignalDef.offset sd)) (toℚ (SignalDef.factor sd))
          {{nonZeroOf (toℚ (SignalDef.factor sd)) factor≢0}})

-- The candidate is bound once, so the division runs once.
checkValue : (sd : SignalDef) → @0 toℚ (SignalDef.factor sd) ≢ 0ℚ → (v : ℚ) → EncodeRefusal ⊎ Encodable sd v
checkValue sd factor≢0 v
  with inBounds₀ v (toℚ (SignalDef.minimum sd)) (toℚ (SignalDef.maximum sd))
... | false because₀ _ = inj₁ OutOfRange
... | true  because₀ inRange
  with candidateRaw sd factor≢0 v
...   | raw
  with applyScaling raw (toℚ (SignalDef.factor sd)) (toℚ (SignalDef.offset sd)) ≟ℚ₀ v
...     | false because₀ _      = inj₁ NotRepresentable
...     | true  because₀ scaled =
  inj₂ (encodable raw (proj₁ (invert inRange)) (proj₂ (invert inRange)) (invert scaled))

-- ============================================================================
-- THE BITS
-- ============================================================================

-- The proof the bits are built under: the raw value fits them, so its
-- unsigned representation lies below 2^n.
@0 fitBound : ∀ {sd v} (raw : ℤ)
  → toℚ (SignalDef.minimum sd) ≤ v → v ≤ toℚ (SignalDef.maximum sd)
  → applyScaling raw (toℚ (SignalDef.factor sd)) (toℚ (SignalDef.offset sd)) ≡ v
  → SignalFacts sd
  → fromSigned raw (SignalDef.bitLength sd) < 2 ^ SignalDef.bitLength sd
fitBound {sd} raw lowOk highOk exact facts =
  RawFits-implies-bounded raw (SignalDef.bitLength sd) (SignalDef.isSigned sd) (SignalFacts.bitLength>0 facts)
    (rawFits raw lowOk highOk exact facts)

-- The bits of an encodable value, built from the proof that its raw value
-- fits them; nothing is checked.
encodedBits : ∀ {sd v} → Encodable sd v → @0 SignalFacts sd → BitVec (SignalDef.bitLength sd)
encodedBits {sd} (encodable raw lowOk highOk exact) facts =
  ℕToBitVec (fromSigned raw (SignalDef.bitLength sd)) (fitBound raw lowOk highOk exact facts)
