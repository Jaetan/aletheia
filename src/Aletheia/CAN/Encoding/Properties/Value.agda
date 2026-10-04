-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What checking and encoding a signal value guarantee.
--
-- Each refusal of `checkValue` names the condition it found broken: out of
-- range means the value lies outside [minimum, maximum]; not representable
-- means no integer raw value scales to it.  An accepted value lies in the
-- range and scales exactly from its raw value, and the frame written with
-- its bits (`encodedBits`, through the frame writer `withInjected`)
-- extracts back to exactly that value.
--
-- The runtime carries these facts erased; each lemma here re-derives them
-- relevantly from the Bool checks the runtime ran.
--
-- DEFER-stdlib-mandate (Cat 29): `unscale` takes the `.{{_ : NonZero f}}` the
-- stdlib's `_÷_` mandates, and its call sites supply it explicitly as
-- `{{nonZeroOf …}}`, so instance resolution is trivial.
module Aletheia.CAN.Encoding.Properties.Value where

open import Aletheia.CAN.Encoding using (extractSignal; scaleExtracted; withInjected)
open import Aletheia.CAN.Encoding.Arithmetic using (applyScaling; inBounds; inBounds₀; fromSigned)
open import Aletheia.CAN.Encoding.Arithmetic.Range using (RawFits; unsigned-fits; signed-fits; SignedFits-implies-fromSigned-bounded)
open import Aletheia.CAN.Encoding.Value
  using (Encodable; encodable; EncodeRefusal; OutOfRange; NotRepresentable; checkValue; candidateRaw;
         SignalFacts; encodedBits; nonZeroOf; rawFits; fitBound)
open import Aletheia.CAN.Encoding.Properties.Roundtrip using (extractSignal-reduces-unsigned; extractSignal-reduces-signed)
open import Aletheia.CAN.Encoding.Properties.Arithmetic.Rational using (floor-int)
open import Aletheia.CAN.Endianness using (ByteOrder)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec; ℕToBitVec-irrelevant)
open import Aletheia.Data.Dec0 using (_because₀_; does₀; T-∧→; T-∧←)
open import Aletheia.Data.Dec0.Rational using (_≟ℚ₀_)
open import Aletheia.Prelude using (T→true)
open import Aletheia.DBC.DecRat using (toℚ)
open import Data.Bool using (Bool; true; false; T)
open import Data.Integer using (ℤ; +_)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _*_; _≤_; _<_; _>_; _^_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; floor; NonZero; 1/_)
  renaming (_≤_ to _≤ᵣ_; _+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_; _/_ to _/ᵣ_; _÷_ to _÷ᵣ_; -_ to -ᵣ_)
import Data.Rational.Properties as ℚP
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

private
  minOf maxOf factorOf offsetOf : SignalDef → ℚ
  minOf sd    = toℚ (SignalDef.minimum sd)
  maxOf sd    = toℚ (SignalDef.maximum sd)
  factorOf sd = toℚ (SignalDef.factor sd)
  offsetOf sd = toℚ (SignalDef.offset sd)

  -- Scaling an integer up and back down returns it.
  unscale : ∀ (r : ℤ) (f o : ℚ) .{{_ : NonZero f}} → ((r /ᵣ 1 *ᵣ f +ᵣ o) -ᵣ o) ÷ᵣ f ≡ r /ᵣ 1
  unscale r f o = trans (cong (_÷ᵣ f) dropOffset)
                        (trans (ℚP.*-assoc (r /ᵣ 1) f (1/ f))
                               (trans (cong (r /ᵣ 1 *ᵣ_) (ℚP.*-inverseʳ f)) (ℚP.*-identityʳ (r /ᵣ 1))))
    where
      dropOffset : (r /ᵣ 1 *ᵣ f +ᵣ o) -ᵣ o ≡ r /ᵣ 1 *ᵣ f
      dropOffset = trans (ℚP.+-assoc (r /ᵣ 1 *ᵣ f) o (-ᵣ o))
                         (trans (cong (r /ᵣ 1 *ᵣ f +ᵣ_) (ℚP.+-inverseʳ o)) (ℚP.+-identityʳ (r /ᵣ 1 *ᵣ f)))

-- ============================================================================
-- THE CHECKS
-- ============================================================================

-- An accepted value lies in the declared range and scales exactly from its
-- raw value.
checkValue-accepted : ∀ (sd : SignalDef) (@0 nz : factorOf sd ≢ 0ℚ) (v : ℚ) (e : Encodable sd v)
  → checkValue sd nz v ≡ inj₂ e
  → (minOf sd ≤ᵣ v) × (v ≤ᵣ maxOf sd) × (applyScaling (Encodable.raw e) (factorOf sd) (offsetOf sd) ≡ v)
checkValue-accepted sd nz v e eq
  with inBounds₀ v (minOf sd) (maxOf sd) in inB | eq
... | false because₀ _ | ()
... | true  because₀ _ | eq₁
  with candidateRaw sd nz v | eq₁
...   | r | eq₂
  with applyScaling r (factorOf sd) (offsetOf sd) ≟ℚ₀ v in sm | eq₂
...     | false because₀ _ | ()
...     | true  because₀ _ | refl =
  ℚP.≤ᵇ⇒≤ (proj₁ inRange) , ℚP.≤ᵇ⇒≤ (proj₂ inRange) ,
  ℚP.≤-antisym (ℚP.≤ᵇ⇒≤ (proj₁ scaled)) (ℚP.≤ᵇ⇒≤ (proj₂ scaled))
  where
    inRange = T-∧→ (subst T (sym (cong does₀ inB)) tt)
    scaled  = T-∧→ (subst T (sym (cong does₀ sm)) tt)

-- A value refused as out of range lies outside the declared range.
checkValue-out-of-range : ∀ (sd : SignalDef) (@0 nz : factorOf sd ≢ 0ℚ) (v : ℚ)
  → checkValue sd nz v ≡ inj₁ OutOfRange
  → ¬ ((minOf sd ≤ᵣ v) × (v ≤ᵣ maxOf sd))
checkValue-out-of-range sd nz v eq
  with inBounds₀ v (minOf sd) (maxOf sd) in inB | eq
... | false because₀ _ | refl = λ inRange →
  subst T (cong does₀ inB) (T-∧← (ℚP.≤⇒≤ᵇ (proj₁ inRange)) (ℚP.≤⇒≤ᵇ (proj₂ inRange)))
... | true  because₀ _ | eq₁
  with candidateRaw sd nz v | eq₁
...   | r | eq₂
  with applyScaling r (factorOf sd) (offsetOf sd) ≟ℚ₀ v | eq₂
...     | false because₀ _ | ()
...     | true  because₀ _ | ()

-- A value refused as not representable is the image of no integer raw value.
checkValue-not-representable : ∀ (sd : SignalDef) (@0 nz : factorOf sd ≢ 0ℚ) (v : ℚ)
  → checkValue sd nz v ≡ inj₁ NotRepresentable
  → ∀ (r : ℤ) → applyScaling r (factorOf sd) (offsetOf sd) ≢ v
checkValue-not-representable sd nz v eq
  with inBounds₀ v (minOf sd) (maxOf sd) | eq
... | false because₀ _ | ()
... | true  because₀ _ | eq₁
  with candidateRaw sd nz v in cand | eq₁
...   | c | eq₂
  with applyScaling c (factorOf sd) (offsetOf sd) ≟ℚ₀ v in sm | eq₂
...     | true  because₀ _ | ()
...     | false because₀ _ | refl = λ r scales →
  subst T (cong does₀ sm) (T-∧← (ℚP.≤⇒≤ᵇ (≤-same r scales)) (ℚP.≤⇒≤ᵇ (≥-same r scales)))
  where
    -- A raw value scaling to v is the candidate: v scaled out is that raw
    -- value exactly, whose floor is itself.
    candidate≡ : ∀ r → applyScaling r (factorOf sd) (offsetOf sd) ≡ v → c ≡ r
    candidate≡ r scales =
      trans (sym cand)
        (trans (cong (λ x → floor (_÷ᵣ_ (x -ᵣ offsetOf sd) (factorOf sd) {{nonZeroOf (factorOf sd) nz}})) (sym scales))
               (trans (cong floor (unscale r (factorOf sd) (offsetOf sd) {{nonZeroOf (factorOf sd) nz}})) (floor-int r)))
    candScales : ∀ r → applyScaling r (factorOf sd) (offsetOf sd) ≡ v
               → applyScaling c (factorOf sd) (offsetOf sd) ≡ v
    candScales r scales = trans (cong (λ x → applyScaling x (factorOf sd) (offsetOf sd)) (candidate≡ r scales)) scales
    ≤-same : ∀ r → applyScaling r (factorOf sd) (offsetOf sd) ≡ v
           → applyScaling c (factorOf sd) (offsetOf sd) ≤ᵣ v
    ≤-same r scales = ℚP.≤-reflexive (candScales r scales)
    ≥-same : ∀ r → applyScaling r (factorOf sd) (offsetOf sd) ≡ v
           → v ≤ᵣ applyScaling c (factorOf sd) (offsetOf sd)
    ≥-same r scales = ℚP.≤-reflexive (sym (candScales r scales))

-- ============================================================================
-- THE ROUNDTRIP
-- ============================================================================

private
  inBounds-complete : ∀ {v mn mx : ℚ} → mn ≤ᵣ v → v ≤ᵣ mx → inBounds v mn mx ≡ true
  inBounds-complete lo hi = T→true (T-∧← (ℚP.≤⇒≤ᵇ lo) (ℚP.≤⇒≤ᵇ hi))

  -- The frame written with a fitting raw value's bits extracts back to the
  -- value that raw value scales to.
  extract-written : ∀ {m} (sd : SignalDef) (bo : ByteOrder) (frame : CANFrame m) (raw : ℤ)
    → (s : Bool) → SignalDef.isSigned sd ≡ s → RawFits raw (SignalDef.bitLength sd) s
    → (bl>0 : SignalDef.bitLength sd > 0)
    → (@0 bound : fromSigned raw (SignalDef.bitLength sd) < 2 ^ SignalDef.bitLength sd)
    → inBounds (scaleExtracted raw sd) (minOf sd) (maxOf sd) ≡ true
    → SignalDef.startBit sd + SignalDef.bitLength sd ≤ m * 8
    → extractSignal (withInjected (SignalDef.startBit sd)
                                  (ℕToBitVec {SignalDef.bitLength sd} (fromSigned raw (SignalDef.bitLength sd)) bound) bo frame) sd bo
      ≡ just (scaleExtracted raw sd)
  extract-written sd bo frame .(+ k) false unsigned (unsigned-fits {k} refl k<) _ bound bounds fits =
    trans (cong (λ bits → extractSignal (withInjected (SignalDef.startBit sd) bits bo frame) sd bo)
                (ℕToBitVec-irrelevant {SignalDef.bitLength sd} k bound k<))
          (extractSignal-reduces-unsigned k sd bo frame bounds unsigned fits k<)
  extract-written sd bo frame raw true signed (signed-fits sf) bl>0 bound bounds fits =
    trans (cong (λ bits → extractSignal (withInjected (SignalDef.startBit sd) bits bo frame) sd bo)
                (ℕToBitVec-irrelevant {SignalDef.bitLength sd} (fromSigned raw (SignalDef.bitLength sd)) bound
                  (SignedFits-implies-fromSigned-bounded raw (SignalDef.bitLength sd) bl>0 sf)))
          (extractSignal-reduces-signed raw sd bo frame bounds signed bl>0 sf fits)

-- The frame written with an accepted value's bits, its signal inside the
-- frame, extracts back to exactly that value.
extractSignal-encodedBits : ∀ {m} (sd : SignalDef) (@0 nz : factorOf sd ≢ 0ℚ) (v : ℚ) (e : Encodable sd v)
  → checkValue sd nz v ≡ inj₂ e
  → (facts : SignalFacts sd) (bo : ByteOrder) (frame : CANFrame m)
  → SignalDef.startBit sd + SignalDef.bitLength sd ≤ m * 8
  → extractSignal (withInjected (SignalDef.startBit sd) (encodedBits e facts) bo frame) sd bo ≡ just v
extractSignal-encodedBits sd nz v e@(encodable raw lowOk highOk exactOk) accepted facts bo frame fits =
  subst (λ x → extractSignal (withInjected (SignalDef.startBit sd) (encodedBits e facts) bo frame) sd bo ≡ just x)
        exact
        (extract-written sd bo frame raw (SignalDef.isSigned sd) refl (rawFits raw lo hi exact facts)
                         (SignalFacts.bitLength>0 facts)
                         (fitBound raw lowOk highOk exactOk facts)
                         (inBounds-complete (subst (minOf sd ≤ᵣ_) (sym exact) lo) (subst (_≤ᵣ maxOf sd) (sym exact) hi))
                         fits)
  where
    checks = checkValue-accepted sd nz v e accepted
    lo     = proj₁ checks
    hi     = proj₁ (proj₂ checks)
    exact  = proj₂ (proj₂ checks)

-- The facts are erased and never shape the bits: two proofs of them give the
-- same bits.
encodedBits-irrelevant : ∀ {sd v} (e : Encodable sd v) (@0 f₁ f₂ : SignalFacts sd)
  → encodedBits e f₁ ≡ encodedBits e f₂
encodedBits-irrelevant {sd} (encodable raw lowOk highOk exactOk) f₁ f₂ =
  ℕToBitVec-irrelevant {SignalDef.bitLength sd} (fromSigned raw (SignalDef.bitLength sd))
    (fitBound raw lowOk highOk exactOk f₁) (fitBound raw lowOk highOk exactOk f₂)
