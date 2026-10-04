-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Pairwise disjointness, single-write preservation, and batch roundtrip.
--
-- Purpose: batch injection leaves every disjoint signal's extraction as it
--   was, and every signal it injected extracts back to its value.
-- Key results: injectOne-written, injectAll-preserves-disjoint,
--   injectAll-roundtrip.
--
-- The theorems quantify over the DBC's validity proof relevantly: a runtime
-- `ValidDBC` is `validated dbc proof` with the proof erased, the same value
-- at the type level, so each theorem speaks of the runtime's own frames.
module Aletheia.CAN.Batch.Properties.Roundtrip where

open import Aletheia.CAN.Frame using (CANFrame; CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (extractSignal; extractSignalCore; extractionBytes; scaleExtracted; withInjected)
open import Aletheia.CAN.Encoding.Arithmetic using (inBounds; toSigned)
open import Aletheia.CAN.Encoding.Value using (Encodable; checkValue; encodedBits; SignalFacts; OutOfRange; NotRepresentable)
open import Aletheia.CAN.Encoding.Properties.Value using (extractSignal-encodedBits; encodedBits-irrelevant)
open import Aletheia.CAN.Encoding.Properties.Disjoint using (withInjected-preserves-disjoint-bits-physical)
open import Aletheia.CAN.Endianness using (extractBits)
open import Aletheia.CAN.BatchFrameBuilding using (Request; requestedSignal; injectOne; injectAll; firstPastFrameEnd; validateAndBuild)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.Decidable using (PhysicallyDisjoint)
open import Aletheia.DBC.Decidable.SignalGeometry using (signalFitsFrame₀)
open import Aletheia.DBC.Properties using (physicallyDisjoint-sym)
open import Aletheia.DBC.Validity using (IsValidDBC; ValidDBC; validated; signalFacts)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ)
open import Aletheia.Data.Dec0 using (does₀)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.Prelude using (Found)
open import Data.Bool using (T; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Rational using (ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)

-- ============================================================================
-- PAIRWISE DISJOINTNESS FOR SIGNAL LISTS
-- ============================================================================

-- A signal is physically disjoint from all signals in a list
-- n is the frame byte count (for physicalBitPos)
data DisjointFromAll (n : ℕ) (sig : DBCSignal) : List (DBCSignal × ℚ) → Set where
  dfa-nil : DisjointFromAll n sig []
  dfa-cons : ∀ {s v rest}
    → PhysicallyDisjoint n sig s
    → DisjointFromAll n sig rest
    → DisjointFromAll n sig ((s , v) ∷ rest)

-- All pairs in a signal list are disjoint
data AllPairsDisjoint (n : ℕ) : List (DBCSignal × ℚ) → Set where
  apd-nil : AllPairsDisjoint n []
  apd-cons : ∀ {s v rest}
    → DisjointFromAll n s rest
    → AllPairsDisjoint n rest
    → AllPairsDisjoint n ((s , v) ∷ rest)

-- All signals in a list fit within payloadBytes * 8 bits
data AllSignalsFit (payloadBytes : ℕ) : List (DBCSignal × ℚ) → Set where
  asf-nil : AllSignalsFit payloadBytes []
  asf-cons : ∀ {s v rest}
    → SignalDef.startBit (DBCSignal.signalDef s) + SignalDef.bitLength (DBCSignal.signalDef s) ≤ payloadBytes * 8
    → AllSignalsFit payloadBytes rest
    → AllSignalsFit payloadBytes ((s , v) ∷ rest)

-- All signals come from a specific message
data AllFromMessage (msg : DBCMessage) : List (DBCSignal × ℚ) → Set where
  afm-nil  : AllFromMessage msg []
  afm-cons : ∀ {s v rest}
    → s ∈ DBCMessage.signals msg
    → AllFromMessage msg rest
    → AllFromMessage msg ((s , v) ∷ rest)

-- Helper: Signal fit bounds (parameterized by payload byte count)
signalFits : ℕ → SignalDef → Set
signalFits payloadBytes sig = SignalDef.startBit sig + SignalDef.bitLength sig ≤ payloadBytes * 8

-- A request list as the (signal, value) pairs it asks for.
pairs : ∀ {msg} → List (Request msg) → List (DBCSignal × ℚ)
pairs [] = []
pairs {msg} ((sig , v) ∷ rest) = (Found.item sig , v) ∷ pairs {msg} rest

private
  map-requested : ∀ {msg} (reqs : List (Request msg)) → map (requestedSignal {msg}) reqs ≡ map proj₁ (pairs {msg} reqs)
  map-requested [] = refl
  map-requested ((sig , v) ∷ rest) = cong (Found.item sig ∷_) (map-requested rest)

-- ============================================================================
-- THE BUILDER ESTABLISHES THE FIT THE THEOREMS BELOW ASSUME
-- ============================================================================

-- `firstPastFrameEnd` names the first signal whose last bit lies past the end
-- of a frame of `n` bytes, on the geometry proposition the ingest gates
-- decide.  Naming none means every signal fits, which is what the roundtrip
-- theorems ask of their caller: the builder checks it, so a caller that built
-- a frame has it already.
nonePastFrameEnd-fits : ∀ {n} (defs : List (DBCSignal × ℚ))
  → firstPastFrameEnd n (map proj₁ defs) ≡ nothing
  → AllSignalsFit n defs
nonePastFrameEnd-fits [] _ = asf-nil
nonePastFrameEnd-fits {n} ((s , v) ∷ rest) eq
  with does₀ (signalFitsFrame₀ n (SignalDef.startBit (DBCSignal.signalDef s))
                                 (SignalDef.bitLength (DBCSignal.signalDef s)))
       in fitsEq
... | true = asf-cons (≤ᵇ⇒≤ _ _ (subst T (sym fitsEq) tt))
                      (nonePastFrameEnd-fits rest eq)

-- The build path's own statement of it: a payload it answers with was built
-- from signals that all fit the frame the caller asked for.
validateAndBuild-fits : ∀ (vdbc : ValidDBC) (msg : Found (DBC.messages (ValidDBC.dbc vdbc)))
    (canId : CANId) (dlc : DLC) (reqs : List (Request (Found.item msg))) {payload}
  → validateAndBuild vdbc msg canId dlc reqs ≡ inj₂ payload
  → AllSignalsFit (dlcBytes dlc) (pairs {Found.item msg} reqs)
validateAndBuild-fits vdbc msg canId dlc reqs eq
  with firstPastFrameEnd (dlcBytes dlc) (map (requestedSignal {Found.item msg}) reqs) in fEq
... | nothing = nonePastFrameEnd-fits (pairs {Found.item msg} reqs) (trans (cong (firstPastFrameEnd (dlcBytes dlc)) (sym (map-requested reqs))) fEq)

-- ============================================================================
-- ONE WRITE PRESERVES DISJOINT EXTRACTION
-- ============================================================================

private
  extractSignal-bits-eq : ∀ {n} (frame₁ frame₂ : CANFrame n) sig bo
    → extractBits {SignalDef.bitLength sig} (extractionBytes frame₁ bo) (SignalDef.startBit sig)
      ≡ extractBits {SignalDef.bitLength sig} (extractionBytes frame₂ bo) (SignalDef.startBit sig)
    → extractSignal frame₁ sig bo ≡ extractSignal frame₂ sig bo
  extractSignal-bits-eq frame₁ frame₂ sig bo bits-eq = result-eq
    where
      open SignalDef sig
        using (startBit; bitLength; isSigned)
        renaming (minimum to minimumᵈ; maximum to maximumᵈ)
      minimum = toℚ minimumᵈ
      maximum = toℚ maximumᵈ

      bytes₁ = extractionBytes frame₁ bo
      bytes₂ = extractionBytes frame₂ bo

      core-eq : extractSignalCore bytes₁ sig ≡ extractSignalCore bytes₂ sig
      core-eq = cong (λ bits → toSigned (bitVecToℕ bits) bitLength isSigned) bits-eq

      value-eq : scaleExtracted (extractSignalCore bytes₁ sig) sig
               ≡ scaleExtracted (extractSignalCore bytes₂ sig) sig
      value-eq = cong (λ core → scaleExtracted core sig) core-eq

      bounds-eq : inBounds (scaleExtracted (extractSignalCore bytes₁ sig) sig) minimum maximum
                ≡ inBounds (scaleExtracted (extractSignalCore bytes₂ sig) sig) minimum maximum
      bounds-eq = cong (λ v → inBounds v minimum maximum) value-eq

      result-eq : extractSignal frame₁ sig bo ≡ extractSignal frame₂ sig bo
      result-eq with inBounds (scaleExtracted (extractSignalCore bytes₁ sig) sig) minimum maximum
                   | inBounds (scaleExtracted (extractSignalCore bytes₂ sig) sig) minimum maximum
                   | bounds-eq
      ... | true  | true  | _  = cong just value-eq
      ... | false | false | _  = refl
      ... | true  | false | ()
      ... | false | true  | ()

-- Writing one signal's bits leaves a physically disjoint signal's
-- extraction as it was, whatever the two byte orders.
single-write-preserves :
  ∀ {n} (s sig : DBCSignal) (bits : BitVec (SignalDef.bitLength (DBCSignal.signalDef s))) (frame : CANFrame n)
  → PhysicallyDisjoint n sig s
  → signalFits n (DBCSignal.signalDef s)
  → signalFits n (DBCSignal.signalDef sig)
  → extractSignal (withInjected (SignalDef.startBit (DBCSignal.signalDef s)) bits (DBCSignal.byteOrder s) frame)
                  (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
single-write-preserves s sig bits frame pd fits-s fits-sig =
  extractSignal-bits-eq _ frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    (withInjected-preserves-disjoint-bits-physical
      (SignalDef.startBit (DBCSignal.signalDef s)) bits (DBCSignal.byteOrder s) (DBCSignal.byteOrder sig)
      frame (SignalDef.startBit (DBCSignal.signalDef sig))
      (physicallyDisjoint-sym {_} {sig} {s} pd) fits-s fits-sig)

-- ============================================================================
-- WHAT ONE ACCEPTED INJECTION WRITES
-- ============================================================================

-- An injection that answers a frame accepted the value and wrote its bits.
injectOne-written : ∀ {n} (dbc : DBC) (iv : IsValidDBC dbc) (msg : Found (DBC.messages dbc))
    (frame frame' : CANFrame n) (sig : Found (DBCMessage.signals (Found.item msg))) (v : ℚ)
  → injectOne (validated dbc iv) msg frame (sig , v) ≡ inj₂ frame'
  → let sd    = DBCSignal.signalDef (Found.item sig)
        facts = signalFacts iv (Found.position msg) (Found.position sig)
    in Σ (Encodable sd v) λ e
       → (checkValue sd (SignalFacts.factor≢0 facts) v ≡ inj₂ e)
       × (frame' ≡ withInjected (SignalDef.startBit sd) (encodedBits e facts) (DBCSignal.byteOrder (Found.item sig)) frame)
injectOne-written dbc iv msg frame frame' sig v eq
  with checkValue (DBCSignal.signalDef (Found.item sig))
                  (SignalFacts.factor≢0 (signalFacts iv (Found.position msg) (Found.position sig))) v
       | eq
... | inj₁ OutOfRange       | ()
... | inj₁ NotRepresentable | ()
... | inj₂ e                | refl = e , refl , refl

-- An injection that answers a frame wrote the signal so that it extracts
-- back to its value.
injectOne-roundtrip : ∀ {n} (dbc : DBC) (iv : IsValidDBC dbc) (msg : Found (DBC.messages dbc))
    (frame frame' : CANFrame n) (sig : Found (DBCMessage.signals (Found.item msg))) (v : ℚ)
  → Found.item msg ∈ DBC.messages dbc
  → Found.item sig ∈ DBCMessage.signals (Found.item msg)
  → signalFits n (DBCSignal.signalDef (Found.item sig))
  → injectOne (validated dbc iv) msg frame (sig , v) ≡ inj₂ frame'
  → extractSignal frame' (DBCSignal.signalDef (Found.item sig)) (DBCSignal.byteOrder (Found.item sig)) ≡ just v
injectOne-roundtrip dbc iv msg frame frame' sig v msg∈ sig∈ fits eq
  with injectOne-written dbc iv msg frame frame' sig v eq
... | e , checked , refl =
  trans (cong (λ bits → extractSignal (withInjected (SignalDef.startBit sd) bits bo frame) sd bo)
              (encodedBits-irrelevant e (signalFacts iv (Found.position msg) (Found.position sig)) facts))
        (extractSignal-encodedBits sd _ v e checked facts bo frame fits)
  where
    sd    = DBCSignal.signalDef (Found.item sig)
    bo    = DBCSignal.byteOrder (Found.item sig)
    facts = signalFacts iv msg∈ sig∈

-- ============================================================================
-- KEY LEMMA: injectAll preserves extraction at disjoint positions
-- ============================================================================

injectAll-preserves-disjoint :
  ∀ {n} (dbc : DBC) (iv : IsValidDBC dbc) (msg : Found (DBC.messages dbc))
    (reqs : List (Request (Found.item msg))) (frame frame' : CANFrame n) (sig : DBCSignal)
  → AllSignalsFit n (pairs {Found.item msg} reqs)
  → signalFits n (DBCSignal.signalDef sig)
  → injectAll (validated dbc iv) msg frame reqs ≡ inj₂ frame'
  → DisjointFromAll n sig (pairs {Found.item msg} reqs)
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
injectAll-preserves-disjoint dbc iv msg [] frame .frame sig _ _ refl dfa-nil = refl
injectAll-preserves-disjoint dbc iv msg ((s , v) ∷ rest) frame frame' sig
    (asf-cons s-fits rest-fits) sig-fits eq (dfa-cons disj restDisj)
  with injectOne (validated dbc iv) msg frame (s , v) in injEq | eq
... | inj₁ _      | ()
... | inj₂ frame₁ | restEq =
  trans (injectAll-preserves-disjoint dbc iv msg rest frame₁ frame' sig rest-fits sig-fits restEq restDisj)
        (written (injectOne-written dbc iv msg frame frame₁ s v injEq))
  where
    written : _ → extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
                ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    written (e , _ , refl) =
      single-write-preserves (Found.item s) sig
        (encodedBits e (signalFacts iv (Found.position msg) (Found.position s))) frame disj s-fits sig-fits

-- ============================================================================
-- BATCH ROUNDTRIP: extracting any injected signal returns its value
-- ============================================================================

injectAll-roundtrip :
  ∀ {n} (dbc : DBC) (iv : IsValidDBC dbc) (msg : Found (DBC.messages dbc))
    (reqs : List (Request (Found.item msg))) (frame frame' : CANFrame n)
  → Found.item msg ∈ DBC.messages dbc
  → AllFromMessage (Found.item msg) (pairs {Found.item msg} reqs)
  → AllPairsDisjoint n (pairs {Found.item msg} reqs)
  → AllSignalsFit n (pairs {Found.item msg} reqs)
  → injectAll (validated dbc iv) msg frame reqs ≡ inj₂ frame'
  → ∀ {s v} → (s , v) ∈ pairs {Found.item msg} reqs
  → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
injectAll-roundtrip dbc iv msg [] _ _ _ _ _ _ _ ()
injectAll-roundtrip dbc iv msg ((s₀ , v₀) ∷ rest) frame frame' msg∈
    (afm-cons s₀∈ afm-rest) (apd-cons dfa apd-rest) (asf-cons s₀-fits asf-rest) eq mem
  with injectOne (validated dbc iv) msg frame (s₀ , v₀) in injEq | eq
... | inj₁ _      | ()
... | inj₂ frame₁ | restEq = go mem
  where
    go : ∀ {s v} → (s , v) ∈ pairs {Found.item msg} ((s₀ , v₀) ∷ rest)
       → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
    go (here refl) =
      trans (injectAll-preserves-disjoint dbc iv msg rest frame₁ frame' (Found.item s₀) asf-rest s₀-fits restEq dfa)
            (injectOne-roundtrip dbc iv msg frame frame₁ s₀ v₀ msg∈ s₀∈ s₀-fits injEq)
    go (there mem') = injectAll-roundtrip dbc iv msg rest frame₁ frame' msg∈ afm-rest apd-rest asf-rest restEq mem'
