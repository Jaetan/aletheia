{-# OPTIONS --safe --without-K #-}

-- Pairwise disjointness, single-injection preservation, and batch roundtrip.
--
-- Purpose: Core inductive proofs that batch injection preserves extraction
--   at disjoint positions, and that injected signals can be extracted back.
-- Key results: injectAll-preserves-disjoint, injectAll-roundtrip.
module Aletheia.CAN.Batch.Properties.Roundtrip where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (extractSignal; extractSignalCore; extractionBytes; scaleExtracted; injectSignal)
open import Aletheia.CAN.Encoding.Properties using (
  injectSignal-preserves-disjoint-bits-physical;
  signalValue;
  injectSignal-reduces-unsigned; injectSignal-reduces-signed;
  extractSignal-reduces-unsigned; extractSignal-reduces-signed;
  SignedFits;
  removeScaling-applyScaling-exact; removeScaling-nothing⇒zero)
open import Aletheia.CAN.Encoding.Arithmetic using (inBounds; toSigned; removeScaling)
open import Aletheia.CAN.Endianness using (extractBits)
open import Aletheia.CAN.BatchFrameBuilding using (injectAll)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Properties using (PhysicallyDisjoint; physicallyDisjoint-sym)

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _^_; _>_; _∸_; suc; _<?_; _≤?_)
open import Data.Rational using (ℚ; 0ℚ)
open import Aletheia.DBC.DecRat using (DecRat; 0ᵈ; toℚ)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Bool using (true; false)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (case_of_)

open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ)

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

-- Helper: Signal fit bounds (parameterized by payload byte count)
signalFits : ℕ → SignalDef → Set
signalFits payloadBytes sig = SignalDef.startBit sig + SignalDef.bitLength sig ≤ payloadBytes * 8

-- ============================================================================
-- SINGLE INJECTION PRESERVES DISJOINT EXTRACTION
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
        renaming (factor to factorᵈ; offset to offsetᵈ; minimum to minimumᵈ; maximum to maximumᵈ)
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

-- PhysicallyDisjoint is sufficient for any byte order combination.
single-inject-preserves :
  ∀ {n} (frame frame' : CANFrame n) (s : DBCSignal) (v : ℚ) (sig : DBCSignal)
  → PhysicallyDisjoint n sig s
  → signalFits n (DBCSignal.signalDef s)
  → signalFits n (DBCSignal.signalDef sig)
  → injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame ≡ just frame'
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
single-inject-preserves frame frame' s v sig pd fits-s fits-sig inj-eq =
  extractSignal-bits-eq frame' frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) bits-preserved
  where
    bits-preserved = injectSignal-preserves-disjoint-bits-physical v
      (DBCSignal.signalDef s) (DBCSignal.byteOrder s) (DBCSignal.byteOrder sig)
      frame frame' (SignalDef.startBit (DBCSignal.signalDef sig))
      inj-eq (physicallyDisjoint-sym {_} {sig} {s} pd) fits-s fits-sig

-- ============================================================================
-- KEY LEMMA: injectAll preserves extraction at disjoint positions
-- ============================================================================

injectAll-preserves-disjoint :
  ∀ {n} (sigs : List (DBCSignal × ℚ)) (frame frame' : CANFrame n)
    (sig : DBCSignal)
  → AllSignalsFit n sigs
  → signalFits n (DBCSignal.signalDef sig)
  → injectAll frame sigs ≡ inj₂ frame'
  → DisjointFromAll n sig sigs
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)

injectAll-preserves-disjoint [] frame .frame sig _ _ refl dfa-nil = refl

injectAll-preserves-disjoint ((s , v) ∷ rest) frame frame' sig
    (asf-cons s-fits rest-fits) sig-fits eq (dfa-cons disj restDisj)
  with injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame in injEq
... | nothing = case eq of λ ()
... | just frame₁ = proof
  where
    restEq : injectAll frame₁ rest ≡ inj₂ frame'
    restEq with injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame
    ... | just _ = eq
    ... | nothing = case injEq of λ ()

    step1 : extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    step1 = injectAll-preserves-disjoint rest frame₁ frame' sig rest-fits sig-fits restEq restDisj

    step2 : extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    step2 = single-inject-preserves frame frame₁ s v sig disj s-fits sig-fits injEq

    proof : extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    proof = trans step1 step2

-- ============================================================================
-- SINGLE SIGNAL ROUNDTRIP PREDICATE
-- ============================================================================

-- A (signal, value) pair roundtrips: inject then extract returns v
InjectRoundtrips : ℕ → DBCSignal → ℚ → Set
InjectRoundtrips n sig v =
  ∀ (frame frame' : CANFrame n)
  → injectSignal v (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame ≡ just frame'
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) ≡ just v

-- All signals in a list roundtrip
data AllRoundtrip (n : ℕ) : List (DBCSignal × ℚ) → Set where
  ar-nil  : AllRoundtrip n []
  ar-cons : ∀ {s v rest}
    → InjectRoundtrips n s v → AllRoundtrip n rest → AllRoundtrip n ((s , v) ∷ rest)

-- ============================================================================
-- BRIDGE LEMMAS: from existing roundtrips to InjectRoundtrips
-- ============================================================================

-- Unsigned signals: bridge from Encoding.Properties roundtrip
roundtrip-unsigned→IR :
  ∀ {m} (n : ℕ) (sig : DBCSignal)
  → inBounds (signalValue (+ n) (DBCSignal.signalDef sig))
             (toℚ (SignalDef.minimum (DBCSignal.signalDef sig)))
             (toℚ (SignalDef.maximum (DBCSignal.signalDef sig))) ≡ true
  → toℚ (SignalDef.factor (DBCSignal.signalDef sig)) ≢ 0ℚ
  → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ false
  → signalFits m (DBCSignal.signalDef sig)
  → n < 2 ^ SignalDef.bitLength (DBCSignal.signalDef sig)
  → InjectRoundtrips m sig (signalValue (+ n) (DBCSignal.signalDef sig))
roundtrip-unsigned→IR n sig bounds-ok factor≢0 unsigned fits n<2^bl frame frame' inj-eq =
  subst (λ f → extractSignal f sd bo ≡ just v) frame'-eq extract-reduces
  where
    sd = DBCSignal.signalDef sig
    bo = DBCSignal.byteOrder sig
    v  = signalValue (+ n) sd
    inject-reduces = injectSignal-reduces-unsigned n sd bo frame bounds-ok factor≢0 n<2^bl
    frame'-eq      = just-injective (trans (sym inject-reduces) inj-eq)
    extract-reduces = extractSignal-reduces-unsigned n sd bo frame bounds-ok unsigned fits n<2^bl

-- Signed signals: bridge from Encoding.Properties roundtrip
roundtrip-signed→IR :
  ∀ {m} (z : ℤ) (sig : DBCSignal)
  → inBounds (signalValue z (DBCSignal.signalDef sig))
             (toℚ (SignalDef.minimum (DBCSignal.signalDef sig)))
             (toℚ (SignalDef.maximum (DBCSignal.signalDef sig))) ≡ true
  → toℚ (SignalDef.factor (DBCSignal.signalDef sig)) ≢ 0ℚ
  → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ true
  → SignalDef.bitLength (DBCSignal.signalDef sig) > 0
  → SignedFits z (SignalDef.bitLength (DBCSignal.signalDef sig))
  → signalFits m (DBCSignal.signalDef sig)
  → InjectRoundtrips m sig (signalValue z (DBCSignal.signalDef sig))
roundtrip-signed→IR z sig bounds-ok factor≢0 signed bl>0 sf fits frame frame' inj-eq =
  subst (λ f → extractSignal f sd bo ≡ just v) frame'-eq extract-reduces
  where
    sd = DBCSignal.signalDef sig
    bo = DBCSignal.byteOrder sig
    v  = signalValue z sd
    inject-reduces  = injectSignal-reduces-signed z sd bo frame bounds-ok factor≢0 bl>0 sf
    frame'-eq       = just-injective (trans (sym inject-reduces) inj-eq)
    extract-reduces = extractSignal-reduces-signed z sd bo frame bounds-ok signed bl>0 sf fits

-- ============================================================================
-- BATCH ROUNDTRIP: extracting any injected signal returns its value
-- ============================================================================

injectAll-roundtrip :
  ∀ {n} (sigs : List (DBCSignal × ℚ)) (frame frame' : CANFrame n)
  → AllPairsDisjoint n sigs
  → AllSignalsFit n sigs
  → AllRoundtrip n sigs
  → injectAll frame sigs ≡ inj₂ frame'
  → ∀ {s v} → (s , v) ∈ sigs
  → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v

injectAll-roundtrip [] _ _ _ _ _ _ ()

injectAll-roundtrip ((s₀ , v₀) ∷ rest) frame frame'
    (apd-cons dfa apd-rest) (asf-cons s₀-fits asf-rest) (ar-cons ir₀ ar-rest) eq mem
  with injectSignal v₀ (DBCSignal.signalDef s₀) (DBCSignal.byteOrder s₀) frame in injEq
... | nothing = case eq of λ ()
... | just frame₁ = go mem
  where
    restEq : injectAll frame₁ rest ≡ inj₂ frame'
    restEq with injectSignal v₀ (DBCSignal.signalDef s₀) (DBCSignal.byteOrder s₀) frame
    ... | just _  = eq
    ... | nothing = case injEq of λ ()

    go : ∀ {s v} → (s , v) ∈ ((s₀ , v₀) ∷ rest)
       → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
    go (here refl) = trans preserve (ir₀ frame frame₁ injEq)
      where
        preserve = injectAll-preserves-disjoint rest frame₁ frame' s₀
                     asf-rest s₀-fits restEq dfa
    go (there mem') = injectAll-roundtrip rest frame₁ frame' apd-rest asf-rest ar-rest restEq mem'
