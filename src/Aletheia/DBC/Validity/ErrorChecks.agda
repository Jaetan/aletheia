{-# OPTIONS --safe --without-K #-}

-- Per-check soundness and completeness for all 8 error-severity checks.
--
-- For each error check: checkE args ≡ [] ↔ condition(args)
-- Proved by case analysis on the Dec used in each check function.
module Aletheia.DBC.Validity.ErrorChecks where

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using
  ( checkBitLengthZero; checkAllBitLengthZero
  ; checkFactorZeroSig; checkAllFactorZero
  ; checkSignalExceedsDLC; checkAllSignalExceedsDLC
  ; checkDupIdPair; checkDupIdAgainstList; checkDuplicateMessageIds
  ; checkDupSigPair; checkDupSigAgainstList; checkDupSigTriangular
  ; checkAllDuplicateSignalNames
  ; checkOverlapPair; checkOverlapAgainstList; checkOverlapTriangular
  ; checkAllSignalOverlaps
  ; checkMuxFoundSig; checkAllMuxFound
  ; checkMuxAlwaysPresentSig; checkAllMuxAlwaysPresent
  ; findSignalPresence
  )
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Validity using (NonZeroBitLength; NonZeroFactor; BitsInFrame; MuxResolvable; MuxIsAlways)
open import Aletheia.DBC.Validity.Combinators using
  ( liftConcatMap-sound; liftConcatMap-complete
  ; requireDec-sound; requireDec-complete
  ; rejectDec-sound; rejectDec-complete
  ; liftTriangular-sound; liftTriangular-complete )
open import Aletheia.DBC.Properties using (SignalPairValid; signalPairValid?)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (_≤?_) renaming (_≟_ to _≟ₙ_)
open import Data.Integer using (ℤ; +_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Rational using (ℚ)
open import Data.String.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- ============================================================================
-- CHECK 10: BIT LENGTH ZERO
-- ============================================================================

checkBitLengthZero-sound : ∀ msgName sig →
  checkBitLengthZero msgName sig ≡ [] → NonZeroBitLength sig
checkBitLengthZero-sound _ sig =
  rejectDec-sound (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ₙ 0) _

checkBitLengthZero-complete : ∀ msgName sig →
  NonZeroBitLength sig → checkBitLengthZero msgName sig ≡ []
checkBitLengthZero-complete _ sig =
  rejectDec-complete (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ₙ 0) _

checkAllBitLengthZero-sound : ∀ msgs →
  checkAllBitLengthZero msgs ≡ [] →
  All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs
checkAllBitLengthZero-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkBitLengthZero-sound (DBCMessage.name msg)) _

checkAllBitLengthZero-complete : ∀ msgs →
  All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs →
  checkAllBitLengthZero msgs ≡ []
checkAllBitLengthZero-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkBitLengthZero-complete (DBCMessage.name msg)) _

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig-sound : ∀ msgName sig →
  checkFactorZeroSig msgName sig ≡ [] → NonZeroFactor sig
checkFactorZeroSig-sound _ sig =
  rejectDec-sound (ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)) _

checkFactorZeroSig-complete : ∀ msgName sig →
  NonZeroFactor sig → checkFactorZeroSig msgName sig ≡ []
checkFactorZeroSig-complete _ sig =
  rejectDec-complete (ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)) _

checkAllFactorZero-sound : ∀ msgs →
  checkAllFactorZero msgs ≡ [] →
  All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs
checkAllFactorZero-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkFactorZeroSig-sound (DBCMessage.name msg)) _

checkAllFactorZero-complete : ∀ msgs →
  All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs →
  checkAllFactorZero msgs ≡ []
checkAllFactorZero-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkFactorZeroSig-complete (DBCMessage.name msg)) _

-- ============================================================================
-- CHECK 8: SIGNAL EXCEEDS DLC
-- ============================================================================

checkSignalExceedsDLC-sound : ∀ msgName dlc sig →
  checkSignalExceedsDLC msgName dlc sig ≡ [] →
  BitsInFrame dlc sig
checkSignalExceedsDLC-sound _ dlc sig =
  requireDec-sound (SignalDef.startBit (DBCSignal.signalDef sig)
                    + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8) _

checkSignalExceedsDLC-complete : ∀ msgName dlc sig →
  BitsInFrame dlc sig →
  checkSignalExceedsDLC msgName dlc sig ≡ []
checkSignalExceedsDLC-complete _ dlc sig =
  requireDec-complete (SignalDef.startBit (DBCSignal.signalDef sig)
                       + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8) _

checkAllSignalExceedsDLC-sound : ∀ msgs →
  checkAllSignalExceedsDLC msgs ≡ [] →
  All (λ m → All (BitsInFrame (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)) msgs
checkAllSignalExceedsDLC-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkSignalExceedsDLC-sound (DBCMessage.name msg) (dlcBytes (DBCMessage.dlc msg))) _

checkAllSignalExceedsDLC-complete : ∀ msgs →
  All (λ m → All (BitsInFrame (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)) msgs →
  checkAllSignalExceedsDLC msgs ≡ []
checkAllSignalExceedsDLC-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkSignalExceedsDLC-complete (DBCMessage.name msg) (dlcBytes (DBCMessage.dlc msg))) _

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs (triangular)
-- ============================================================================

checkDupIdPair-sound : ∀ m1 m2 →
  checkDupIdPair m1 m2 ≡ [] → DBCMessage.id m1 ≢ DBCMessage.id m2
checkDupIdPair-sound m1 m2 =
  rejectDec-sound (DBCMessage.id m1 ≟-CANId DBCMessage.id m2) _

checkDupIdPair-complete : ∀ m1 m2 →
  DBCMessage.id m1 ≢ DBCMessage.id m2 → checkDupIdPair m1 m2 ≡ []
checkDupIdPair-complete m1 m2 =
  rejectDec-complete (DBCMessage.id m1 ≟-CANId DBCMessage.id m2) _

checkDupIdAgainstList-sound : ∀ m rest →
  checkDupIdAgainstList m rest ≡ [] →
  All (λ other → DBCMessage.id m ≢ DBCMessage.id other) rest
checkDupIdAgainstList-sound m =
  liftConcatMap-sound (checkDupIdPair m) (checkDupIdPair-sound m)

checkDupIdAgainstList-complete : ∀ m rest →
  All (λ other → DBCMessage.id m ≢ DBCMessage.id other) rest →
  checkDupIdAgainstList m rest ≡ []
checkDupIdAgainstList-complete m =
  liftConcatMap-complete (checkDupIdPair m) (checkDupIdPair-complete m)

checkDuplicateMessageIds-sound : ∀ msgs →
  checkDuplicateMessageIds msgs ≡ [] →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
checkDuplicateMessageIds-sound =
  liftTriangular-sound checkDupIdPair checkDupIdPair-sound

checkDuplicateMessageIds-complete : ∀ msgs →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs →
  checkDuplicateMessageIds msgs ≡ []
checkDuplicateMessageIds-complete =
  liftTriangular-complete checkDupIdPair checkDupIdPair-complete

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (nested triangular)
-- ============================================================================

checkDupSigPair-sound : ∀ msgName s1 s2 →
  checkDupSigPair msgName s1 s2 ≡ [] → DBCSignal.name s1 ≢ DBCSignal.name s2
checkDupSigPair-sound _ s1 s2 =
  rejectDec-sound (DBCSignal.name s1 ≟ DBCSignal.name s2) _

checkDupSigPair-complete : ∀ msgName s1 s2 →
  DBCSignal.name s1 ≢ DBCSignal.name s2 → checkDupSigPair msgName s1 s2 ≡ []
checkDupSigPair-complete _ s1 s2 =
  rejectDec-complete (DBCSignal.name s1 ≟ DBCSignal.name s2) _

checkDupSigAgainstList-sound : ∀ msgName sig rest →
  checkDupSigAgainstList msgName sig rest ≡ [] →
  All (λ other → DBCSignal.name sig ≢ DBCSignal.name other) rest
checkDupSigAgainstList-sound msgName sig =
  liftConcatMap-sound (checkDupSigPair msgName sig) (checkDupSigPair-sound msgName sig)

checkDupSigAgainstList-complete : ∀ msgName sig rest →
  All (λ other → DBCSignal.name sig ≢ DBCSignal.name other) rest →
  checkDupSigAgainstList msgName sig rest ≡ []
checkDupSigAgainstList-complete msgName sig =
  liftConcatMap-complete (checkDupSigPair msgName sig) (checkDupSigPair-complete msgName sig)

checkDupSigTriangular-sound : ∀ msgName sigs →
  checkDupSigTriangular msgName sigs ≡ [] →
  AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂) sigs
checkDupSigTriangular-sound msgName =
  liftTriangular-sound (checkDupSigPair msgName) (checkDupSigPair-sound msgName)

checkDupSigTriangular-complete : ∀ msgName sigs →
  AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂) sigs →
  checkDupSigTriangular msgName sigs ≡ []
checkDupSigTriangular-complete msgName =
  liftTriangular-complete (checkDupSigPair msgName) (checkDupSigPair-complete msgName)

checkAllDuplicateSignalNames-sound : ∀ msgs →
  checkAllDuplicateSignalNames msgs ≡ [] →
  All (λ m → AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂)
                       (DBCMessage.signals m)) msgs
checkAllDuplicateSignalNames-sound = liftConcatMap-sound _ λ msg →
  checkDupSigTriangular-sound (DBCMessage.name msg) (DBCMessage.signals msg)

checkAllDuplicateSignalNames-complete : ∀ msgs →
  All (λ m → AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂)
                       (DBCMessage.signals m)) msgs →
  checkAllDuplicateSignalNames msgs ≡ []
checkAllDuplicateSignalNames-complete = liftConcatMap-complete _ λ msg →
  checkDupSigTriangular-complete (DBCMessage.name msg) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 9: SIGNAL OVERLAP (nested triangular via signalPairValid?)
-- ============================================================================

checkOverlapPair-sound : ∀ msgName n s1 s2 →
  checkOverlapPair msgName n s1 s2 ≡ [] → SignalPairValid n s1 s2
checkOverlapPair-sound _ n s1 s2 =
  requireDec-sound (signalPairValid? n s1 s2) _

checkOverlapPair-complete : ∀ msgName n s1 s2 →
  SignalPairValid n s1 s2 → checkOverlapPair msgName n s1 s2 ≡ []
checkOverlapPair-complete _ n s1 s2 =
  requireDec-complete (signalPairValid? n s1 s2) _

checkOverlapAgainstList-sound : ∀ msgName n sig rest →
  checkOverlapAgainstList msgName n sig rest ≡ [] →
  All (SignalPairValid n sig) rest
checkOverlapAgainstList-sound msgName n sig =
  liftConcatMap-sound (checkOverlapPair msgName n sig) (checkOverlapPair-sound msgName n sig)

checkOverlapAgainstList-complete : ∀ msgName n sig rest →
  All (SignalPairValid n sig) rest →
  checkOverlapAgainstList msgName n sig rest ≡ []
checkOverlapAgainstList-complete msgName n sig =
  liftConcatMap-complete (checkOverlapPair msgName n sig) (checkOverlapPair-complete msgName n sig)

checkOverlapTriangular-sound : ∀ msgName n sigs →
  checkOverlapTriangular msgName n sigs ≡ [] →
  AllPairs (SignalPairValid n) sigs
checkOverlapTriangular-sound msgName n =
  liftTriangular-sound (checkOverlapPair msgName n) (checkOverlapPair-sound msgName n)

checkOverlapTriangular-complete : ∀ msgName n sigs →
  AllPairs (SignalPairValid n) sigs →
  checkOverlapTriangular msgName n sigs ≡ []
checkOverlapTriangular-complete msgName n =
  liftTriangular-complete (checkOverlapPair msgName n) (checkOverlapPair-complete msgName n)

checkAllSignalOverlaps-sound : ∀ msgs →
  checkAllSignalOverlaps msgs ≡ [] →
  All (λ m → AllPairs (SignalPairValid (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)) msgs
checkAllSignalOverlaps-sound = liftConcatMap-sound _ λ msg →
  checkOverlapTriangular-sound (DBCMessage.name msg) (dlcBytes (DBCMessage.dlc msg))
    (DBCMessage.signals msg)

checkAllSignalOverlaps-complete : ∀ msgs →
  All (λ m → AllPairs (SignalPairValid (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)) msgs →
  checkAllSignalOverlaps msgs ≡ []
checkAllSignalOverlaps-complete = liftConcatMap-complete _ λ msg →
  checkOverlapTriangular-complete (DBCMessage.name msg) (dlcBytes (DBCMessage.dlc msg))
    (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 4: MULTIPLEXOR NOT FOUND
-- ============================================================================

checkMuxFoundSig-sound : ∀ msgName sigs sig →
  checkMuxFoundSig msgName sigs sig ≡ [] →
  MuxResolvable sigs (DBCSignal.presence sig)
checkMuxFoundSig-sound msgName sigs sig eq with DBCSignal.presence sig
... | Always = tt
... | When muxName _ with any? (λ s → DBCSignal.name s ≟ muxName) sigs
...   | yes p = p
checkMuxFoundSig-sound _ _ _ () | When _ _ | no _

checkMuxFoundSig-complete : ∀ msgName sigs sig →
  MuxResolvable sigs (DBCSignal.presence sig) →
  checkMuxFoundSig msgName sigs sig ≡ []
checkMuxFoundSig-complete msgName sigs sig p with DBCSignal.presence sig
... | Always = refl
... | When muxName _ with any? (λ s → DBCSignal.name s ≟ muxName) sigs
...   | yes _ = refl
...   | no ¬a = ⊥-elim (¬a p)

checkAllMuxFound-sound : ∀ msgs →
  checkAllMuxFound msgs ≡ [] →
  All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs
checkAllMuxFound-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _
    (checkMuxFoundSig-sound (DBCMessage.name msg) (DBCMessage.signals msg)) _

checkAllMuxFound-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxFound msgs ≡ []
checkAllMuxFound-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _
    (checkMuxFoundSig-complete (DBCMessage.name msg) (DBCMessage.signals msg)) _

-- ============================================================================
-- CHECK 5: MULTIPLEXOR NOT ALWAYS PRESENT
-- ============================================================================

checkMuxAlwaysPresentSig-sound : ∀ msgName sigs sig →
  checkMuxAlwaysPresentSig msgName sigs sig ≡ [] →
  MuxIsAlways sigs (DBCSignal.presence sig)
checkMuxAlwaysPresentSig-sound msgName sigs sig eq with DBCSignal.presence sig
... | Always = tt
... | When muxName _ with findSignalPresence muxName sigs
...   | nothing     = tt
...   | just Always = tt
checkMuxAlwaysPresentSig-sound _ _ _ () | When _ _ | just (When _ _)

checkMuxAlwaysPresentSig-complete : ∀ msgName sigs sig →
  MuxIsAlways sigs (DBCSignal.presence sig) →
  checkMuxAlwaysPresentSig msgName sigs sig ≡ []
checkMuxAlwaysPresentSig-complete msgName sigs sig p with DBCSignal.presence sig
... | Always = refl
... | When muxName _ with findSignalPresence muxName sigs
...   | nothing     = refl
...   | just Always = refl
...   | just (When _ _) = ⊥-elim p

checkAllMuxAlwaysPresent-sound : ∀ msgs →
  checkAllMuxAlwaysPresent msgs ≡ [] →
  All (λ m → All (λ sig → MuxIsAlways (DBCMessage.signals m)
                                        (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs
checkAllMuxAlwaysPresent-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _
    (checkMuxAlwaysPresentSig-sound (DBCMessage.name msg) (DBCMessage.signals msg)) _

checkAllMuxAlwaysPresent-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxIsAlways (DBCMessage.signals m)
                                        (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxAlwaysPresent msgs ≡ []
checkAllMuxAlwaysPresent-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _
    (checkMuxAlwaysPresentSig-complete (DBCMessage.name msg) (DBCMessage.signals msg)) _
