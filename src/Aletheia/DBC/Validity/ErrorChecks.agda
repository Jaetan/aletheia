{-# OPTIONS --safe --without-K #-}

-- Per-check soundness and completeness for all 8 error-severity checks.
--
-- For each error check: checkE args ≡ [] ↔ condition(args)
-- Proved by case analysis on the Dec used in each check function.
module Aletheia.DBC.Validity.ErrorChecks where
open import Aletheia.DBC.Identifier using (Identifier; nameStr)
open import Aletheia.DBC.Types using (signalNameStr; messageNameStr)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using
  ( checkBitLengthZero; checkAllBitLengthZero
  ; checkFactorZeroSig; checkAllFactorZero
  ; checkSignalExceedsDLC; checkAllSignalExceedsDLC
  ; checkDuplicateIdPair; checkDuplicateIdAgainstList; checkDuplicateMessageIds
  ; checkDuplicateSignalPair; checkDuplicateSignalAgainstList; checkDuplicateSignalTriangular
  ; checkAllDuplicateSignalNames
  ; checkOverlapPair; checkOverlapAgainstList; checkOverlapTriangular
  ; checkAllSignalOverlaps
  ; checkMuxFoundSig; checkAllMuxFound
  ; checkMuxCycleSig; checkAllMuxCycle
  ; findSignalPresence; walkMux
  )
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Validity using (NonZeroBitLength; NonZeroFactor; BitsInFrame; MuxResolvable; MuxAcyclic)
open import Aletheia.DBC.Validity.Combinators using
  ( liftConcatMap-sound; liftConcatMap-complete
  ; requireDec-sound; requireDec-complete
  ; rejectDec-sound; rejectDec-complete
  ; liftTriangular-sound; liftTriangular-complete )
open import Aletheia.DBC.Properties using (SignalPairValid; signalPairValid?)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_; concatMap; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (_≤?_; _≟_)
open import Data.Integer using (ℤ; +_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.DecRat using (DecRat)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Bool using (Bool; true; false)
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
  rejectDec-sound (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ 0) _

checkBitLengthZero-complete : ∀ msgName sig →
  NonZeroBitLength sig → checkBitLengthZero msgName sig ≡ []
checkBitLengthZero-complete _ sig =
  rejectDec-complete (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ 0) _

checkAllBitLengthZero-sound : ∀ msgs →
  checkAllBitLengthZero msgs ≡ [] →
  All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs
checkAllBitLengthZero-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkBitLengthZero-sound (messageNameStr msg)) _

checkAllBitLengthZero-complete : ∀ msgs →
  All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs →
  checkAllBitLengthZero msgs ≡ []
checkAllBitLengthZero-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkBitLengthZero-complete (messageNameStr msg)) _

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig-sound : ∀ msgName sig →
  checkFactorZeroSig msgName sig ≡ [] → NonZeroFactor sig
checkFactorZeroSig-sound _ sig =
  rejectDec-sound (DecRat.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)) _

checkFactorZeroSig-complete : ∀ msgName sig →
  NonZeroFactor sig → checkFactorZeroSig msgName sig ≡ []
checkFactorZeroSig-complete _ sig =
  rejectDec-complete (DecRat.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)) _

checkAllFactorZero-sound : ∀ msgs →
  checkAllFactorZero msgs ≡ [] →
  All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs
checkAllFactorZero-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkFactorZeroSig-sound (messageNameStr msg)) _

checkAllFactorZero-complete : ∀ msgs →
  All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs →
  checkAllFactorZero msgs ≡ []
checkAllFactorZero-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkFactorZeroSig-complete (messageNameStr msg)) _

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
  liftConcatMap-sound _ (checkSignalExceedsDLC-sound (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg))) _

checkAllSignalExceedsDLC-complete : ∀ msgs →
  All (λ m → All (BitsInFrame (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)) msgs →
  checkAllSignalExceedsDLC msgs ≡ []
checkAllSignalExceedsDLC-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkSignalExceedsDLC-complete (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg))) _

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs (triangular)
-- ============================================================================

checkDuplicateIdPair-sound : ∀ m1 m2 →
  checkDuplicateIdPair m1 m2 ≡ [] → DBCMessage.id m1 ≢ DBCMessage.id m2
checkDuplicateIdPair-sound m1 m2 =
  rejectDec-sound (DBCMessage.id m1 ≟-CANId DBCMessage.id m2) _

checkDuplicateIdPair-complete : ∀ m1 m2 →
  DBCMessage.id m1 ≢ DBCMessage.id m2 → checkDuplicateIdPair m1 m2 ≡ []
checkDuplicateIdPair-complete m1 m2 =
  rejectDec-complete (DBCMessage.id m1 ≟-CANId DBCMessage.id m2) _

checkDuplicateIdAgainstList-sound : ∀ m rest →
  checkDuplicateIdAgainstList m rest ≡ [] →
  All (λ other → DBCMessage.id m ≢ DBCMessage.id other) rest
checkDuplicateIdAgainstList-sound m =
  liftConcatMap-sound (checkDuplicateIdPair m) (checkDuplicateIdPair-sound m)

checkDuplicateIdAgainstList-complete : ∀ m rest →
  All (λ other → DBCMessage.id m ≢ DBCMessage.id other) rest →
  checkDuplicateIdAgainstList m rest ≡ []
checkDuplicateIdAgainstList-complete m =
  liftConcatMap-complete (checkDuplicateIdPair m) (checkDuplicateIdPair-complete m)

checkDuplicateMessageIds-sound : ∀ msgs →
  checkDuplicateMessageIds msgs ≡ [] →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
checkDuplicateMessageIds-sound =
  liftTriangular-sound checkDuplicateIdPair checkDuplicateIdPair-sound

checkDuplicateMessageIds-complete : ∀ msgs →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs →
  checkDuplicateMessageIds msgs ≡ []
checkDuplicateMessageIds-complete =
  liftTriangular-complete checkDuplicateIdPair checkDuplicateIdPair-complete

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (nested triangular)
-- ============================================================================

checkDuplicateSignalPair-sound : ∀ msgName s1 s2 →
  checkDuplicateSignalPair msgName s1 s2 ≡ [] → signalNameStr s1 ≢ signalNameStr s2
checkDuplicateSignalPair-sound _ s1 s2 =
  rejectDec-sound (signalNameStr s1 ≟ₛ signalNameStr s2) _

checkDuplicateSignalPair-complete : ∀ msgName s1 s2 →
  signalNameStr s1 ≢ signalNameStr s2 → checkDuplicateSignalPair msgName s1 s2 ≡ []
checkDuplicateSignalPair-complete _ s1 s2 =
  rejectDec-complete (signalNameStr s1 ≟ₛ signalNameStr s2) _

checkDuplicateSignalAgainstList-sound : ∀ msgName sig rest →
  checkDuplicateSignalAgainstList msgName sig rest ≡ [] →
  All (λ other → signalNameStr sig ≢ signalNameStr other) rest
checkDuplicateSignalAgainstList-sound msgName sig =
  liftConcatMap-sound (checkDuplicateSignalPair msgName sig) (checkDuplicateSignalPair-sound msgName sig)

checkDuplicateSignalAgainstList-complete : ∀ msgName sig rest →
  All (λ other → signalNameStr sig ≢ signalNameStr other) rest →
  checkDuplicateSignalAgainstList msgName sig rest ≡ []
checkDuplicateSignalAgainstList-complete msgName sig =
  liftConcatMap-complete (checkDuplicateSignalPair msgName sig) (checkDuplicateSignalPair-complete msgName sig)

checkDuplicateSignalTriangular-sound : ∀ msgName sigs →
  checkDuplicateSignalTriangular msgName sigs ≡ [] →
  AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂) sigs
checkDuplicateSignalTriangular-sound msgName =
  liftTriangular-sound (checkDuplicateSignalPair msgName) (checkDuplicateSignalPair-sound msgName)

checkDuplicateSignalTriangular-complete : ∀ msgName sigs →
  AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂) sigs →
  checkDuplicateSignalTriangular msgName sigs ≡ []
checkDuplicateSignalTriangular-complete msgName =
  liftTriangular-complete (checkDuplicateSignalPair msgName) (checkDuplicateSignalPair-complete msgName)

checkAllDuplicateSignalNames-sound : ∀ msgs →
  checkAllDuplicateSignalNames msgs ≡ [] →
  All (λ m → AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂)
                       (DBCMessage.signals m)) msgs
checkAllDuplicateSignalNames-sound = liftConcatMap-sound _ λ msg →
  checkDuplicateSignalTriangular-sound (messageNameStr msg) (DBCMessage.signals msg)

checkAllDuplicateSignalNames-complete : ∀ msgs →
  All (λ m → AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂)
                       (DBCMessage.signals m)) msgs →
  checkAllDuplicateSignalNames msgs ≡ []
checkAllDuplicateSignalNames-complete = liftConcatMap-complete _ λ msg →
  checkDuplicateSignalTriangular-complete (messageNameStr msg) (DBCMessage.signals msg)

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
  checkOverlapTriangular-sound (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg))
    (DBCMessage.signals msg)

checkAllSignalOverlaps-complete : ∀ msgs →
  All (λ m → AllPairs (SignalPairValid (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)) msgs →
  checkAllSignalOverlaps msgs ≡ []
checkAllSignalOverlaps-complete = liftConcatMap-complete _ λ msg →
  checkOverlapTriangular-complete (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg))
    (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 4: MULTIPLEXOR NOT FOUND
-- ============================================================================

checkMuxFoundSig-sound : ∀ msgName sigs sig →
  checkMuxFoundSig msgName sigs sig ≡ [] →
  MuxResolvable sigs (DBCSignal.presence sig)
checkMuxFoundSig-sound msgName sigs sig eq with DBCSignal.presence sig
... | Always = tt
... | When muxName _ with any? (λ s → signalNameStr s ≟ₛ nameStr muxName) sigs
...   | yes p = p
checkMuxFoundSig-sound _ _ _ () | When _ _ | no _

checkMuxFoundSig-complete : ∀ msgName sigs sig →
  MuxResolvable sigs (DBCSignal.presence sig) →
  checkMuxFoundSig msgName sigs sig ≡ []
checkMuxFoundSig-complete msgName sigs sig p with DBCSignal.presence sig
... | Always = refl
... | When muxName _ with any? (λ s → signalNameStr s ≟ₛ nameStr muxName) sigs
...   | yes _ = refl
...   | no ¬a = ⊥-elim (¬a p)

checkAllMuxFound-sound : ∀ msgs →
  checkAllMuxFound msgs ≡ [] →
  All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs
checkAllMuxFound-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _
    (checkMuxFoundSig-sound (messageNameStr msg) (DBCMessage.signals msg)) _

checkAllMuxFound-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxFound msgs ≡ []
checkAllMuxFound-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _
    (checkMuxFoundSig-complete (messageNameStr msg) (DBCMessage.signals msg)) _

-- ============================================================================
-- CHECK 5: MULTIPLEXOR CYCLE
-- ============================================================================

checkMuxCycleSig-sound : ∀ msgName sigs sig →
  checkMuxCycleSig msgName sigs sig ≡ [] →
  MuxAcyclic sigs (DBCSignal.presence sig)
checkMuxCycleSig-sound msgName sigs sig eq
  with walkMux (length sigs) sigs (DBCSignal.presence sig)
... | true = refl
checkMuxCycleSig-sound _ _ _ () | false

checkMuxCycleSig-complete : ∀ msgName sigs sig →
  MuxAcyclic sigs (DBCSignal.presence sig) →
  checkMuxCycleSig msgName sigs sig ≡ []
checkMuxCycleSig-complete msgName sigs sig p
  with walkMux (length sigs) sigs (DBCSignal.presence sig)
... | true  = refl
checkMuxCycleSig-complete _ _ _ () | false

checkAllMuxCycle-sound : ∀ msgs →
  checkAllMuxCycle msgs ≡ [] →
  All (λ m → All (λ sig → MuxAcyclic (DBCMessage.signals m)
                                       (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs
checkAllMuxCycle-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _
    (checkMuxCycleSig-sound (messageNameStr msg) (DBCMessage.signals msg)) _

checkAllMuxCycle-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxAcyclic (DBCMessage.signals m)
                                       (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxCycle msgs ≡ []
checkAllMuxCycle-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _
    (checkMuxCycleSig-complete (messageNameStr msg) (DBCMessage.signals msg)) _
