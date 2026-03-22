{-# OPTIONS --safe --without-K #-}

-- Per-check soundness and completeness for all 9 error-severity checks.
--
-- For each error check: checkE args ≡ [] ↔ condition(args)
-- Proved by case analysis on the Dec used in each check function.
module Aletheia.DBC.Validity.ErrorChecks where

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using (checkBitLengthZero; checkAllBitLengthZero; checkFactorZeroSig; checkAllFactorZero; checkDLCOutOfRange; checkAllDLCOutOfRange; checkSignalExceedsDLC; checkAllSignalExceedsDLC; checkDupIdPair; checkDupIdAgainstList; checkDuplicateMessageIds; checkDupSigPair; checkDupSigAgainstList; checkDupSigTriangular; checkAllDuplicateSignalNames; checkOverlapPair; checkOverlapAgainstList; checkOverlapTriangular; checkAllSignalOverlaps; checkMuxFoundSig; checkAllMuxFound; checkMuxAlwaysPresentSig; checkAllMuxAlwaysPresent; findSignalPresence; _≟-CANId_)
open import Aletheia.DBC.Validity using (NonZeroBitLength; NonZeroFactor; ValidDLC; BitsInFrame; MuxResolvable; MuxIsAlways)
open import Aletheia.DBC.Validity.ListLemmas using (++-≡[]-split; ++-≡[]-combine; All-map; concatMap-≡[]-sound; concatMap-≡[]-complete)
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
open import Data.Maybe using (Maybe; just; nothing)
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
checkBitLengthZero-sound msgName sig eq
  with SignalDef.bitLength (DBCSignal.signalDef sig) ≟ₙ 0
checkBitLengthZero-sound _ _ () | yes _
... | no ¬p = ¬p

checkBitLengthZero-complete : ∀ msgName sig →
  NonZeroBitLength sig → checkBitLengthZero msgName sig ≡ []
checkBitLengthZero-complete msgName sig neq
  with SignalDef.bitLength (DBCSignal.signalDef sig) ≟ₙ 0
... | no  _  = refl
... | yes eq = ⊥-elim (neq eq)

checkAllBitLengthZero-sound : ∀ msgs →
  checkAllBitLengthZero msgs ≡ [] →
  All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs
checkAllBitLengthZero-sound [] _ = []
checkAllBitLengthZero-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in All-map (λ sig → checkBitLengthZero-sound (DBCMessage.name msg) sig)
             (concatMap-≡[]-sound eq₁)
     ∷ checkAllBitLengthZero-sound rest eq₂

checkAllBitLengthZero-complete : ∀ msgs →
  All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs →
  checkAllBitLengthZero msgs ≡ []
checkAllBitLengthZero-complete [] [] = refl
checkAllBitLengthZero-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (concatMap-≡[]-complete
      (All-map (λ sig → checkBitLengthZero-complete (DBCMessage.name msg) sig) pm))
    (checkAllBitLengthZero-complete rest pms)

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig-sound : ∀ msgName sig →
  checkFactorZeroSig msgName sig ≡ [] → NonZeroFactor sig
checkFactorZeroSig-sound msgName sig eq
  with ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)
checkFactorZeroSig-sound _ _ () | yes _
... | no ¬p = ¬p

checkFactorZeroSig-complete : ∀ msgName sig →
  NonZeroFactor sig → checkFactorZeroSig msgName sig ≡ []
checkFactorZeroSig-complete msgName sig neq
  with ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)
... | no  _  = refl
... | yes eq = ⊥-elim (neq eq)

checkAllFactorZero-sound : ∀ msgs →
  checkAllFactorZero msgs ≡ [] →
  All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs
checkAllFactorZero-sound [] _ = []
checkAllFactorZero-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in All-map (λ sig → checkFactorZeroSig-sound (DBCMessage.name msg) sig)
             (concatMap-≡[]-sound eq₁)
     ∷ checkAllFactorZero-sound rest eq₂

checkAllFactorZero-complete : ∀ msgs →
  All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs →
  checkAllFactorZero msgs ≡ []
checkAllFactorZero-complete [] [] = refl
checkAllFactorZero-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (concatMap-≡[]-complete
      (All-map (λ sig → checkFactorZeroSig-complete (DBCMessage.name msg) sig) pm))
    (checkAllFactorZero-complete rest pms)

-- ============================================================================
-- CHECK 12: DLC OUT OF RANGE
-- ============================================================================

checkDLCOutOfRange-sound : ∀ msg →
  checkDLCOutOfRange msg ≡ [] → ValidDLC msg
checkDLCOutOfRange-sound msg eq with DBCMessage.dlc msg ≤? 8
... | yes p = p
checkDLCOutOfRange-sound _ () | no _

checkDLCOutOfRange-complete : ∀ msg →
  ValidDLC msg → checkDLCOutOfRange msg ≡ []
checkDLCOutOfRange-complete msg p with DBCMessage.dlc msg ≤? 8
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

checkAllDLCOutOfRange-sound : ∀ msgs →
  checkAllDLCOutOfRange msgs ≡ [] → All ValidDLC msgs
checkAllDLCOutOfRange-sound msgs eq =
  All-map (λ m → checkDLCOutOfRange-sound m) (concatMap-≡[]-sound eq)

checkAllDLCOutOfRange-complete : ∀ msgs →
  All ValidDLC msgs → checkAllDLCOutOfRange msgs ≡ []
checkAllDLCOutOfRange-complete msgs pf =
  concatMap-≡[]-complete (All-map (λ m → checkDLCOutOfRange-complete m) pf)

-- ============================================================================
-- CHECK 8: SIGNAL EXCEEDS DLC
-- ============================================================================

checkSignalExceedsDLC-sound : ∀ msgName dlc sig →
  checkSignalExceedsDLC msgName dlc sig ≡ [] →
  BitsInFrame dlc sig
checkSignalExceedsDLC-sound msgName dlc sig eq
  with SignalDef.startBit (DBCSignal.signalDef sig)
     + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8
... | yes p = p
checkSignalExceedsDLC-sound _ _ _ () | no _

checkSignalExceedsDLC-complete : ∀ msgName dlc sig →
  BitsInFrame dlc sig →
  checkSignalExceedsDLC msgName dlc sig ≡ []
checkSignalExceedsDLC-complete msgName dlc sig p
  with SignalDef.startBit (DBCSignal.signalDef sig)
     + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

checkAllSignalExceedsDLC-sound : ∀ msgs →
  checkAllSignalExceedsDLC msgs ≡ [] →
  All (λ m → All (BitsInFrame (DBCMessage.dlc m)) (DBCMessage.signals m)) msgs
checkAllSignalExceedsDLC-sound [] _ = []
checkAllSignalExceedsDLC-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in All-map (λ sig → checkSignalExceedsDLC-sound
                         (DBCMessage.name msg) (DBCMessage.dlc msg) sig)
             (concatMap-≡[]-sound eq₁)
     ∷ checkAllSignalExceedsDLC-sound rest eq₂

checkAllSignalExceedsDLC-complete : ∀ msgs →
  All (λ m → All (BitsInFrame (DBCMessage.dlc m)) (DBCMessage.signals m)) msgs →
  checkAllSignalExceedsDLC msgs ≡ []
checkAllSignalExceedsDLC-complete [] [] = refl
checkAllSignalExceedsDLC-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (concatMap-≡[]-complete
      (All-map (λ sig → checkSignalExceedsDLC-complete
                           (DBCMessage.name msg) (DBCMessage.dlc msg) sig) pm))
    (checkAllSignalExceedsDLC-complete rest pms)

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs (triangular)
-- ============================================================================

checkDupIdPair-sound : ∀ m1 m2 →
  checkDupIdPair m1 m2 ≡ [] → DBCMessage.id m1 ≢ DBCMessage.id m2
checkDupIdPair-sound m1 m2 eq with DBCMessage.id m1 ≟-CANId DBCMessage.id m2
checkDupIdPair-sound _ _ () | yes _
... | no ¬p = ¬p

checkDupIdPair-complete : ∀ m1 m2 →
  DBCMessage.id m1 ≢ DBCMessage.id m2 → checkDupIdPair m1 m2 ≡ []
checkDupIdPair-complete m1 m2 neq with DBCMessage.id m1 ≟-CANId DBCMessage.id m2
... | no  _  = refl
... | yes eq = ⊥-elim (neq eq)

checkDupIdAgainstList-sound : ∀ m rest →
  checkDupIdAgainstList m rest ≡ [] →
  All (λ other → DBCMessage.id m ≢ DBCMessage.id other) rest
checkDupIdAgainstList-sound _ [] _ = []
checkDupIdAgainstList-sound m (other ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkDupIdPair-sound m other eq₁ ∷ checkDupIdAgainstList-sound m rest eq₂

checkDupIdAgainstList-complete : ∀ m rest →
  All (λ other → DBCMessage.id m ≢ DBCMessage.id other) rest →
  checkDupIdAgainstList m rest ≡ []
checkDupIdAgainstList-complete _ [] [] = refl
checkDupIdAgainstList-complete m (other ∷ rest) (p ∷ ps) =
  ++-≡[]-combine (checkDupIdPair-complete m other p)
                 (checkDupIdAgainstList-complete m rest ps)

checkDuplicateMessageIds-sound : ∀ msgs →
  checkDuplicateMessageIds msgs ≡ [] →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
checkDuplicateMessageIds-sound [] _ = []
checkDuplicateMessageIds-sound (m ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkDupIdAgainstList-sound m rest eq₁ ∷
     checkDuplicateMessageIds-sound rest eq₂

checkDuplicateMessageIds-complete : ∀ msgs →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs →
  checkDuplicateMessageIds msgs ≡ []
checkDuplicateMessageIds-complete [] [] = refl
checkDuplicateMessageIds-complete (m ∷ rest) (pm ∷ prest) =
  ++-≡[]-combine (checkDupIdAgainstList-complete m rest pm)
                 (checkDuplicateMessageIds-complete rest prest)

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (nested triangular)
-- ============================================================================

checkDupSigPair-sound : ∀ msgName s1 s2 →
  checkDupSigPair msgName s1 s2 ≡ [] → DBCSignal.name s1 ≢ DBCSignal.name s2
checkDupSigPair-sound msgName s1 s2 eq with DBCSignal.name s1 ≟ DBCSignal.name s2
checkDupSigPair-sound _ _ _ () | yes _
... | no ¬p = ¬p

checkDupSigPair-complete : ∀ msgName s1 s2 →
  DBCSignal.name s1 ≢ DBCSignal.name s2 → checkDupSigPair msgName s1 s2 ≡ []
checkDupSigPair-complete msgName s1 s2 neq with DBCSignal.name s1 ≟ DBCSignal.name s2
... | no  _  = refl
... | yes eq = ⊥-elim (neq eq)

checkDupSigAgainstList-sound : ∀ msgName sig rest →
  checkDupSigAgainstList msgName sig rest ≡ [] →
  All (λ other → DBCSignal.name sig ≢ DBCSignal.name other) rest
checkDupSigAgainstList-sound _ _ [] _ = []
checkDupSigAgainstList-sound msgName sig (other ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkDupSigPair-sound msgName sig other eq₁ ∷
     checkDupSigAgainstList-sound msgName sig rest eq₂

checkDupSigAgainstList-complete : ∀ msgName sig rest →
  All (λ other → DBCSignal.name sig ≢ DBCSignal.name other) rest →
  checkDupSigAgainstList msgName sig rest ≡ []
checkDupSigAgainstList-complete _ _ [] [] = refl
checkDupSigAgainstList-complete msgName sig (other ∷ rest) (p ∷ ps) =
  ++-≡[]-combine (checkDupSigPair-complete msgName sig other p)
                 (checkDupSigAgainstList-complete msgName sig rest ps)

-- Now using the exposed top-level checkDupSigTriangular
checkDupSigTriangular-sound : ∀ msgName sigs →
  checkDupSigTriangular msgName sigs ≡ [] →
  AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂) sigs
checkDupSigTriangular-sound _ [] _ = []
checkDupSigTriangular-sound msgName (sig ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkDupSigAgainstList-sound msgName sig rest eq₁ ∷
     checkDupSigTriangular-sound msgName rest eq₂

checkDupSigTriangular-complete : ∀ msgName sigs →
  AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂) sigs →
  checkDupSigTriangular msgName sigs ≡ []
checkDupSigTriangular-complete _ [] [] = refl
checkDupSigTriangular-complete msgName (sig ∷ rest) (p ∷ ps) =
  ++-≡[]-combine (checkDupSigAgainstList-complete msgName sig rest p)
                 (checkDupSigTriangular-complete msgName rest ps)

checkAllDuplicateSignalNames-sound : ∀ msgs →
  checkAllDuplicateSignalNames msgs ≡ [] →
  All (λ m → AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂)
                       (DBCMessage.signals m)) msgs
checkAllDuplicateSignalNames-sound [] _ = []
checkAllDuplicateSignalNames-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkDupSigTriangular-sound (DBCMessage.name msg) (DBCMessage.signals msg) eq₁ ∷
     checkAllDuplicateSignalNames-sound rest eq₂

checkAllDuplicateSignalNames-complete : ∀ msgs →
  All (λ m → AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂)
                       (DBCMessage.signals m)) msgs →
  checkAllDuplicateSignalNames msgs ≡ []
checkAllDuplicateSignalNames-complete [] [] = refl
checkAllDuplicateSignalNames-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (checkDupSigTriangular-complete (DBCMessage.name msg) (DBCMessage.signals msg) pm)
    (checkAllDuplicateSignalNames-complete rest pms)

-- ============================================================================
-- CHECK 9: SIGNAL OVERLAP (nested triangular via signalPairValid?)
-- ============================================================================

checkOverlapPair-sound : ∀ msgName s1 s2 →
  checkOverlapPair msgName s1 s2 ≡ [] → SignalPairValid s1 s2
checkOverlapPair-sound msgName s1 s2 eq with signalPairValid? s1 s2
... | yes p = p
checkOverlapPair-sound _ _ _ () | no _

checkOverlapPair-complete : ∀ msgName s1 s2 →
  SignalPairValid s1 s2 → checkOverlapPair msgName s1 s2 ≡ []
checkOverlapPair-complete msgName s1 s2 p with signalPairValid? s1 s2
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

checkOverlapAgainstList-sound : ∀ msgName sig rest →
  checkOverlapAgainstList msgName sig rest ≡ [] →
  All (SignalPairValid sig) rest
checkOverlapAgainstList-sound _ _ [] _ = []
checkOverlapAgainstList-sound msgName sig (other ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkOverlapPair-sound msgName sig other eq₁ ∷
     checkOverlapAgainstList-sound msgName sig rest eq₂

checkOverlapAgainstList-complete : ∀ msgName sig rest →
  All (SignalPairValid sig) rest →
  checkOverlapAgainstList msgName sig rest ≡ []
checkOverlapAgainstList-complete _ _ [] [] = refl
checkOverlapAgainstList-complete msgName sig (other ∷ rest) (p ∷ ps) =
  ++-≡[]-combine (checkOverlapPair-complete msgName sig other p)
                 (checkOverlapAgainstList-complete msgName sig rest ps)

checkOverlapTriangular-sound : ∀ msgName sigs →
  checkOverlapTriangular msgName sigs ≡ [] →
  AllPairs SignalPairValid sigs
checkOverlapTriangular-sound _ [] _ = []
checkOverlapTriangular-sound msgName (sig ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkOverlapAgainstList-sound msgName sig rest eq₁ ∷
     checkOverlapTriangular-sound msgName rest eq₂

checkOverlapTriangular-complete : ∀ msgName sigs →
  AllPairs SignalPairValid sigs →
  checkOverlapTriangular msgName sigs ≡ []
checkOverlapTriangular-complete _ [] [] = refl
checkOverlapTriangular-complete msgName (sig ∷ rest) (p ∷ ps) =
  ++-≡[]-combine (checkOverlapAgainstList-complete msgName sig rest p)
                 (checkOverlapTriangular-complete msgName rest ps)

checkAllSignalOverlaps-sound : ∀ msgs →
  checkAllSignalOverlaps msgs ≡ [] →
  All (λ m → AllPairs SignalPairValid (DBCMessage.signals m)) msgs
checkAllSignalOverlaps-sound [] _ = []
checkAllSignalOverlaps-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkOverlapTriangular-sound (DBCMessage.name msg) (DBCMessage.signals msg) eq₁ ∷
     checkAllSignalOverlaps-sound rest eq₂

checkAllSignalOverlaps-complete : ∀ msgs →
  All (λ m → AllPairs SignalPairValid (DBCMessage.signals m)) msgs →
  checkAllSignalOverlaps msgs ≡ []
checkAllSignalOverlaps-complete [] [] = refl
checkAllSignalOverlaps-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (checkOverlapTriangular-complete (DBCMessage.name msg) (DBCMessage.signals msg) pm)
    (checkAllSignalOverlaps-complete rest pms)

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
checkAllMuxFound-sound [] _ = []
checkAllMuxFound-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in All-map (λ sig → checkMuxFoundSig-sound
                         (DBCMessage.name msg) (DBCMessage.signals msg) sig)
             (concatMap-≡[]-sound eq₁)
     ∷ checkAllMuxFound-sound rest eq₂

checkAllMuxFound-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxFound msgs ≡ []
checkAllMuxFound-complete [] [] = refl
checkAllMuxFound-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (concatMap-≡[]-complete
      (All-map (λ sig → checkMuxFoundSig-complete
                           (DBCMessage.name msg) (DBCMessage.signals msg) sig) pm))
    (checkAllMuxFound-complete rest pms)

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
checkAllMuxAlwaysPresent-sound [] _ = []
checkAllMuxAlwaysPresent-sound (msg ∷ rest) eq =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in All-map (λ sig → checkMuxAlwaysPresentSig-sound
                         (DBCMessage.name msg) (DBCMessage.signals msg) sig)
             (concatMap-≡[]-sound eq₁)
     ∷ checkAllMuxAlwaysPresent-sound rest eq₂

checkAllMuxAlwaysPresent-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxIsAlways (DBCMessage.signals m)
                                        (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxAlwaysPresent msgs ≡ []
checkAllMuxAlwaysPresent-complete [] [] = refl
checkAllMuxAlwaysPresent-complete (msg ∷ rest) (pm ∷ pms) =
  ++-≡[]-combine
    (concatMap-≡[]-complete
      (All-map (λ sig → checkMuxAlwaysPresentSig-complete
                           (DBCMessage.name msg) (DBCMessage.signals msg) sig) pm))
    (checkAllMuxAlwaysPresent-complete rest pms)
