{-# OPTIONS --safe --without-K #-}

-- Composition layer: connects errorIssues to per-check proofs.
--
-- Provides:
-- 1. Core errorIssues distributivity lemmas
-- 2. All-error-severity proofs for each of the 9 error checks
-- Used by Theorem.agda to derive top-level soundness/completeness.
module Aletheia.DBC.Validity.Composition where
open import Aletheia.DBC.Identifier using (Identifier; nameStr)
open import Aletheia.DBC.Types using (signalNameStr; messageNameStr)

open import Aletheia.DBC.Types using (ValidationIssue; IsError; IsWarning; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using
  ( errorIssues; findSignalPresence; walkMux
  ; checkDuplicateIdPair; checkDuplicateIdAgainstList; checkDuplicateMessageIds
  ; checkDuplicateSignalPair; checkDuplicateSignalAgainstList; checkDuplicateSignalTriangular
  ; checkAllDuplicateSignalNames
  ; checkFactorZeroSig; checkAllFactorZero
  ; checkMuxFoundSig; checkAllMuxFound
  ; checkMuxCycleSig; checkAllMuxCycle
  ; checkSignalExceedsDLC; checkAllSignalExceedsDLC
  ; checkOverlapPair; checkOverlapAgainstList; checkOverlapTriangular
  ; checkAllSignalOverlaps
  ; checkBitLengthZero; checkAllBitLengthZero
  )
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Validity.ListLemmas using (++-≡[]-combine; ++-≡[]-split; All-concatMap)
open import Aletheia.DBC.Properties using (signalPairValid?)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_; concatMap; length) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (_≤?_; _≟_)
open import Data.Integer using (ℤ; +_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.DecRat using (DecRat)
open import Data.Maybe using (just; nothing)
open import Data.Bool using (true; false)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

private
  E : ValidationIssue → Set
  E i = ValidationIssue.severity i ≡ IsError

  W : ValidationIssue → Set
  W i = ValidationIssue.severity i ≡ IsWarning


-- ============================================================================
-- CORE errorIssues LEMMAS
-- ============================================================================

errorIssues-++ : ∀ xs ys →
  errorIssues (xs ++ₗ ys) ≡ errorIssues xs ++ₗ errorIssues ys
errorIssues-++ [] ys = refl
errorIssues-++ (i ∷ rest) ys with ValidationIssue.severity i
... | IsError   = cong (i ∷_) (errorIssues-++ rest ys)
... | IsWarning = errorIssues-++ rest ys

errorIssues-allW : ∀ xs → All W xs → errorIssues xs ≡ []
errorIssues-allW [] _ = refl
errorIssues-allW (i ∷ rest) (p ∷ ps) with ValidationIssue.severity i | p
... | IsWarning | refl = errorIssues-allW rest ps

errorIssues-allE : ∀ xs → All E xs → errorIssues xs ≡ xs
errorIssues-allE [] _ = refl
errorIssues-allE (i ∷ rest) (p ∷ ps) with ValidationIssue.severity i | p
... | IsError | refl = cong (i ∷_) (errorIssues-allE rest ps)

errorIssues-allE-nil : ∀ xs → All E xs → errorIssues xs ≡ [] → xs ≡ []
errorIssues-allE-nil xs ps eq = trans (sym (errorIssues-allE xs ps)) eq

ei-split : ∀ xs ys → errorIssues (xs ++ₗ ys) ≡ [] →
  errorIssues xs ≡ [] × errorIssues ys ≡ []
ei-split xs ys eq = ++-≡[]-split (trans (sym (errorIssues-++ xs ys)) eq)

ei-from-≡[] : ∀ xs → xs ≡ [] → errorIssues xs ≡ []
ei-from-≡[] .[] refl = refl

ei-combine : ∀ xs ys → errorIssues xs ≡ [] → errorIssues ys ≡ [] →
  errorIssues (xs ++ₗ ys) ≡ []
ei-combine xs ys px py = trans (errorIssues-++ xs ys) (++-≡[]-combine px py)

-- ============================================================================
-- PER-ELEMENT allE PROOFS
-- ============================================================================

-- Check 1: DuplicateMessageIds
checkDuplicateIdPair-allE : ∀ m1 m2 → All E (checkDuplicateIdPair m1 m2)
checkDuplicateIdPair-allE m1 m2 with DBCMessage.id m1 ≟-CANId DBCMessage.id m2
... | yes _ = refl ∷ []
... | no  _ = []

-- Check 2: DuplicateSignalNames
checkDuplicateSignalPair-allE : ∀ msgName s1 s2 → All E (checkDuplicateSignalPair msgName s1 s2)
checkDuplicateSignalPair-allE msgName s1 s2 with signalNameStr s1 ≟ₛ signalNameStr s2
... | yes _ = refl ∷ []
... | no  _ = []

-- Check 3: FactorZero
checkFactorZeroSig-allE : ∀ msgName sig → All E (checkFactorZeroSig msgName sig)
checkFactorZeroSig-allE msgName sig
  with DecRat.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)
... | yes _ = refl ∷ []
... | no  _ = []

-- Check 4: MuxFound
checkMuxFoundSig-allE : ∀ msgName sigs sig → All E (checkMuxFoundSig msgName sigs sig)
checkMuxFoundSig-allE msgName sigs sig with DBCSignal.presence sig
... | Always = []
... | When muxName _ with any? (λ s → signalNameStr s ≟ₛ nameStr muxName) sigs
...   | yes _ = []
...   | no  _ = refl ∷ []

-- Check 5: MuxCycle
checkMuxCycleSig-allE : ∀ msgName sigs sig →
  All E (checkMuxCycleSig msgName sigs sig)
checkMuxCycleSig-allE msgName sigs sig
  with walkMux (length sigs) sigs (DBCSignal.presence sig)
... | true  = []
... | false = refl ∷ []

-- Check 8: SignalExceedsDLC
checkSignalExceedsDLC-allE : ∀ msgName dlc sig →
  All E (checkSignalExceedsDLC msgName dlc sig)
checkSignalExceedsDLC-allE msgName dlc sig
  with SignalDef.startBit (DBCSignal.signalDef sig)
     + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8
... | yes _ = []
... | no  _ = refl ∷ []

-- Check 9: SignalOverlap
checkOverlapPair-allE : ∀ msgName n s1 s2 → All E (checkOverlapPair msgName n s1 s2)
checkOverlapPair-allE msgName n s1 s2 with signalPairValid? n s1 s2
... | yes _ = []
... | no  _ = refl ∷ []

-- Check 10: BitLengthZero
checkBitLengthZero-allE : ∀ msgName sig → All E (checkBitLengthZero msgName sig)
checkBitLengthZero-allE msgName sig
  with SignalDef.bitLength (DBCSignal.signalDef sig) ≟ 0
... | yes _ = refl ∷ []
... | no  _ = []

-- ============================================================================
-- LIFTED allE PROOFS
-- ============================================================================

-- Check 1
checkDuplicateIdAgainstList-allE : ∀ m rest → All E (checkDuplicateIdAgainstList m rest)
checkDuplicateIdAgainstList-allE _ [] = []
checkDuplicateIdAgainstList-allE m (other ∷ rest) =
  ++⁺ (checkDuplicateIdPair-allE m other) (checkDuplicateIdAgainstList-allE m rest)

checkDuplicateMessageIds-allE : ∀ msgs → All E (checkDuplicateMessageIds msgs)
checkDuplicateMessageIds-allE [] = []
checkDuplicateMessageIds-allE (m ∷ rest) =
  ++⁺ (checkDuplicateIdAgainstList-allE m rest) (checkDuplicateMessageIds-allE rest)

-- Check 2
checkDuplicateSignalAgainstList-allE : ∀ msgName sig rest →
  All E (checkDuplicateSignalAgainstList msgName sig rest)
checkDuplicateSignalAgainstList-allE _ _ [] = []
checkDuplicateSignalAgainstList-allE msgName sig (other ∷ rest) =
  ++⁺ (checkDuplicateSignalPair-allE msgName sig other)
         (checkDuplicateSignalAgainstList-allE msgName sig rest)

checkDuplicateSignalTriangular-allE : ∀ msgName sigs →
  All E (checkDuplicateSignalTriangular msgName sigs)
checkDuplicateSignalTriangular-allE _ [] = []
checkDuplicateSignalTriangular-allE msgName (sig ∷ rest) =
  ++⁺ (checkDuplicateSignalAgainstList-allE msgName sig rest)
         (checkDuplicateSignalTriangular-allE msgName rest)

checkAllDuplicateSignalNames-allE : ∀ msgs →
  All E (checkAllDuplicateSignalNames msgs)
checkAllDuplicateSignalNames-allE [] = []
checkAllDuplicateSignalNames-allE (msg ∷ rest) =
  ++⁺ (checkDuplicateSignalTriangular-allE (messageNameStr msg) (DBCMessage.signals msg))
         (checkAllDuplicateSignalNames-allE rest)

-- Check 3
checkAllFactorZero-allE : ∀ msgs → All E (checkAllFactorZero msgs)
checkAllFactorZero-allE msgs = All-concatMap (universal (λ msg →
  All-concatMap (universal (checkFactorZeroSig-allE (messageNameStr msg))
                         (DBCMessage.signals msg))) msgs)

-- Check 4
checkAllMuxFound-allE : ∀ msgs → All E (checkAllMuxFound msgs)
checkAllMuxFound-allE msgs = All-concatMap (universal (λ msg →
  All-concatMap (universal (checkMuxFoundSig-allE (messageNameStr msg) (DBCMessage.signals msg))
                         (DBCMessage.signals msg))) msgs)

-- Check 5
checkAllMuxCycle-allE : ∀ msgs → All E (checkAllMuxCycle msgs)
checkAllMuxCycle-allE msgs = All-concatMap (universal (λ msg →
  All-concatMap (universal (checkMuxCycleSig-allE (messageNameStr msg) (DBCMessage.signals msg))
                         (DBCMessage.signals msg))) msgs)

-- Check 8
checkAllSignalExceedsDLC-allE : ∀ msgs → All E (checkAllSignalExceedsDLC msgs)
checkAllSignalExceedsDLC-allE msgs = All-concatMap (universal (λ msg →
  All-concatMap (universal (checkSignalExceedsDLC-allE (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg)))
                         (DBCMessage.signals msg))) msgs)

-- Check 9
checkOverlapAgainstList-allE : ∀ msgName n sig rest →
  All E (checkOverlapAgainstList msgName n sig rest)
checkOverlapAgainstList-allE _ _ _ [] = []
checkOverlapAgainstList-allE msgName n sig (other ∷ rest) =
  ++⁺ (checkOverlapPair-allE msgName n sig other)
         (checkOverlapAgainstList-allE msgName n sig rest)

checkOverlapTriangular-allE : ∀ msgName n sigs →
  All E (checkOverlapTriangular msgName n sigs)
checkOverlapTriangular-allE _ _ [] = []
checkOverlapTriangular-allE msgName n (sig ∷ rest) =
  ++⁺ (checkOverlapAgainstList-allE msgName n sig rest)
         (checkOverlapTriangular-allE msgName n rest)

checkAllSignalOverlaps-allE : ∀ msgs → All E (checkAllSignalOverlaps msgs)
checkAllSignalOverlaps-allE msgs = All-concatMap (universal (λ msg →
  checkOverlapTriangular-allE (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg))
                              (DBCMessage.signals msg)) msgs)

-- Check 10
checkAllBitLengthZero-allE : ∀ msgs → All E (checkAllBitLengthZero msgs)
checkAllBitLengthZero-allE msgs = All-concatMap (universal (λ msg →
  All-concatMap (universal (checkBitLengthZero-allE (messageNameStr msg))
                         (DBCMessage.signals msg))) msgs)

