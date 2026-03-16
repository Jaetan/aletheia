{-# OPTIONS --safe --without-K #-}

-- All 7 warning checks emit only IsWarning severity issues.
--
-- Purpose: Prove that warning checks never produce IsError issues,
-- so errorIssues filters them all out.
module Aletheia.DBC.Validity.WarningChecks where

open import Aletheia.DBC.Types
open import Aletheia.DBC.Validator
open import Data.List using (List; []; _∷_; map; filter; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≤?_; _<?_)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ)

private
  -- Severity predicate shorthand
  W : ValidationIssue → Set
  W i = ValidationIssue.severity i ≡ IsWarning

  -- All-append for warnings
  All-++ : ∀ {xs ys : List ValidationIssue} → All W xs → All W ys → All W (xs ++ₗ ys)
  All-++ [] pys = pys
  All-++ (px ∷ pxs) pys = px ∷ All-++ pxs pys

  -- concatMap preserves All W
  All-concatMap : ∀ {A : Set} {f : A → List ValidationIssue} {xs : List A} →
    All (λ x → All W (f x)) xs → All W (concatMap f xs)
  All-concatMap [] = []
  All-concatMap (p ∷ ps) = All-++ p (All-concatMap ps)

-- ============================================================================
-- CHECK 6: GLOBAL NAME COLLISION
-- ============================================================================

checkGlobalNamePair-allW : ∀ m1 m2 → All W (checkGlobalNamePair m1 m2)
checkGlobalNamePair-allW m1 m2 = go (messageSignalNames m1)
  where
    names2 = messageSignalNames m2
    go : ∀ ns → All W (map (λ n → mkIssue IsWarning GlobalNameCollision
            ("Signal '" ++ₛ n ++ₛ "' appears in both message '"
             ++ₛ DBCMessage.name m1 ++ₛ "' and '"
             ++ₛ DBCMessage.name m2 ++ₛ "'")) (filter (_∈? names2) ns))
    go [] = []
    go (n ∷ ns) with n ∈? names2
    ... | yes _ = refl ∷ go ns
    ... | no  _ = go ns

checkAllGlobalNameCollisions-allW : ∀ msgs → All W (checkAllGlobalNameCollisions msgs)
checkAllGlobalNameCollisions-allW [] = []
checkAllGlobalNameCollisions-allW (m ∷ rest) =
  All-++ (go m rest) (checkAllGlobalNameCollisions-allW rest)
  where
    go : ∀ m rest → All W (checkGlobalNameAgainstList m rest)
    go _ [] = []
    go m (other ∷ rest) = All-++ (checkGlobalNamePair-allW m other) (go m rest)

-- ============================================================================
-- CHECK 7: MIN EXCEEDS MAX
-- ============================================================================

checkMinMaxSig-allW : ∀ msgName sig → All W (checkMinMaxSig msgName sig)
checkMinMaxSig-allW msgName sig
  with SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵣ
       SignalDef.maximum (DBCSignal.signalDef sig)
... | yes _ = []
... | no  _ = refl ∷ []

checkAllMinMax-allW : ∀ msgs → All W (checkAllMinMax msgs)
checkAllMinMax-allW [] = []
checkAllMinMax-allW (msg ∷ rest) =
  All-++ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllMinMax-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkMinMaxSig (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkMinMaxSig-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME
-- ============================================================================

checkDupNamePair-allW : ∀ m1 m2 → All W (checkDupNamePair m1 m2)
checkDupNamePair-allW m1 m2 with DBCMessage.name m1 ≟ DBCMessage.name m2
... | yes _ = refl ∷ []
... | no  _ = []

checkDuplicateMessageNames-allW : ∀ msgs → All W (checkDuplicateMessageNames msgs)
checkDuplicateMessageNames-allW [] = []
checkDuplicateMessageNames-allW (m ∷ rest) =
  All-++ (go m rest) (checkDuplicateMessageNames-allW rest)
  where
    go : ∀ m rest → All W (checkDupNameAgainstList m rest)
    go _ [] = []
    go m (other ∷ rest) = All-++ (checkDupNamePair-allW m other) (go m rest)

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE (uses exposed checkRangeLow/checkRangeHigh)
-- ============================================================================

checkRangeLow-allW : ∀ msgName sigName physMin declMin →
  All W (checkRangeLow msgName sigName physMin declMin)
checkRangeLow-allW msgName sigName physMin declMin with declMin ≤?ᵣ physMin
... | yes _ = []
... | no  _ = refl ∷ []

checkRangeHigh-allW : ∀ msgName sigName physMax declMax →
  All W (checkRangeHigh msgName sigName physMax declMax)
checkRangeHigh-allW msgName sigName physMax declMax with physMax ≤?ᵣ declMax
... | yes _ = []
... | no  _ = refl ∷ []

-- checkRangeBounds is now top-level, so we can prove it directly.
checkRangeBounds-allW : ∀ msgName sigName factor physA physB declMin declMax →
  All W (checkRangeBounds msgName sigName factor physA physB declMin declMax)
checkRangeBounds-allW msgName sigName factor physA physB declMin declMax
  with isNegativeℚ factor
... | false = All-++ (checkRangeLow-allW msgName sigName physA declMin)
                     (checkRangeHigh-allW msgName sigName physB declMax)
... | true  = All-++ (checkRangeLow-allW msgName sigName physB declMin)
                     (checkRangeHigh-allW msgName sigName physA declMax)

-- Check 13: match on isSigned to reduce computeRange, then use checkRangeBounds-allW.
checkOffsetScaleRange-allW : ∀ msgName sig → All W (checkOffsetScaleRange msgName sig)
checkOffsetScaleRange-allW msgName sig
  with SignalDef.isSigned (DBCSignal.signalDef sig)
... | true  = checkRangeBounds-allW msgName (DBCSignal.name sig)
                (SignalDef.factor (DBCSignal.signalDef sig)) _ _ _ _
... | false = checkRangeBounds-allW msgName (DBCSignal.name sig)
                (SignalDef.factor (DBCSignal.signalDef sig)) _ _ _ _

checkAllOffsetScaleRange-allW : ∀ msgs → All W (checkAllOffsetScaleRange msgs)
checkAllOffsetScaleRange-allW [] = []
checkAllOffsetScaleRange-allW (msg ∷ rest) =
  All-++ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllOffsetScaleRange-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkOffsetScaleRange (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkOffsetScaleRange-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 14: EMPTY MESSAGE
-- ============================================================================

checkEmptyMessage-allW : ∀ msg → All W (checkEmptyMessage msg)
checkEmptyMessage-allW msg with DBCMessage.signals msg
... | []    = refl ∷ []
... | _ ∷ _ = []

checkAllEmptyMessage-allW : ∀ msgs → All W (checkAllEmptyMessage msgs)
checkAllEmptyMessage-allW msgs = All-concatMap (go msgs)
  where
    go : ∀ ms → All (λ m → All W (checkEmptyMessage m)) ms
    go [] = []
    go (m ∷ ms) = checkEmptyMessage-allW m ∷ go ms

-- ============================================================================
-- CHECK 15: START BIT OUT OF RANGE
-- ============================================================================

checkStartBitOutOfRange-allW : ∀ msgName sig → All W (checkStartBitOutOfRange msgName sig)
checkStartBitOutOfRange-allW msgName sig
  with SignalDef.startBit (DBCSignal.signalDef sig) <? 64
... | yes _ = []
... | no  _ = refl ∷ []

checkAllStartBitOutOfRange-allW : ∀ msgs → All W (checkAllStartBitOutOfRange msgs)
checkAllStartBitOutOfRange-allW [] = []
checkAllStartBitOutOfRange-allW (msg ∷ rest) =
  All-++ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllStartBitOutOfRange-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkStartBitOutOfRange (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkStartBitOutOfRange-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 16: BIT LENGTH EXCESSIVE
-- ============================================================================

checkBitLengthExcessive-allW : ∀ msgName sig → All W (checkBitLengthExcessive msgName sig)
checkBitLengthExcessive-allW msgName sig
  with SignalDef.bitLength (DBCSignal.signalDef sig) ≤? 64
... | yes _ = []
... | no  _ = refl ∷ []

checkAllBitLengthExcessive-allW : ∀ msgs → All W (checkAllBitLengthExcessive msgs)
checkAllBitLengthExcessive-allW [] = []
checkAllBitLengthExcessive-allW (msg ∷ rest) =
  All-++ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllBitLengthExcessive-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkBitLengthExcessive (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkBitLengthExcessive-allW (DBCMessage.name msg) sig ∷ go sigs
