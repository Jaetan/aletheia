{-# OPTIONS --safe --without-K #-}

-- Warning check severity proofs and soundness/completeness.
--
-- Purpose: (1) Prove all 8 warning checks emit only IsWarning severity.
-- (2) Prove soundness (check ≡ [] → predicate) and completeness
-- (predicate → check ≡ []) for each warning check, relating the
-- validator functions to the predicates in Validity.agda.
module Aletheia.DBC.Validity.WarningChecks where

open import Aletheia.DBC.Types using (ValidationIssue; IsWarning; DBCMessage; DBCSignal; mkIssue; GlobalNameCollision; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using
  ( checkGlobalNamePair; checkGlobalNameAgainstList
  ; checkAllGlobalNameCollisions; messageSignalNames
  ; checkMinMaxSig; checkAllMinMax
  ; checkDupNamePair; checkDupNameAgainstList
  ; checkDuplicateMessageNames
  ; checkRangeLow; checkRangeHigh; checkRangeBounds; isNegativeℚ
  ; checkOffsetScaleRange; checkAllOffsetScaleRange
  ; checkEmptyMessage; checkAllEmptyMessage
  ; checkStartBitOutOfRange; checkAllStartBitOutOfRange
  ; checkBitLengthExcessive; checkAllBitLengthExcessive
  ; checkMuxScaling; checkMuxScalingSig; checkAllMuxScaling
  )
open import Aletheia.CAN.DBCHelpers using (findSignalInList)
open import Aletheia.DBC.Validity using
  ( MinLeqMax; DistinctMessageNames; NonEmptySignals
  ; StartBitInRange; BitLengthInRange; DisjointSignalNames
  ; RangeLowOK; RangeHighOK; RangeBoundsOK
  ; MuxScalingOK; MuxUnitScaling
  )
open import Aletheia.DBC.Validity.ListLemmas using
  (All-concatMap; ++-≡[]-split; ++-≡[]-combine)
open import Aletheia.DBC.Validity.Combinators using
  ( liftConcatMap-sound; liftConcatMap-complete
  ; requireDec-sound; requireDec-complete
  ; rejectDec-sound; rejectDec-complete
  ; liftTriangular-sound; liftTriangular-complete )
open import Data.List using (List; []; _∷_; map; filter; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using (_≟_)
open import Data.Nat.Properties using (_≤?_; _<?_)
open import Data.Rational using (ℚ)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_; _≟_ to _≟ᵣ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.Protocol.JSON using (ℕtoℚ)
open import Aletheia.Prelude using (max-physical-bits)

private
  -- Severity predicate shorthand
  W : ValidationIssue → Set
  W i = ValidationIssue.severity i ≡ IsWarning

-- ============================================================================
-- CHECK 6: GLOBAL NAME COLLISION — Severity
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
  ++⁺ (go m rest) (checkAllGlobalNameCollisions-allW rest)
  where
    go : ∀ m rest → All W (checkGlobalNameAgainstList m rest)
    go _ [] = []
    go m (other ∷ rest) = ++⁺ (checkGlobalNamePair-allW m other) (go m rest)

-- ============================================================================
-- CHECK 6: GLOBAL NAME COLLISION — Soundness/Completeness
-- ============================================================================

checkGlobalNamePair-sound : ∀ m1 m2 →
  checkGlobalNamePair m1 m2 ≡ [] →
  DisjointSignalNames (messageSignalNames m1) (messageSignalNames m2)
checkGlobalNamePair-sound m1 m2 eq = go (messageSignalNames m1) eq
  where
    names2 = messageSignalNames m2
    go : ∀ ns → map (λ n → mkIssue IsWarning GlobalNameCollision
            ("Signal '" ++ₛ n ++ₛ "' appears in both message '"
             ++ₛ DBCMessage.name m1 ++ₛ "' and '"
             ++ₛ DBCMessage.name m2 ++ₛ "'")) (filter (_∈? names2) ns) ≡ []
         → All (λ n → ¬ Any (n ≡_) names2) ns
    go [] _ = []
    go (n ∷ ns) eq with n ∈? names2
    go (n ∷ ns) () | yes _
    go (n ∷ ns) eq | no ¬n∈ = ¬n∈ ∷ go ns eq

checkGlobalNamePair-complete : ∀ m1 m2 →
  DisjointSignalNames (messageSignalNames m1) (messageSignalNames m2) →
  checkGlobalNamePair m1 m2 ≡ []
checkGlobalNamePair-complete m1 m2 disj = go (messageSignalNames m1) disj
  where
    names2 = messageSignalNames m2
    go : ∀ ns → All (λ n → ¬ Any (n ≡_) names2) ns
         → map (λ n → mkIssue IsWarning GlobalNameCollision
                  ("Signal '" ++ₛ n ++ₛ "' appears in both message '"
                   ++ₛ DBCMessage.name m1 ++ₛ "' and '"
                   ++ₛ DBCMessage.name m2 ++ₛ "'")) (filter (_∈? names2) ns) ≡ []
    go [] [] = refl
    go (n ∷ ns) (¬n∈ ∷ rest) with n ∈? names2
    ... | yes n∈ = ⊥-elim (¬n∈ n∈)
    ... | no  _  = go ns rest

checkGlobalNameAgainstList-sound : ∀ m rest →
  checkGlobalNameAgainstList m rest ≡ [] →
  All (λ other → DisjointSignalNames (messageSignalNames m) (messageSignalNames other)) rest
checkGlobalNameAgainstList-sound m =
  liftConcatMap-sound (checkGlobalNamePair m) (checkGlobalNamePair-sound m)

checkGlobalNameAgainstList-complete : ∀ m rest →
  All (λ other → DisjointSignalNames (messageSignalNames m) (messageSignalNames other)) rest →
  checkGlobalNameAgainstList m rest ≡ []
checkGlobalNameAgainstList-complete m =
  liftConcatMap-complete (checkGlobalNamePair m) (checkGlobalNamePair-complete m)

checkAllGlobalNameCollisions-sound : ∀ msgs →
  checkAllGlobalNameCollisions msgs ≡ [] →
  AllPairs (λ m1 m2 → DisjointSignalNames (messageSignalNames m1) (messageSignalNames m2)) msgs
checkAllGlobalNameCollisions-sound =
  liftTriangular-sound checkGlobalNamePair checkGlobalNamePair-sound

checkAllGlobalNameCollisions-complete : ∀ msgs →
  AllPairs (λ m1 m2 → DisjointSignalNames (messageSignalNames m1) (messageSignalNames m2)) msgs →
  checkAllGlobalNameCollisions msgs ≡ []
checkAllGlobalNameCollisions-complete =
  liftTriangular-complete checkGlobalNamePair checkGlobalNamePair-complete

-- ============================================================================
-- CHECK 7: MIN EXCEEDS MAX — Severity
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
  ++⁺ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllMinMax-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkMinMaxSig (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkMinMaxSig-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 7: MIN EXCEEDS MAX — Soundness/Completeness
-- ============================================================================

checkMinMaxSig-sound : ∀ msgName sig →
  checkMinMaxSig msgName sig ≡ [] → MinLeqMax sig
checkMinMaxSig-sound _ sig =
  requireDec-sound (SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵣ
                    SignalDef.maximum (DBCSignal.signalDef sig)) _

checkMinMaxSig-complete : ∀ msgName sig →
  MinLeqMax sig → checkMinMaxSig msgName sig ≡ []
checkMinMaxSig-complete _ sig =
  requireDec-complete (SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵣ
                       SignalDef.maximum (DBCSignal.signalDef sig)) _

checkAllMinMax-sound : ∀ msgs →
  checkAllMinMax msgs ≡ [] →
  All (λ m → All MinLeqMax (DBCMessage.signals m)) msgs
checkAllMinMax-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkMinMaxSig-sound (DBCMessage.name msg)) _

checkAllMinMax-complete : ∀ msgs →
  All (λ m → All MinLeqMax (DBCMessage.signals m)) msgs →
  checkAllMinMax msgs ≡ []
checkAllMinMax-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkMinMaxSig-complete (DBCMessage.name msg)) _

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME — Severity
-- ============================================================================

checkDupNamePair-allW : ∀ m1 m2 → All W (checkDupNamePair m1 m2)
checkDupNamePair-allW m1 m2 with DBCMessage.name m1 ≟ DBCMessage.name m2
... | yes _ = refl ∷ []
... | no  _ = []

checkDuplicateMessageNames-allW : ∀ msgs → All W (checkDuplicateMessageNames msgs)
checkDuplicateMessageNames-allW [] = []
checkDuplicateMessageNames-allW (m ∷ rest) =
  ++⁺ (go m rest) (checkDuplicateMessageNames-allW rest)
  where
    go : ∀ m rest → All W (checkDupNameAgainstList m rest)
    go _ [] = []
    go m (other ∷ rest) = ++⁺ (checkDupNamePair-allW m other) (go m rest)

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME — Soundness/Completeness
-- ============================================================================

checkDupNamePair-sound : ∀ m1 m2 →
  checkDupNamePair m1 m2 ≡ [] → DistinctMessageNames m1 m2
checkDupNamePair-sound m1 m2 =
  rejectDec-sound (DBCMessage.name m1 ≟ DBCMessage.name m2) _

checkDupNamePair-complete : ∀ m1 m2 →
  DistinctMessageNames m1 m2 → checkDupNamePair m1 m2 ≡ []
checkDupNamePair-complete m1 m2 =
  rejectDec-complete (DBCMessage.name m1 ≟ DBCMessage.name m2) _

checkDupNameAgainstList-sound : ∀ m rest →
  checkDupNameAgainstList m rest ≡ [] →
  All (DistinctMessageNames m) rest
checkDupNameAgainstList-sound m =
  liftConcatMap-sound (checkDupNamePair m) (checkDupNamePair-sound m)

checkDupNameAgainstList-complete : ∀ m rest →
  All (DistinctMessageNames m) rest →
  checkDupNameAgainstList m rest ≡ []
checkDupNameAgainstList-complete m =
  liftConcatMap-complete (checkDupNamePair m) (checkDupNamePair-complete m)

checkDuplicateMessageNames-sound : ∀ msgs →
  checkDuplicateMessageNames msgs ≡ [] →
  AllPairs DistinctMessageNames msgs
checkDuplicateMessageNames-sound =
  liftTriangular-sound checkDupNamePair checkDupNamePair-sound

checkDuplicateMessageNames-complete : ∀ msgs →
  AllPairs DistinctMessageNames msgs →
  checkDuplicateMessageNames msgs ≡ []
checkDuplicateMessageNames-complete =
  liftTriangular-complete checkDupNamePair checkDupNamePair-complete

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE — Severity
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

checkRangeBounds-allW : ∀ msgName sigName factor physA physB declMin declMax →
  All W (checkRangeBounds msgName sigName factor physA physB declMin declMax)
checkRangeBounds-allW msgName sigName factor physA physB declMin declMax
  with isNegativeℚ factor
... | false = ++⁺ (checkRangeLow-allW msgName sigName physA declMin)
                     (checkRangeHigh-allW msgName sigName physB declMax)
... | true  = ++⁺ (checkRangeLow-allW msgName sigName physB declMin)
                     (checkRangeHigh-allW msgName sigName physA declMax)

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
  ++⁺ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllOffsetScaleRange-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkOffsetScaleRange (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkOffsetScaleRange-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE — Soundness/Completeness (component level)
-- ============================================================================

checkRangeLow-sound : ∀ msgName sigName physMin declMin →
  checkRangeLow msgName sigName physMin declMin ≡ [] → RangeLowOK physMin declMin
checkRangeLow-sound _ _ physMin declMin =
  requireDec-sound (declMin ≤?ᵣ physMin) _

checkRangeLow-complete : ∀ msgName sigName physMin declMin →
  RangeLowOK physMin declMin → checkRangeLow msgName sigName physMin declMin ≡ []
checkRangeLow-complete _ _ physMin declMin =
  requireDec-complete (declMin ≤?ᵣ physMin) _

checkRangeHigh-sound : ∀ msgName sigName physMax declMax →
  checkRangeHigh msgName sigName physMax declMax ≡ [] → RangeHighOK physMax declMax
checkRangeHigh-sound _ _ physMax declMax =
  requireDec-sound (physMax ≤?ᵣ declMax) _

checkRangeHigh-complete : ∀ msgName sigName physMax declMax →
  RangeHighOK physMax declMax → checkRangeHigh msgName sigName physMax declMax ≡ []
checkRangeHigh-complete _ _ physMax declMax =
  requireDec-complete (physMax ≤?ᵣ declMax) _

checkRangeBounds-sound : ∀ msgName sigName factor physA physB declMin declMax →
  checkRangeBounds msgName sigName factor physA physB declMin declMax ≡ [] →
  RangeBoundsOK (isNegativeℚ factor) physA physB declMin declMax
checkRangeBounds-sound msgName sigName factor physA physB declMin declMax eq
  with isNegativeℚ factor
... | false =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkRangeLow-sound msgName sigName physA declMin eq₁ ,
     checkRangeHigh-sound msgName sigName physB declMax eq₂
... | true  =
  let (eq₁ , eq₂) = ++-≡[]-split eq
  in checkRangeLow-sound msgName sigName physB declMin eq₁ ,
     checkRangeHigh-sound msgName sigName physA declMax eq₂

checkRangeBounds-complete : ∀ msgName sigName factor physA physB declMin declMax →
  RangeBoundsOK (isNegativeℚ factor) physA physB declMin declMax →
  checkRangeBounds msgName sigName factor physA physB declMin declMax ≡ []
checkRangeBounds-complete msgName sigName factor physA physB declMin declMax p
  with isNegativeℚ factor
... | false =
  let (lo , hi) = p
  in ++-≡[]-combine (checkRangeLow-complete msgName sigName physA declMin lo)
                    (checkRangeHigh-complete msgName sigName physB declMax hi)
... | true  =
  let (lo , hi) = p
  in ++-≡[]-combine (checkRangeLow-complete msgName sigName physB declMin lo)
                    (checkRangeHigh-complete msgName sigName physA declMax hi)

-- ============================================================================
-- CHECK 14: EMPTY MESSAGE — Severity
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
-- CHECK 14: EMPTY MESSAGE — Soundness/Completeness
-- ============================================================================

checkEmptyMessage-sound : ∀ msg →
  checkEmptyMessage msg ≡ [] → NonEmptySignals msg
checkEmptyMessage-sound msg eq with DBCMessage.signals msg
checkEmptyMessage-sound _ () | []
... | _ ∷ _ = λ ()

checkEmptyMessage-complete : ∀ msg →
  NonEmptySignals msg → checkEmptyMessage msg ≡ []
checkEmptyMessage-complete msg ne with DBCMessage.signals msg
... | []    = ⊥-elim (ne refl)
... | _ ∷ _ = refl

checkAllEmptyMessage-sound : ∀ msgs →
  checkAllEmptyMessage msgs ≡ [] →
  All NonEmptySignals msgs
checkAllEmptyMessage-sound =
  liftConcatMap-sound checkEmptyMessage checkEmptyMessage-sound

checkAllEmptyMessage-complete : ∀ msgs →
  All NonEmptySignals msgs →
  checkAllEmptyMessage msgs ≡ []
checkAllEmptyMessage-complete =
  liftConcatMap-complete checkEmptyMessage checkEmptyMessage-complete

-- ============================================================================
-- CHECK 15: START BIT OUT OF RANGE — Severity
-- ============================================================================

checkStartBitOutOfRange-allW : ∀ msgName sig → All W (checkStartBitOutOfRange msgName sig)
checkStartBitOutOfRange-allW msgName sig
  with SignalDef.startBit (DBCSignal.signalDef sig) <? max-physical-bits
... | yes _ = []
... | no  _ = refl ∷ []

checkAllStartBitOutOfRange-allW : ∀ msgs → All W (checkAllStartBitOutOfRange msgs)
checkAllStartBitOutOfRange-allW [] = []
checkAllStartBitOutOfRange-allW (msg ∷ rest) =
  ++⁺ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllStartBitOutOfRange-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkStartBitOutOfRange (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkStartBitOutOfRange-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 15: START BIT OUT OF RANGE — Soundness/Completeness
-- ============================================================================

checkStartBitOutOfRange-sound : ∀ msgName sig →
  checkStartBitOutOfRange msgName sig ≡ [] → StartBitInRange sig
checkStartBitOutOfRange-sound _ sig =
  requireDec-sound (SignalDef.startBit (DBCSignal.signalDef sig) <? max-physical-bits) _

checkStartBitOutOfRange-complete : ∀ msgName sig →
  StartBitInRange sig → checkStartBitOutOfRange msgName sig ≡ []
checkStartBitOutOfRange-complete _ sig =
  requireDec-complete (SignalDef.startBit (DBCSignal.signalDef sig) <? max-physical-bits) _

checkAllStartBitOutOfRange-sound : ∀ msgs →
  checkAllStartBitOutOfRange msgs ≡ [] →
  All (λ m → All StartBitInRange (DBCMessage.signals m)) msgs
checkAllStartBitOutOfRange-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkStartBitOutOfRange-sound (DBCMessage.name msg)) _

checkAllStartBitOutOfRange-complete : ∀ msgs →
  All (λ m → All StartBitInRange (DBCMessage.signals m)) msgs →
  checkAllStartBitOutOfRange msgs ≡ []
checkAllStartBitOutOfRange-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkStartBitOutOfRange-complete (DBCMessage.name msg)) _

-- ============================================================================
-- CHECK 16: BIT LENGTH EXCESSIVE — Severity
-- ============================================================================

checkBitLengthExcessive-allW : ∀ msgName sig → All W (checkBitLengthExcessive msgName sig)
checkBitLengthExcessive-allW msgName sig
  with SignalDef.bitLength (DBCSignal.signalDef sig) ≤? max-physical-bits
... | yes _ = []
... | no  _ = refl ∷ []

checkAllBitLengthExcessive-allW : ∀ msgs → All W (checkAllBitLengthExcessive msgs)
checkAllBitLengthExcessive-allW [] = []
checkAllBitLengthExcessive-allW (msg ∷ rest) =
  ++⁺ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllBitLengthExcessive-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkBitLengthExcessive (DBCMessage.name msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkBitLengthExcessive-allW (DBCMessage.name msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 16: BIT LENGTH EXCESSIVE — Soundness/Completeness
-- ============================================================================

checkBitLengthExcessive-sound : ∀ msgName sig →
  checkBitLengthExcessive msgName sig ≡ [] → BitLengthInRange sig
checkBitLengthExcessive-sound _ sig =
  requireDec-sound (SignalDef.bitLength (DBCSignal.signalDef sig) ≤? max-physical-bits) _

checkBitLengthExcessive-complete : ∀ msgName sig →
  BitLengthInRange sig → checkBitLengthExcessive msgName sig ≡ []
checkBitLengthExcessive-complete _ sig =
  requireDec-complete (SignalDef.bitLength (DBCSignal.signalDef sig) ≤? max-physical-bits) _

checkAllBitLengthExcessive-sound : ∀ msgs →
  checkAllBitLengthExcessive msgs ≡ [] →
  All (λ m → All BitLengthInRange (DBCMessage.signals m)) msgs
checkAllBitLengthExcessive-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _ (checkBitLengthExcessive-sound (DBCMessage.name msg)) _

checkAllBitLengthExcessive-complete : ∀ msgs →
  All (λ m → All BitLengthInRange (DBCMessage.signals m)) msgs →
  checkAllBitLengthExcessive msgs ≡ []
checkAllBitLengthExcessive-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _ (checkBitLengthExcessive-complete (DBCMessage.name msg)) _

-- ============================================================================
-- CHECK 17: MULTIPLEXOR NON-UNIT SCALING — Severity
-- ============================================================================

checkMuxScaling-allW : ∀ msgName muxName muxSig → All W (checkMuxScaling msgName muxName muxSig)
checkMuxScaling-allW msgName muxName muxSig
  with SignalDef.factor (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 1
     | SignalDef.offset (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 0
... | yes _ | yes _ = []
... | yes _ | no  _ = refl ∷ []
... | no  _ | _     = refl ∷ []

checkMuxScalingSig-allW : ∀ msgName allSigs sig → All W (checkMuxScalingSig msgName allSigs sig)
checkMuxScalingSig-allW msgName allSigs sig with DBCSignal.presence sig
... | Always = []
... | When muxName _ with findSignalInList muxName allSigs
...   | nothing     = []
...   | just muxSig = checkMuxScaling-allW msgName muxName muxSig

checkAllMuxScaling-allW : ∀ msgs → All W (checkAllMuxScaling msgs)
checkAllMuxScaling-allW [] = []
checkAllMuxScaling-allW (msg ∷ rest) =
  ++⁺ (All-concatMap (go (DBCMessage.signals msg)))
         (checkAllMuxScaling-allW rest)
  where
    go : ∀ sigs → All (λ sig → All W (checkMuxScalingSig (DBCMessage.name msg)
                                        (DBCMessage.signals msg) sig)) sigs
    go [] = []
    go (sig ∷ sigs) = checkMuxScalingSig-allW (DBCMessage.name msg)
                        (DBCMessage.signals msg) sig ∷ go sigs

-- ============================================================================
-- CHECK 17: MULTIPLEXOR NON-UNIT SCALING — Soundness/Completeness
-- ============================================================================

-- Core: checkMuxScaling ≡ [] ↔ MuxScalingOK (just muxSig)
checkMuxScaling-sound : ∀ msgName muxName muxSig →
  checkMuxScaling msgName muxName muxSig ≡ [] → MuxScalingOK (just muxSig)
checkMuxScaling-sound msgName muxName muxSig eq
  with SignalDef.factor (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 1
     | SignalDef.offset (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 0
... | yes p₁ | yes p₂ = p₁ , p₂
checkMuxScaling-sound _ _ _ () | yes _ | no _
checkMuxScaling-sound _ _ _ () | no _  | _

checkMuxScaling-complete : ∀ msgName muxName muxSig →
  MuxScalingOK (just muxSig) → checkMuxScaling msgName muxName muxSig ≡ []
checkMuxScaling-complete msgName muxName muxSig (p₁ , p₂)
  with SignalDef.factor (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 1
     | SignalDef.offset (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 0
... | yes _  | yes _  = refl
... | yes _  | no ¬p₂ = ⊥-elim (¬p₂ p₂)
... | no ¬p₁ | _      = ⊥-elim (¬p₁ p₁)

-- Per-signal: checkMuxScalingSig ≡ [] ↔ MuxUnitScaling
checkMuxScalingSig-sound : ∀ msgName allSigs sig →
  checkMuxScalingSig msgName allSigs sig ≡ [] →
  MuxUnitScaling allSigs (DBCSignal.presence sig)
checkMuxScalingSig-sound msgName allSigs sig eq with DBCSignal.presence sig
... | Always = tt
... | When muxName _ with findSignalInList muxName allSigs
...   | nothing     = tt
...   | just muxSig = checkMuxScaling-sound msgName muxName muxSig eq

checkMuxScalingSig-complete : ∀ msgName allSigs sig →
  MuxUnitScaling allSigs (DBCSignal.presence sig) →
  checkMuxScalingSig msgName allSigs sig ≡ []
checkMuxScalingSig-complete msgName allSigs sig p with DBCSignal.presence sig
... | Always = refl
... | When muxName _ with findSignalInList muxName allSigs
...   | nothing     = refl
...   | just muxSig = checkMuxScaling-complete msgName muxName muxSig p

-- Lifted: checkAllMuxScaling ≡ [] ↔ All (All MuxUnitScaling) msgs
checkAllMuxScaling-sound : ∀ msgs →
  checkAllMuxScaling msgs ≡ [] →
  All (λ m → All (λ sig → MuxUnitScaling (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs
checkAllMuxScaling-sound = liftConcatMap-sound _ λ msg →
  liftConcatMap-sound _
    (checkMuxScalingSig-sound (DBCMessage.name msg) (DBCMessage.signals msg)) _

checkAllMuxScaling-complete : ∀ msgs →
  All (λ m → All (λ sig → MuxUnitScaling (DBCMessage.signals m)
                                          (DBCSignal.presence sig))
                  (DBCMessage.signals m)) msgs →
  checkAllMuxScaling msgs ≡ []
checkAllMuxScaling-complete = liftConcatMap-complete _ λ msg →
  liftConcatMap-complete _
    (checkMuxScalingSig-complete (DBCMessage.name msg) (DBCMessage.signals msg)) _
