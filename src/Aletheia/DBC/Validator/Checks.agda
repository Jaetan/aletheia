{-# OPTIONS --safe --without-K #-}

-- DBC structural validator: individual check functions.
--
-- Purpose: Per-check functions for all 17 DBC validity conditions.
-- Each check returns [] (no issues) or a singleton list (issue found).
-- checkAll* variants lift per-element checks to full message lists via concatMap.
-- Role: Used by Validity proofs (ErrorChecks, WarningChecks) and composed
--   into validateDBCFull in the parent Validator module.
module Aletheia.DBC.Validator.Checks where

open import Aletheia.DBC.Types using
  ( DBCMessage; DBCSignal; SignalPresence; Always; When
  ; ValidationIssue; mkIssue; IsError; IsWarning
  ; DuplicateMessageId; DuplicateSignalName; FactorZero
  ; MultiplexorNotFound; MultiplexorNotAlwaysPresent
  ; GlobalNameCollision; MinExceedsMax; SignalExceedsDLC
  ; SignalOverlap; BitLengthZero; DuplicateMessageName
  ; OffsetScaleRange; EmptyMessage
  ; StartBitOutOfRange; BitLengthExcessive
  ; MultiplexorNonUnitScaling
  )
open import Aletheia.Prelude using (max-physical-bits)
open import Aletheia.DBC.Properties using (signalPairValid?)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_; findSignalInList)
open import Aletheia.CAN.DLC using (DLC; dlcBytes; dlcToBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_; map; filter; concatMap)
  renaming (_++_ to _++ₗ_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _∸_; pred)
open import Data.Nat.Properties using (_≤?_; _<?_) renaming (_≟_ to _≟ₙ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)
open import Aletheia.Protocol.JSON using (ℕtoℚ)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_; _≟_ to _≟ᵣ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Relation.Nullary using (yes; no)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Aletheia.DBC.Validity.Combinators using
  (requireDec; rejectDec; checkAgainst; triangularCheck)

-- ============================================================================
-- DECIDABLE HELPERS
-- ============================================================================

findSignalPresence : String → List DBCSignal → Maybe SignalPresence
findSignalPresence name [] = nothing
findSignalPresence name (sig ∷ rest) with DBCSignal.name sig ≟ name
... | yes _ = just (DBCSignal.presence sig)
... | no  _ = findSignalPresence name rest

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs
-- ============================================================================

checkDupIdPair : DBCMessage → DBCMessage → List ValidationIssue
checkDupIdPair m1 m2 =
  rejectDec (DBCMessage.id m1 ≟-CANId DBCMessage.id m2)
            (mkIssue IsError DuplicateMessageId
              ("Messages '" ++ₛ DBCMessage.name m1 ++ₛ "' and '"
               ++ₛ DBCMessage.name m2 ++ₛ "' share the same CAN ID"))

checkDupIdAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkDupIdAgainstList = checkAgainst checkDupIdPair

checkDuplicateMessageIds : List DBCMessage → List ValidationIssue
checkDuplicateMessageIds = triangularCheck checkDupIdPair

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (within a message)
-- ============================================================================

checkDupSigPair : String → DBCSignal → DBCSignal → List ValidationIssue
checkDupSigPair msgName s1 s2 =
  rejectDec (DBCSignal.name s1 ≟ DBCSignal.name s2)
            (mkIssue IsError DuplicateSignalName
              ("Message '" ++ₛ msgName ++ₛ "': duplicate signal name '"
               ++ₛ DBCSignal.name s1 ++ₛ "'"))

checkDupSigAgainstList : String → DBCSignal → List DBCSignal → List ValidationIssue
checkDupSigAgainstList msgName = checkAgainst (checkDupSigPair msgName)

checkDupSigTriangular : String → List DBCSignal → List ValidationIssue
checkDupSigTriangular msgName = triangularCheck (checkDupSigPair msgName)

checkDuplicateSignalNamesInMsg : DBCMessage → List ValidationIssue
checkDuplicateSignalNamesInMsg msg =
  checkDupSigTriangular (DBCMessage.name msg) (DBCMessage.signals msg)

checkAllDuplicateSignalNames : List DBCMessage → List ValidationIssue
checkAllDuplicateSignalNames = concatMap checkDuplicateSignalNamesInMsg

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig : String → DBCSignal → List ValidationIssue
checkFactorZeroSig msgName sig =
  rejectDec (ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0))
            (mkIssue IsError FactorZero
              ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
               ++ₛ "': factor is zero (constant-zero signal)"))

checkAllFactorZero : List DBCMessage → List ValidationIssue
checkAllFactorZero = concatMap λ msg →
  concatMap (checkFactorZeroSig (DBCMessage.name msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 4: MULTIPLEXOR NOT FOUND
-- ============================================================================

checkMuxFoundSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxFoundSig msgName allSigs sig with DBCSignal.presence sig
... | Always        = []
... | When muxName _ with any? (λ s → DBCSignal.name s ≟ muxName) allSigs
...   | yes _ = []
...   | no  _ = mkIssue IsError MultiplexorNotFound
                  ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                   ++ₛ "': multiplexor '" ++ₛ muxName
                   ++ₛ "' not found in message") ∷ []

checkAllMuxFound : List DBCMessage → List ValidationIssue
checkAllMuxFound = concatMap λ msg →
  concatMap (checkMuxFoundSig (DBCMessage.name msg) (DBCMessage.signals msg))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 5: MULTIPLEXOR NOT ALWAYS PRESENT
-- ============================================================================

checkMuxAlwaysPresentSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxAlwaysPresentSig msgName allSigs sig with DBCSignal.presence sig
... | Always        = []
... | When muxName _ with findSignalPresence muxName allSigs
...   | nothing          = []
...   | just Always      = []
...   | just (When _ _)  = mkIssue IsError MultiplexorNotAlwaysPresent
                             ("Message '" ++ₛ msgName ++ₛ "', signal '"
                              ++ₛ DBCSignal.name sig ++ₛ "': multiplexor '"
                              ++ₛ muxName
                              ++ₛ "' is itself conditionally present") ∷ []

checkAllMuxAlwaysPresent : List DBCMessage → List ValidationIssue
checkAllMuxAlwaysPresent = concatMap λ msg →
  concatMap (checkMuxAlwaysPresentSig (DBCMessage.name msg) (DBCMessage.signals msg))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 17: MULTIPLEXOR NON-UNIT SCALING
-- ============================================================================

checkMuxScaling : String → String → DBCSignal → List ValidationIssue
checkMuxScaling msgName muxName muxSig
  with SignalDef.factor (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 1
     | SignalDef.offset (DBCSignal.signalDef muxSig) ≟ᵣ ℕtoℚ 0
... | yes _ | yes _ = []
... | _     | _     = mkIssue IsWarning MultiplexorNonUnitScaling
                         ("Message '" ++ₛ msgName ++ₛ "': multiplexor '"
                          ++ₛ muxName
                          ++ₛ "' has non-unit scaling (factor≠1 or offset≠0); "
                          ++ₛ "mux value matching may be unreliable") ∷ []

checkMuxScalingSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxScalingSig msgName allSigs sig with DBCSignal.presence sig
... | Always = []
... | When muxName _ with findSignalInList muxName allSigs
...   | nothing     = []
...   | just muxSig = checkMuxScaling msgName muxName muxSig

checkAllMuxScaling : List DBCMessage → List ValidationIssue
checkAllMuxScaling = concatMap λ msg →
  concatMap (checkMuxScalingSig (DBCMessage.name msg) (DBCMessage.signals msg))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 6: GLOBAL NAME COLLISION
-- ============================================================================

messageSignalNames : DBCMessage → List String
messageSignalNames msg = map DBCSignal.name (DBCMessage.signals msg)

checkGlobalNamePair : DBCMessage → DBCMessage → List ValidationIssue
checkGlobalNamePair m1 m2 =
  let names1  = messageSignalNames m1
      names2  = messageSignalNames m2
      shared  = filter (_∈? names2) names1
  in map (λ n → mkIssue IsWarning GlobalNameCollision
                  ("Signal '" ++ₛ n ++ₛ "' appears in both message '"
                   ++ₛ DBCMessage.name m1 ++ₛ "' and '"
                   ++ₛ DBCMessage.name m2 ++ₛ "'")) shared

checkGlobalNameAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkGlobalNameAgainstList = checkAgainst checkGlobalNamePair

checkAllGlobalNameCollisions : List DBCMessage → List ValidationIssue
checkAllGlobalNameCollisions = triangularCheck checkGlobalNamePair

-- ============================================================================
-- CHECK 7: MIN EXCEEDS MAX
-- ============================================================================

checkMinMaxSig : String → DBCSignal → List ValidationIssue
checkMinMaxSig msgName sig =
  requireDec (SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵣ
              SignalDef.maximum (DBCSignal.signalDef sig))
             (mkIssue IsWarning MinExceedsMax
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ DBCSignal.name sig
                ++ₛ "': minimum exceeds maximum"))

checkAllMinMax : List DBCMessage → List ValidationIssue
checkAllMinMax = concatMap λ msg →
  concatMap (checkMinMaxSig (DBCMessage.name msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 8: SIGNAL EXCEEDS DLC
-- ============================================================================

checkSignalExceedsDLC : String → ℕ → DBCSignal → List ValidationIssue
checkSignalExceedsDLC msgName dlc sig =
  requireDec (SignalDef.startBit (DBCSignal.signalDef sig)
              + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8)
             (mkIssue IsError SignalExceedsDLC
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                ++ₛ "': bit range exceeds DLC"))

checkAllSignalExceedsDLC : List DBCMessage → List ValidationIssue
checkAllSignalExceedsDLC = concatMap λ msg →
  concatMap (checkSignalExceedsDLC (DBCMessage.name msg) (dlcBytes (DBCMessage.dlc msg)))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 9: SIGNAL OVERLAP
-- ============================================================================

checkOverlapPair : String → ℕ → DBCSignal → DBCSignal → List ValidationIssue
checkOverlapPair msgName n s1 s2 =
  requireDec (signalPairValid? n s1 s2)
             (mkIssue IsError SignalOverlap
               ("Message '" ++ₛ msgName ++ₛ "', signals '" ++ₛ DBCSignal.name s1
                ++ₛ "' and '" ++ₛ DBCSignal.name s2 ++ₛ "' overlap"))

checkOverlapAgainstList : String → ℕ → DBCSignal → List DBCSignal → List ValidationIssue
checkOverlapAgainstList msgName n = checkAgainst (checkOverlapPair msgName n)

checkOverlapTriangular : String → ℕ → List DBCSignal → List ValidationIssue
checkOverlapTriangular msgName n = triangularCheck (checkOverlapPair msgName n)

checkOverlapsInMsg : DBCMessage → List ValidationIssue
checkOverlapsInMsg msg =
  checkOverlapTriangular (DBCMessage.name msg) (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg)

checkAllSignalOverlaps : List DBCMessage → List ValidationIssue
checkAllSignalOverlaps = concatMap checkOverlapsInMsg

-- ============================================================================
-- CHECK 10: BIT LENGTH ZERO
-- ============================================================================

checkBitLengthZero : String → DBCSignal → List ValidationIssue
checkBitLengthZero msgName sig =
  rejectDec (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ₙ 0)
            (mkIssue IsError BitLengthZero
              ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
               ++ₛ "': bit length is zero"))

checkAllBitLengthZero : List DBCMessage → List ValidationIssue
checkAllBitLengthZero = concatMap λ msg →
  concatMap (checkBitLengthZero (DBCMessage.name msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME
-- ============================================================================

checkDupNamePair : DBCMessage → DBCMessage → List ValidationIssue
checkDupNamePair m1 m2 =
  rejectDec (DBCMessage.name m1 ≟ DBCMessage.name m2)
            (mkIssue IsWarning DuplicateMessageName
              ("Messages '" ++ₛ DBCMessage.name m1 ++ₛ "' and '"
               ++ₛ DBCMessage.name m2 ++ₛ "' share the same name"))

checkDupNameAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkDupNameAgainstList = checkAgainst checkDupNamePair

checkDuplicateMessageNames : List DBCMessage → List ValidationIssue
checkDuplicateMessageNames = triangularCheck checkDupNamePair

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE
-- ============================================================================

ℤtoℚ : ℤ → ℚ
ℤtoℚ z = z /ᵣ 1

isNegativeℚ : ℚ → Bool
isNegativeℚ q with ℚ.numerator q
... | (+ _)     = false
... | (-[1+ _ ]) = true

checkRangeLow : String → String → ℚ → ℚ → List ValidationIssue
checkRangeLow msgName sigName physMin declaredMin =
  requireDec (declaredMin ≤?ᵣ physMin)
             (mkIssue IsWarning OffsetScaleRange
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ sigName
                ++ₛ "': declared minimum is below physical range"))

checkRangeHigh : String → String → ℚ → ℚ → List ValidationIssue
checkRangeHigh msgName sigName physMax declaredMax =
  requireDec (physMax ≤?ᵣ declaredMax)
             (mkIssue IsWarning OffsetScaleRange
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ sigName
                ++ₛ "': declared maximum is above physical range"))

checkRangeBounds : String → String → ℚ → ℚ → ℚ → ℚ → ℚ → List ValidationIssue
checkRangeBounds msgName sigName factor physA physB declMin declMax
  with isNegativeℚ factor
... | false = checkRangeLow msgName sigName physA declMin ++ₗ checkRangeHigh msgName sigName physB declMax
... | true  = checkRangeLow msgName sigName physB declMin ++ₗ checkRangeHigh msgName sigName physA declMax

checkOffsetScaleRange : String → DBCSignal → List ValidationIssue
checkOffsetScaleRange msgName sig with SignalDef.isSigned (DBCSignal.signalDef sig)
... | true =
  let sd     = DBCSignal.signalDef sig
      n      = SignalDef.bitLength sd
      factor = SignalDef.factor sd
      offset = SignalDef.offset sd
      half   = 2 ^ (n ∸ 1)
      sn     = DBCSignal.name sig
      rawMinℚ = ℤtoℚ (-[1+ pred half ])
      rawMaxℚ = ℕtoℚ (pred half)
      physA   = rawMinℚ *ᵣ factor +ᵣ offset
      physB   = rawMaxℚ *ᵣ factor +ᵣ offset
  in checkRangeBounds msgName sn factor physA physB
                      (SignalDef.minimum sd) (SignalDef.maximum sd)
... | false =
  let sd     = DBCSignal.signalDef sig
      n      = SignalDef.bitLength sd
      factor = SignalDef.factor sd
      offset = SignalDef.offset sd
      sn     = DBCSignal.name sig
      rawMinℚ = ℕtoℚ 0
      rawMaxℚ = ℕtoℚ (pred (2 ^ n))
      physA   = rawMinℚ *ᵣ factor +ᵣ offset
      physB   = rawMaxℚ *ᵣ factor +ᵣ offset
  in checkRangeBounds msgName sn factor physA physB
                      (SignalDef.minimum sd) (SignalDef.maximum sd)

checkAllOffsetScaleRange : List DBCMessage → List ValidationIssue
checkAllOffsetScaleRange = concatMap λ msg →
  concatMap (checkOffsetScaleRange (DBCMessage.name msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 14: EMPTY MESSAGE
-- ============================================================================

checkEmptyMessage : DBCMessage → List ValidationIssue
checkEmptyMessage msg with DBCMessage.signals msg
... | []    = mkIssue IsWarning EmptyMessage
                ("Message '" ++ₛ DBCMessage.name msg
                 ++ₛ "': message has no signals") ∷ []
... | _ ∷ _ = []

checkAllEmptyMessage : List DBCMessage → List ValidationIssue
checkAllEmptyMessage = concatMap checkEmptyMessage

-- ============================================================================
-- CHECK 15: START BIT OUT OF RANGE
-- ============================================================================

checkStartBitOutOfRange : String → DBCSignal → List ValidationIssue
checkStartBitOutOfRange msgName sig =
  requireDec (SignalDef.startBit (DBCSignal.signalDef sig) <? max-physical-bits)
             (mkIssue IsWarning StartBitOutOfRange
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                ++ₛ "': start bit ≥ max-physical-bits"))

checkAllStartBitOutOfRange : List DBCMessage → List ValidationIssue
checkAllStartBitOutOfRange = concatMap λ msg →
  concatMap (checkStartBitOutOfRange (DBCMessage.name msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 16: BIT LENGTH EXCESSIVE
-- ============================================================================

checkBitLengthExcessive : String → DBCSignal → List ValidationIssue
checkBitLengthExcessive msgName sig =
  requireDec (SignalDef.bitLength (DBCSignal.signalDef sig) ≤? max-physical-bits)
             (mkIssue IsWarning BitLengthExcessive
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                ++ₛ "': bit length exceeds max-physical-bits"))

checkAllBitLengthExcessive : List DBCMessage → List ValidationIssue
checkAllBitLengthExcessive = concatMap λ msg →
  concatMap (checkBitLengthExcessive (DBCMessage.name msg)) (DBCMessage.signals msg)
