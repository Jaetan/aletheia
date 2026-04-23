{-# OPTIONS --safe --without-K #-}

-- DBC structural validator: individual check functions.
--
-- Purpose: Per-check functions for all 16 DBC validity conditions.
-- Each check returns [] (no issues) or a singleton list (issue found).
-- checkAll* variants lift per-element checks to full message lists via concatMap.
-- Role: Used by Validity proofs (ErrorChecks, WarningChecks) and composed
--   into validateDBCFull in the parent Validator module.
module Aletheia.DBC.Validator.Checks where

open import Aletheia.DBC.Types using
  ( DBCMessage; DBCSignal; SignalPresence; Always; When
  ; ValidationIssue; mkIssue; IsError; IsWarning
  ; DuplicateMessageId; DuplicateSignalName; FactorZero
  ; MultiplexorNotFound; MultiplexorCycle
  ; GlobalNameCollision; MinExceedsMax; SignalExceedsDLC
  ; SignalOverlap; BitLengthZero; DuplicateMessageName
  ; OffsetScaleRange; EmptyMessage
  ; StartBitOutOfRange; BitLengthExcessive
  ; MultiplexorNonUnitScaling
  ; DuplicateAttributeName; UnknownCommentTarget; UnknownMessageSender
  ; UnknownSignalReceiver
  ; Node; DBCComment
  ; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; EnvironmentVar
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef
  )
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Constants using (max-physical-bits)
open import Aletheia.DBC.Properties using (signalPairValid?)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_; findSignalInList)
open import Aletheia.CAN.DLC using (DLC; dlcBytes; dlcToBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_; map; filter; concatMap; length)
  renaming (_++_ to _++ₗ_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; pred)
open import Data.Nat.Properties using (_≤?_; _<?_; _≟_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapₘ)
open import Data.Rational using (ℚ) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)
open import Aletheia.Prelude using (ℕtoℚ; fromℤ)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_; _≟_ to _≟ᵣ_)
open import Aletheia.DBC.DecRat using (DecRat; 0ᵈ; 1ᵈ; toℚ; _≟ᵈ_; _≤?ᵈ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.List.Membership.DecPropositional _≟ₛ_ using (_∈?_)
open import Aletheia.DBC.Validity.Combinators using
  (requireDec; rejectDec; checkAgainst; triangularCheck)

-- ============================================================================
-- DECIDABLE HELPERS
-- ============================================================================

findSignalPresence : String → List DBCSignal → Maybe SignalPresence
findSignalPresence name sigs = mapₘ DBCSignal.presence (findSignalInList name sigs)

-- ============================================================================
-- LIFTING COMBINATOR
-- ============================================================================

-- Lift a per-signal check (parameterised by message name) to all messages.
-- Replaces the recurring concatMap (λ msg → concatMap (f (name msg)) (signals msg)) pattern.
liftPerSignal : (String → DBCSignal → List ValidationIssue) → List DBCMessage → List ValidationIssue
liftPerSignal f = concatMap λ msg →
  concatMap (f (DBCMessage.name msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs
-- ============================================================================

checkDuplicateIdPair : DBCMessage → DBCMessage → List ValidationIssue
checkDuplicateIdPair m1 m2 =
  rejectDec (DBCMessage.id m1 ≟-CANId DBCMessage.id m2)
            (mkIssue IsError DuplicateMessageId
              ("Messages '" ++ₛ DBCMessage.name m1 ++ₛ "' and '"
               ++ₛ DBCMessage.name m2 ++ₛ "' share the same CAN ID"))

checkDuplicateIdAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkDuplicateIdAgainstList = checkAgainst checkDuplicateIdPair

checkDuplicateMessageIds : List DBCMessage → List ValidationIssue
checkDuplicateMessageIds = triangularCheck checkDuplicateIdPair

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (within a message)
-- ============================================================================

checkDuplicateSignalPair : String → DBCSignal → DBCSignal → List ValidationIssue
checkDuplicateSignalPair msgName s1 s2 =
  rejectDec (DBCSignal.name s1 ≟ₛ DBCSignal.name s2)
            (mkIssue IsError DuplicateSignalName
              ("Message '" ++ₛ msgName ++ₛ "': duplicate signal name '"
               ++ₛ DBCSignal.name s1 ++ₛ "'"))

checkDuplicateSignalAgainstList : String → DBCSignal → List DBCSignal → List ValidationIssue
checkDuplicateSignalAgainstList msgName = checkAgainst (checkDuplicateSignalPair msgName)

checkDuplicateSignalTriangular : String → List DBCSignal → List ValidationIssue
checkDuplicateSignalTriangular msgName = triangularCheck (checkDuplicateSignalPair msgName)

checkDuplicateSignalNamesInMsg : DBCMessage → List ValidationIssue
checkDuplicateSignalNamesInMsg msg =
  checkDuplicateSignalTriangular (DBCMessage.name msg) (DBCMessage.signals msg)

checkAllDuplicateSignalNames : List DBCMessage → List ValidationIssue
checkAllDuplicateSignalNames = concatMap checkDuplicateSignalNamesInMsg

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig : String → DBCSignal → List ValidationIssue
checkFactorZeroSig msgName sig =
  rejectDec (DecRat.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0))
            (mkIssue IsError FactorZero
              ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
               ++ₛ "': factor is zero (constant-zero signal)"))

checkAllFactorZero : List DBCMessage → List ValidationIssue
checkAllFactorZero = liftPerSignal checkFactorZeroSig

-- ============================================================================
-- CHECK 4: MULTIPLEXOR NOT FOUND
-- ============================================================================

checkMuxFoundSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxFoundSig msgName allSigs sig with DBCSignal.presence sig
... | Always        = []
... | When muxName _ with any? (λ s → DBCSignal.name s ≟ₛ muxName) allSigs
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
-- CHECK 5: MULTIPLEXOR CYCLE
-- ============================================================================

-- Walk a mux chain with bounded fuel. Returns true if the chain reaches an
-- Always signal (acyclic) or an unresolved reference (caught by check 4).
-- Returns false only when fuel is exhausted, indicating a cycle.
--
-- Termination: fuel ≤ length sigs at entry (callers pass `length allSigs`),
-- and strictly decreases at every recursive call (`suc f → f`). The
-- structural recursion on ℕ discharges Agda's termination checker without
-- well-founded machinery. No `<-Rec` wrapper is needed because the fuel
-- argument is already the decreasing measure.
--
-- Soundness of the fuel bound: the maximum length of an acyclic mux chain
-- through n signals is n (each signal is visited at most once before
-- reaching an `Always` sink); any chain of length > n must revisit a
-- signal, i.e. contain a cycle. Therefore fuel = length sigs is both
-- necessary (shorter fuel would reject valid acyclic chains longer than the
-- remaining fuel at recursion) and sufficient (longer fuel would accept
-- cycles). Proof of "no-false-positive" would require a pigeonhole argument
-- on the set of visited signals; we rely on the fuel bound operationally
-- and let check 4 (MultiplexorNotFound) catch dangling references.
walkMux : ℕ → List DBCSignal → SignalPresence → Bool
walkMux _       _    Always         = true
walkMux zero    _    (When _ _)     = false
walkMux (suc f) sigs (When name _) with findSignalPresence name sigs
... | nothing = true   -- caught by checkMuxFound (check 4)
... | just p  = walkMux f sigs p

checkMuxCycleSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxCycleSig msgName allSigs sig
  with walkMux (length allSigs) allSigs (DBCSignal.presence sig)
... | true  = []
... | false = mkIssue IsError MultiplexorCycle
                ("Message '" ++ₛ msgName ++ₛ "', signal '"
                 ++ₛ DBCSignal.name sig
                 ++ₛ "': multiplexor chain forms a cycle") ∷ []

checkAllMuxCycle : List DBCMessage → List ValidationIssue
checkAllMuxCycle = concatMap λ msg →
  concatMap (checkMuxCycleSig (DBCMessage.name msg) (DBCMessage.signals msg))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 17: MULTIPLEXOR NON-UNIT SCALING
-- ============================================================================

checkMuxScaling : String → String → DBCSignal → List ValidationIssue
checkMuxScaling msgName muxName muxSig
  with SignalDef.factor (DBCSignal.signalDef muxSig) ≟ᵈ 1ᵈ
     | SignalDef.offset (DBCSignal.signalDef muxSig) ≟ᵈ 0ᵈ
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
  requireDec (SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵈ
              SignalDef.maximum (DBCSignal.signalDef sig))
             (mkIssue IsWarning MinExceedsMax
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ DBCSignal.name sig
                ++ₛ "': minimum exceeds maximum"))

checkAllMinMax : List DBCMessage → List ValidationIssue
checkAllMinMax = liftPerSignal checkMinMaxSig

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
  rejectDec (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ 0)
            (mkIssue IsError BitLengthZero
              ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
               ++ₛ "': bit length is zero"))

checkAllBitLengthZero : List DBCMessage → List ValidationIssue
checkAllBitLengthZero = liftPerSignal checkBitLengthZero

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME
-- ============================================================================

checkDuplicateNamePair : DBCMessage → DBCMessage → List ValidationIssue
checkDuplicateNamePair m1 m2 =
  rejectDec (DBCMessage.name m1 ≟ₛ DBCMessage.name m2)
            (mkIssue IsWarning DuplicateMessageName
              ("Messages '" ++ₛ DBCMessage.name m1 ++ₛ "' and '"
               ++ₛ DBCMessage.name m2 ++ₛ "' share the same name"))

checkDuplicateNameAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkDuplicateNameAgainstList = checkAgainst checkDuplicateNamePair

checkDuplicateMessageNames : List DBCMessage → List ValidationIssue
checkDuplicateMessageNames = triangularCheck checkDuplicateNamePair

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE
-- ============================================================================

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

-- Raw (pre-scaling) range of an n-bit integer value.
-- Signed: two's complement range [−2^(n−1), 2^(n−1)−1].
-- Unsigned: [0, 2^n − 1].
rawRange : Bool → ℕ → ℚ × ℚ
rawRange true  n = fromℤ (-[1+ pred (2 ^ (n ∸ 1)) ]) , ℕtoℚ (pred (2 ^ (n ∸ 1)))
rawRange false n = ℕtoℚ 0 , ℕtoℚ (pred (2 ^ n))

checkOffsetScaleRange : String → DBCSignal → List ValidationIssue
checkOffsetScaleRange msgName sig =
  let sd      = DBCSignal.signalDef sig
      factor  = toℚ (SignalDef.factor sd)
      offset  = toℚ (SignalDef.offset sd)
      raw     = rawRange (SignalDef.isSigned sd) (SignalDef.bitLength sd)
      physA   = proj₁ raw *ᵣ factor +ᵣ offset
      physB   = proj₂ raw *ᵣ factor +ᵣ offset
  in checkRangeBounds msgName (DBCSignal.name sig) factor physA physB
                      (toℚ (SignalDef.minimum sd)) (toℚ (SignalDef.maximum sd))

checkAllOffsetScaleRange : List DBCMessage → List ValidationIssue
checkAllOffsetScaleRange = liftPerSignal checkOffsetScaleRange

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
checkAllStartBitOutOfRange = liftPerSignal checkStartBitOutOfRange

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
checkAllBitLengthExcessive = liftPerSignal checkBitLengthExcessive

-- ============================================================================
-- CHECK 18: DUPLICATE ATTRIBUTE NAME (BA_DEF_ names only)
-- ============================================================================
-- Names in BA_DEF_DEF_ and BA_ refer back to BA_DEF_ names, so only BA_DEF_
-- names need pairwise distinctness; assignments are validated by resolution
-- separately (not in commit 1 scope).

attrDefNames : List DBCAttribute → List String
attrDefNames [] = []
attrDefNames (DBCAttrDef d ∷ rest)     = AttrDef.name d ∷ attrDefNames rest
attrDefNames (DBCAttrDefault _ ∷ rest) = attrDefNames rest
attrDefNames (DBCAttrAssign _ ∷ rest)  = attrDefNames rest

checkDuplicateAttrNamePair : String → String → List ValidationIssue
checkDuplicateAttrNamePair n1 n2 =
  rejectDec (n1 ≟ₛ n2)
            (mkIssue IsWarning DuplicateAttributeName
              ("Duplicate attribute definition name '" ++ₛ n1 ++ₛ "'"))

checkDuplicateAttributeNames : List DBCAttribute → List ValidationIssue
checkDuplicateAttributeNames attrs = triangularCheck checkDuplicateAttrNamePair (attrDefNames attrs)

-- ============================================================================
-- CHECK 19: UNKNOWN COMMENT TARGET
-- ============================================================================
-- A CM_ line may target a node (BU_), message (BO_), signal (SG_), or
-- environment variable (EV_). Network-level comments (no keyword) target
-- the DBC as a whole and require no resolution.

-- Linear CANId lookup in a message list.
findMessageInList : CANId → List DBCMessage → Maybe DBCMessage
findMessageInList _   []       = nothing
findMessageInList cid (m ∷ ms) with cid ≟-CANId DBCMessage.id m
... | yes _ = just m
... | no  _ = findMessageInList cid ms

checkCommentTargetExists : List DBCMessage → List Node → List EnvironmentVar
                         → DBCComment → List ValidationIssue
checkCommentTargetExists msgs nodes envVars cm with DBCComment.target cm
... | CTNetwork = []
... | CTNode nname =
        requireDec (any? (λ n → Node.name n ≟ₛ nname) nodes)
          (mkIssue IsWarning UnknownCommentTarget
            ("Comment references unknown node '" ++ₛ nname ++ₛ "'"))
... | CTMessage mid with findMessageInList mid msgs
...   | just _  = []
...   | nothing = mkIssue IsWarning UnknownCommentTarget
                    "Comment references unknown message" ∷ []
checkCommentTargetExists msgs _ _ cm | CTSignal mid sname
  with findMessageInList mid msgs
...   | nothing = mkIssue IsWarning UnknownCommentTarget
                    ("Comment references unknown signal '"
                     ++ₛ sname ++ₛ "' (message not found)") ∷ []
...   | just m with findSignalInList sname (DBCMessage.signals m)
...     | just _  = []
...     | nothing = mkIssue IsWarning UnknownCommentTarget
                      ("Comment references unknown signal '" ++ₛ sname
                       ++ₛ "' in message '" ++ₛ DBCMessage.name m ++ₛ "'") ∷ []
checkCommentTargetExists _ _ envVars cm | CTEnvVar evname =
  requireDec (any? (λ ev → EnvironmentVar.name ev ≟ₛ evname) envVars)
    (mkIssue IsWarning UnknownCommentTarget
      ("Comment references unknown environment variable '" ++ₛ evname ++ₛ "'"))

checkAllUnknownCommentTargets : List DBCMessage → List Node → List EnvironmentVar
                              → List DBCComment → List ValidationIssue
checkAllUnknownCommentTargets msgs nodes envVars =
  concatMap (checkCommentTargetExists msgs nodes envVars)

-- ============================================================================
-- CHECK 20: UNKNOWN MESSAGE SENDER
-- ============================================================================
-- A message's sender should correspond to a declared node. When the DBC
-- has no BU_ section (nodes = []), the check is skipped — many DBCs omit
-- BU_ entirely and the sender field is informational. When BU_ is present,
-- each sender is validated against it.

checkUnknownSender : List Node → DBCMessage → List ValidationIssue
checkUnknownSender nodes msg =
  requireDec (any? (λ n → Node.name n ≟ₛ DBCMessage.sender msg) nodes)
    (mkIssue IsWarning UnknownMessageSender
      ("Message '" ++ₛ DBCMessage.name msg
       ++ₛ "': sender '" ++ₛ DBCMessage.sender msg
       ++ₛ "' not declared in BU_ (nodes) list"))

checkAllUnknownMessageSenders : List DBCMessage → List Node → List ValidationIssue
checkAllUnknownMessageSenders _    []             = []
checkAllUnknownMessageSenders msgs nodes@(_ ∷ _) = concatMap (checkUnknownSender nodes) msgs

-- ============================================================================
-- CHECK 21: UNKNOWN SIGNAL RECEIVER
-- ============================================================================
-- Each receiver listed on a signal should correspond to a declared node.
-- When the DBC has no BU_ section (nodes = []) the check is skipped, same
-- as checkAllUnknownMessageSenders above.

checkUnknownReceiver : List Node → String → String → String → List ValidationIssue
checkUnknownReceiver nodes msgName sigName receiver =
  requireDec (any? (λ n → Node.name n ≟ₛ receiver) nodes)
    (mkIssue IsWarning UnknownSignalReceiver
      ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ sigName
       ++ₛ "': receiver '" ++ₛ receiver
       ++ₛ "' not declared in BU_ (nodes) list"))

checkReceiversForSignal : List Node → String → DBCSignal → List ValidationIssue
checkReceiversForSignal nodes msgName sig =
  concatMap (checkUnknownReceiver nodes msgName (DBCSignal.name sig))
            (DBCSignal.receivers sig)

checkAllUnknownSignalReceivers : List DBCMessage → List Node → List ValidationIssue
checkAllUnknownSignalReceivers _    []             = []
checkAllUnknownSignalReceivers msgs nodes@(_ ∷ _) =
  liftPerSignal (checkReceiversForSignal nodes) msgs

-- ============================================================================
-- CHECK 22: UNKNOWN ADDITIONAL SENDER (BO_TX_BU_)
-- ============================================================================
-- Each additional transmitter listed on a message's BO_TX_BU_ line should
-- correspond to a declared node. Reuses the UnknownMessageSender issue code
-- (same domain concept — a sender that is not in BU_) and skips when the DBC
-- omits BU_, matching the behavior of checkAllUnknownMessageSenders.

checkUnknownAdditionalSender : List Node → String → String → List ValidationIssue
checkUnknownAdditionalSender nodes msgName sender =
  requireDec (any? (λ n → Node.name n ≟ₛ sender) nodes)
    (mkIssue IsWarning UnknownMessageSender
      ("Message '" ++ₛ msgName
       ++ₛ "': additional sender '" ++ₛ sender
       ++ₛ "' not declared in BU_ (nodes) list"))

checkAdditionalSendersForMessage : List Node → DBCMessage → List ValidationIssue
checkAdditionalSendersForMessage nodes msg =
  concatMap (checkUnknownAdditionalSender nodes (DBCMessage.name msg))
            (DBCMessage.senders msg)

checkAllUnknownAdditionalSenders : List DBCMessage → List Node → List ValidationIssue
checkAllUnknownAdditionalSenders _    []             = []
checkAllUnknownAdditionalSenders msgs nodes@(_ ∷ _) =
  concatMap (checkAdditionalSendersForMessage nodes) msgs
