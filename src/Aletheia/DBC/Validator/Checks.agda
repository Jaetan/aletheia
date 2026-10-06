-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- DBC structural validator: individual check functions.
--
-- Purpose: Per-check functions for the DBC validity conditions.
-- Each check returns [] (no issues) or the issues it found, one per broken condition.
-- checkAll* variants lift per-element checks to full message lists via concatMap.
-- Role: Used by Validity proofs (ErrorChecks, WarningChecks) and composed
--   into validateDBCFull in the parent Validator module.
--
-- Cat 26 cold-path acceptance: this module runs per-DBC-ingest (called from
-- handleParseDBC / handleParseDBCText / handleValidateDBC — never per-frame),
-- so `Dec` allocations from `_≟ₛ_`, `_≟_`, `_≤?_`, etc. are acceptable here.
-- The per-call witness allocation is dominated by the surrounding validation
-- machinery (JSON parsing, full-message traversal). Revisit only if the
-- validator is promoted to a hot-path consumer (e.g. per-frame re-validation),
-- at which point the same Bool fast-path treatment applied to
-- `LTL/SignalPredicate/Cache` would be needed here. Mirrors the in-source
-- revisit signal pattern from `Aletheia.Prelude.lookupByKey`.
module Aletheia.DBC.Validator.Checks where
open import Aletheia.DBC.Identifier using (Identifier; nameStr)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)

open import Aletheia.DBC.Types using
  ( signalNameStr; messageNameStr; messageSenderStr; attrDefNameStr
  ; DBCMessage; DBCSignal; SignalPresence; Always; When
  ; ValidationIssue; mkIssue; IsError; IsWarning; IssueCode
  ; DuplicateMessageId; DuplicateSignalName; FactorZero
  ; MultiplexorNotFound; MultiplexorCycle
  ; GlobalNameCollision; MinExceedsMax; SignalExceedsDLC
  ; SignalOverlap; BitLengthZero; DuplicateMessageName
  ; OffsetScaleRange; EmptyMessage; RangeExceedsBits
  ; StartBitOutOfRange; BitLengthExcessive
  ; MultiplexorNonUnitScaling
  ; DuplicateAttributeName; UnknownCommentTarget; UnknownMessageSender
  ; UnknownSignalReceiver; UnknownValueDescriptionTarget
  ; RawValueDesc
  ; Node; DBCComment
  ; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; EnvironmentVar
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )
open import Aletheia.DBC.Decidable using (signalPairValid?)
open import Aletheia.DBC.Decidable.SignalGeometry using
  (startBitInFrame?; bitLengthInFrame?; signalFitsFrame?)
open import Aletheia.CAN.DBCHelpers using (findSignalInList)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding.Value.Facts using (bitsRange)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map; concatMap; length)
  renaming (_++_ to _++ₗ_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapₘ)
open import Data.Rational using (ℚ)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_)
open import Aletheia.DBC.DecRat using (DecRat; 0ᵈ; 1ᵈ; toℚ; _≟ᵈ_; _≤?ᵈ_)
open import Data.Integer using (+_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Data.List.Relation.Unary.Any using (any?)
open import Aletheia.DBC.Validity.Combinators using
  (requireDec; requireDec₀; rejectDec; checkAgainst; triangularCheck)
open import Aletheia.DBC.Validator.Targets using
  (NameSet; _∈?_; nodeNames; envVarNames; MessageIndex; messageIndex; findMessage)
open import Aletheia.DBC.Validator.SharedKeys using
  ( Entry; message; label; nameKey; showCanIdText
  ; messageEntries; messageIdEntries; signalEntries; sharedKeyGroups; perOwner
  ; joinAnd; quoted; sharedIdText )
open import Data.List.NonEmpty using (List⁺) renaming (toList to toList⁺; head to head⁺)
open import Function using (_∘_)
open import Aletheia.DBC.TextParser.WellFormedCheck.Foundations using
  (presenceIssue; mcIssue)

-- ============================================================================
-- DECIDABLE HELPERS
-- ============================================================================

findSignalPresence : List Char → List DBCSignal → Maybe SignalPresence
findSignalPresence name sigs = mapₘ DBCSignal.presence (findSignalInList name sigs)

-- ============================================================================
-- LIFTING COMBINATOR
-- ============================================================================

-- Lift a per-signal check (parameterised by message name) to all messages.
-- Replaces the recurring concatMap (λ msg → concatMap (f (name msg)) (signals msg)) pattern.
liftPerSignal : (String → DBCSignal → List ValidationIssue) → List DBCMessage → List ValidationIssue
liftPerSignal f = concatMap λ msg →
  concatMap (f (messageNameStr msg)) (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs
-- ============================================================================

-- One issue per CAN ID two or more messages share, naming them in order.
duplicateIdIssue : List⁺ Entry → ValidationIssue
duplicateIdIssue g = mkIssue IsError DuplicateMessageId (sharedIdText g)

checkAllDuplicateMessageIds : List DBCMessage → List ValidationIssue
checkAllDuplicateMessageIds msgs = map duplicateIdIssue (sharedKeyGroups (messageIdEntries msgs))

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (within a message)
-- ============================================================================

checkDuplicateSignalPair : String → DBCSignal → DBCSignal → List ValidationIssue
checkDuplicateSignalPair msgName s1 s2 =
  rejectDec (signalNameStr s1 ≟ₛ signalNameStr s2)
            (mkIssue IsError DuplicateSignalName
              ("Message '" ++ₛ msgName ++ₛ "': duplicate signal name '"
               ++ₛ signalNameStr s1 ++ₛ "'"))

checkDuplicateSignalAgainstList : String → DBCSignal → List DBCSignal → List ValidationIssue
checkDuplicateSignalAgainstList msgName = checkAgainst (checkDuplicateSignalPair msgName)

checkDuplicateSignalTriangular : String → List DBCSignal → List ValidationIssue
checkDuplicateSignalTriangular msgName = triangularCheck (checkDuplicateSignalPair msgName)

checkDuplicateSignalNamesInMsg : DBCMessage → List ValidationIssue
checkDuplicateSignalNamesInMsg msg =
  checkDuplicateSignalTriangular (messageNameStr msg) (DBCMessage.signals msg)

checkAllDuplicateSignalNames : List DBCMessage → List ValidationIssue
checkAllDuplicateSignalNames = concatMap checkDuplicateSignalNamesInMsg

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig : String → DBCSignal → List ValidationIssue
checkFactorZeroSig msgName sig =
  rejectDec (DecRat.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0))
            (mkIssue IsError FactorZero
              ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
               ++ₛ "': factor is zero (constant-zero signal)"))

checkAllFactorZero : List DBCMessage → List ValidationIssue
checkAllFactorZero = liftPerSignal checkFactorZeroSig

-- ============================================================================
-- CHECK 4: MULTIPLEXOR NOT FOUND
-- ============================================================================

checkMuxFoundSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxFoundSig msgName allSigs sig with DBCSignal.presence sig
... | Always        = []
... | When muxName _ with any? (λ s → signalNameStr s ≟ₛ nameStr muxName) allSigs
...   | yes _ = []
...   | no  _ = mkIssue IsError MultiplexorNotFound
                  ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
                   ++ₛ "': multiplexor '" ++ₛ nameStr muxName
                   ++ₛ "' not found in message") ∷ []

checkAllMuxFound : List DBCMessage → List ValidationIssue
checkAllMuxFound = concatMap λ msg →
  concatMap (checkMuxFoundSig (messageNameStr msg) (DBCMessage.signals msg))
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
walkMux (suc f) sigs (When name _) with findSignalPresence (Identifier.name name) sigs
... | nothing = true   -- caught by checkMuxFound (check 4)
... | just p  = walkMux f sigs p

checkMuxCycleSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxCycleSig msgName allSigs sig
  with walkMux (length allSigs) allSigs (DBCSignal.presence sig)
... | true  = []
... | false = mkIssue IsError MultiplexorCycle
                ("Message '" ++ₛ msgName ++ₛ "', signal '"
                 ++ₛ signalNameStr sig
                 ++ₛ "': multiplexor chain forms a cycle") ∷ []

checkAllMuxCycle : List DBCMessage → List ValidationIssue
checkAllMuxCycle = concatMap λ msg →
  concatMap (checkMuxCycleSig (messageNameStr msg) (DBCMessage.signals msg))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 17: MULTIPLEXOR NON-UNIT SCALING
-- ============================================================================

checkMuxScaling : String → Identifier → DBCSignal → List ValidationIssue
checkMuxScaling msgName muxName muxSig
  with SignalDef.factor (DBCSignal.signalDef muxSig) ≟ᵈ 1ᵈ
     | SignalDef.offset (DBCSignal.signalDef muxSig) ≟ᵈ 0ᵈ
... | yes _ | yes _ = []
... | _     | _     = mkIssue IsWarning MultiplexorNonUnitScaling
                         ("Message '" ++ₛ msgName ++ₛ "': multiplexor '"
                          ++ₛ nameStr muxName
                          ++ₛ "' has non-unit scaling (factor≠1 or offset≠0); "
                          ++ₛ "mux value matching may be unreliable") ∷ []

checkMuxScalingSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxScalingSig msgName allSigs sig with DBCSignal.presence sig
... | Always = []
... | When muxName _ with findSignalInList (Identifier.name muxName) allSigs
...   | nothing     = []
...   | just muxSig = checkMuxScaling msgName muxName muxSig

checkAllMuxScaling : List DBCMessage → List ValidationIssue
checkAllMuxScaling = concatMap λ msg →
  concatMap (checkMuxScalingSig (messageNameStr msg) (DBCMessage.signals msg))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 6: GLOBAL NAME COLLISION
-- ============================================================================

-- One issue per signal name that signals of two or more messages share,
-- naming those messages in order.
globalNameIssue : List⁺ Entry → ValidationIssue
globalNameIssue g =
  mkIssue IsWarning GlobalNameCollision
    ("Signal " ++ₛ quoted (label (head⁺ g)) ++ₛ " appears in messages "
     ++ₛ joinAnd (map (quoted ∘ messageNameStr ∘ message) (toList⁺ (perOwner g))))

checkAllGlobalNameCollisions : List DBCMessage → List ValidationIssue
checkAllGlobalNameCollisions msgs = map globalNameIssue (sharedKeyGroups (signalEntries msgs))

-- ============================================================================
-- CHECK 7: MIN EXCEEDS MAX
-- ============================================================================

checkMinMaxSig : String → DBCSignal → List ValidationIssue
checkMinMaxSig msgName sig =
  requireDec (SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵈ
              SignalDef.maximum (DBCSignal.signalDef sig))
             (mkIssue IsWarning MinExceedsMax
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ signalNameStr sig
                ++ₛ "': minimum exceeds maximum"))

checkAllMinMax : List DBCMessage → List ValidationIssue
checkAllMinMax = liftPerSignal checkMinMaxSig

-- ============================================================================
-- CHECK 8: SIGNAL EXCEEDS DLC
-- ============================================================================

checkSignalExceedsDLC : String → ℕ → DBCSignal → List ValidationIssue
checkSignalExceedsDLC msgName dlc sig =
  requireDec (signalFitsFrame? dlc
               (SignalDef.startBit (DBCSignal.signalDef sig))
               (SignalDef.bitLength (DBCSignal.signalDef sig)))
             (mkIssue IsError SignalExceedsDLC
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
                ++ₛ "': bit range exceeds DLC"))

checkAllSignalExceedsDLC : List DBCMessage → List ValidationIssue
checkAllSignalExceedsDLC = concatMap λ msg →
  concatMap (checkSignalExceedsDLC (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg)))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 9: SIGNAL OVERLAP
-- ============================================================================

checkOverlapPair : String → ℕ → DBCSignal → DBCSignal → List ValidationIssue
checkOverlapPair msgName n s1 s2 =
  requireDec (signalPairValid? n s1 s2)
             (mkIssue IsError SignalOverlap
               ("Message '" ++ₛ msgName ++ₛ "', signals '" ++ₛ signalNameStr s1
                ++ₛ "' and '" ++ₛ signalNameStr s2 ++ₛ "' overlap"))

checkOverlapAgainstList : String → ℕ → DBCSignal → List DBCSignal → List ValidationIssue
checkOverlapAgainstList msgName n = checkAgainst (checkOverlapPair msgName n)

checkOverlapTriangular : String → ℕ → List DBCSignal → List ValidationIssue
checkOverlapTriangular msgName n = triangularCheck (checkOverlapPair msgName n)

checkOverlapsInMsg : DBCMessage → List ValidationIssue
checkOverlapsInMsg msg =
  checkOverlapTriangular (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg)

checkAllSignalOverlaps : List DBCMessage → List ValidationIssue
checkAllSignalOverlaps = concatMap checkOverlapsInMsg

-- ============================================================================
-- CHECK 10: BIT LENGTH ZERO
-- ============================================================================

checkBitLengthZero : String → DBCSignal → List ValidationIssue
checkBitLengthZero msgName sig =
  rejectDec (SignalDef.bitLength (DBCSignal.signalDef sig) ≟ 0)
            (mkIssue IsError BitLengthZero
              ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
               ++ₛ "': bit length is zero"))

checkAllBitLengthZero : List DBCMessage → List ValidationIssue
checkAllBitLengthZero = liftPerSignal checkBitLengthZero

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME
-- ============================================================================

-- One issue per name two or more messages share, naming them by CAN ID.
duplicateNameIssue : List⁺ Entry → ValidationIssue
duplicateNameIssue g =
  mkIssue IsWarning DuplicateMessageName
    ("Messages with CAN IDs "
     ++ₛ joinAnd (map (showCanIdText ∘ DBCMessage.id ∘ message) (toList⁺ g))
     ++ₛ " share the name " ++ₛ quoted (label (head⁺ g)))

checkAllDuplicateMessageNames : List DBCMessage → List ValidationIssue
checkAllDuplicateMessageNames msgs =
  map duplicateNameIssue
    (sharedKeyGroups (messageEntries (nameKey ∘ messageNameStr) messageNameStr 0 msgs))

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE
-- ============================================================================

checkRangeLow : String → String → ℚ → ℚ → List ValidationIssue
checkRangeLow msgName sigName physMin declaredMin =
  requireDec (declaredMin ≤?ᵣ physMin)
             (mkIssue IsWarning OffsetScaleRange
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ sigName
                ++ₛ "': its bits carry values below the declared minimum"))

checkRangeHigh : String → String → ℚ → ℚ → List ValidationIssue
checkRangeHigh msgName sigName physMax declaredMax =
  requireDec (physMax ≤?ᵣ declaredMax)
             (mkIssue IsWarning OffsetScaleRange
               ("Message '" ++ₛ msgName ++ₛ "', signal '"
                ++ₛ sigName
                ++ₛ "': its bits carry values above the declared maximum"))

checkOffsetScaleRange : String → DBCSignal → List ValidationIssue
checkOffsetScaleRange msgName sig =
  let sd = DBCSignal.signalDef sig
  in checkRangeLow msgName (signalNameStr sig) (proj₁ (bitsRange sd)) (toℚ (SignalDef.minimum sd))
     ++ₗ checkRangeHigh msgName (signalNameStr sig) (proj₂ (bitsRange sd)) (toℚ (SignalDef.maximum sd))

checkAllOffsetScaleRange : List DBCMessage → List ValidationIssue
checkAllOffsetScaleRange = liftPerSignal checkOffsetScaleRange

-- ============================================================================
-- CHECK 26: DECLARED RANGE PAST THE BITS
-- ============================================================================
-- The converse of check 13: a declared minimum or maximum that no raw value
-- reaches.  A value the range admits there has no encoding, so building a
-- frame with it could only fail; a DBC carrying one is refused at load.

checkRangeExceedsBitsSig : String → DBCSignal → List ValidationIssue
checkRangeExceedsBitsSig msgName sig =
  let sd    = DBCSignal.signalDef sig
      subject = "Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
  in requireDec (proj₁ (bitsRange sd) ≤?ᵣ toℚ (SignalDef.minimum sd))
       (mkIssue IsError RangeExceedsBits
         (subject ++ₛ "': declared minimum lies below the values its bits carry"))
     ++ₗ requireDec (toℚ (SignalDef.maximum sd) ≤?ᵣ proj₂ (bitsRange sd))
       (mkIssue IsError RangeExceedsBits
         (subject ++ₛ "': declared maximum lies above the values its bits carry"))

checkAllRangeExceedsBits : List DBCMessage → List ValidationIssue
checkAllRangeExceedsBits = liftPerSignal checkRangeExceedsBitsSig

-- ============================================================================
-- CHECK 14: EMPTY MESSAGE
-- ============================================================================

checkEmptyMessage : DBCMessage → List ValidationIssue
checkEmptyMessage msg with DBCMessage.signals msg
... | []    = mkIssue IsWarning EmptyMessage
                ("Message '" ++ₛ messageNameStr msg
                 ++ₛ "': message has no signals") ∷ []
... | _ ∷ _ = []

checkAllEmptyMessage : List DBCMessage → List ValidationIssue
checkAllEmptyMessage = concatMap checkEmptyMessage

-- ============================================================================
-- CHECK 15: START BIT OUT OF RANGE
-- ============================================================================

checkStartBitOutOfRange : String → ℕ → DBCSignal → List ValidationIssue
checkStartBitOutOfRange msgName dlc sig =
  requireDec (startBitInFrame? dlc (SignalDef.startBit (DBCSignal.signalDef sig)))
             (mkIssue IsWarning StartBitOutOfRange
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
                ++ₛ "': start bit is outside the frame capacity"))

checkAllStartBitOutOfRange : List DBCMessage → List ValidationIssue
checkAllStartBitOutOfRange = concatMap λ msg →
  concatMap (checkStartBitOutOfRange (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg)))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 16: BIT LENGTH EXCESSIVE
-- ============================================================================

checkBitLengthExcessive : String → ℕ → DBCSignal → List ValidationIssue
checkBitLengthExcessive msgName dlc sig =
  requireDec (bitLengthInFrame? dlc (SignalDef.bitLength (DBCSignal.signalDef sig)))
             (mkIssue IsWarning BitLengthExcessive
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
                ++ₛ "': bit length exceeds the frame capacity"))

checkAllBitLengthExcessive : List DBCMessage → List ValidationIssue
checkAllBitLengthExcessive = concatMap λ msg →
  concatMap (checkBitLengthExcessive (messageNameStr msg) (dlcBytes (DBCMessage.dlc msg)))
            (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 18: DUPLICATE ATTRIBUTE NAME (BA_DEF_ names only)
-- ============================================================================
-- Names in BA_DEF_DEF_ and BA_ refer back to BA_DEF_ names, so only BA_DEF_
-- names need pairwise distinctness; assignments are validated by resolution
-- separately (not in commit 1 scope).

attrDefNames : List DBCAttribute → List String
attrDefNames [] = []
attrDefNames (DBCAttrDef d ∷ rest)     = attrDefNameStr d ∷ attrDefNames rest
attrDefNames (DBCAttrDefault _ ∷ rest) = attrDefNames rest
attrDefNames (DBCAttrAssign _ ∷ rest)  = attrDefNames rest

checkDuplicateAttrNamePair : String → String → List ValidationIssue
checkDuplicateAttrNamePair n1 n2 =
  rejectDec (n1 ≟ₛ n2)
            (mkIssue IsWarning DuplicateAttributeName
              ("Duplicate attribute definition name '" ++ₛ n1 ++ₛ "'"))

checkAllDuplicateAttributeNames : List DBCAttribute → List ValidationIssue
checkAllDuplicateAttributeNames attrs = triangularCheck checkDuplicateAttrNamePair (attrDefNames attrs)

-- ============================================================================
-- CHECK 19: UNKNOWN COMMENT TARGET
-- ============================================================================
-- A CM_ line may target a node (BU_), message (BO_), signal (SG_), or
-- environment variable (EV_). Network-level comments (no keyword) target
-- the DBC as a whole and require no resolution.

-- What a comment can name, each indexed once per check.
record CommentTargets : Set where
  field
    messages : MessageIndex
    nodes    : NameSet
    envVars  : NameSet

commentTargets : List DBCMessage → List Node → List EnvironmentVar → CommentTargets
commentTargets msgs nodes envVars = record
  { messages = messageIndex msgs ; nodes = nodeNames nodes ; envVars = envVarNames envVars }

checkCommentTargetExists : CommentTargets → DBCComment → List ValidationIssue
checkCommentTargetExists ts cm with DBCComment.target cm
... | CTNetwork = []
... | CTNode nname =
        requireDec₀ (Identifier.name nname ∈? CommentTargets.nodes ts)
          (mkIssue IsWarning UnknownCommentTarget
            ("Comment references unknown node '" ++ₛ nameStr nname ++ₛ "'"))
... | CTMessage mid with findMessage mid (CommentTargets.messages ts)
...   | just _  = []
...   | nothing = mkIssue IsWarning UnknownCommentTarget
                    "Comment references unknown message" ∷ []
checkCommentTargetExists ts cm | CTSignal mid sname
  with findMessage mid (CommentTargets.messages ts)
...   | nothing = mkIssue IsWarning UnknownCommentTarget
                    ("Comment references unknown signal '"
                     ++ₛ nameStr sname ++ₛ "' (message not found)") ∷ []
...   | just m with findSignalInList (Identifier.name sname) (DBCMessage.signals m)
...     | just _  = []
...     | nothing = mkIssue IsWarning UnknownCommentTarget
                      ("Comment references unknown signal '" ++ₛ nameStr sname
                       ++ₛ "' in message '" ++ₛ messageNameStr m ++ₛ "'") ∷ []
checkCommentTargetExists ts cm | CTEnvVar evname =
  requireDec₀ (Identifier.name evname ∈? CommentTargets.envVars ts)
    (mkIssue IsWarning UnknownCommentTarget
      ("Comment references unknown environment variable '" ++ₛ nameStr evname ++ₛ "'"))

checkAllUnknownCommentTargets : List DBCMessage → List Node → List EnvironmentVar
                              → List DBCComment → List ValidationIssue
checkAllUnknownCommentTargets msgs nodes envVars =
  concatMap (checkCommentTargetExists (commentTargets msgs nodes envVars))

-- Shared body for CHECK 20 / 21 / 22 "is name X declared as a node?"
-- warnings.  Rejects when `name` is not among the declared node names,
-- emitting an IsWarning-severity issue with the given code and detail.
private
  checkUnknownNodeReference :
    NameSet → Identifier → IssueCode → String → List ValidationIssue
  checkUnknownNodeReference known name code detail =
    requireDec₀ (Identifier.name name ∈? known) (mkIssue IsWarning code detail)

-- ============================================================================
-- CHECK 20: UNKNOWN MESSAGE SENDER
-- ============================================================================
-- A message's sender should correspond to a declared node. When the DBC
-- has no BU_ section (nodes = []), the check is skipped — many DBCs omit
-- BU_ entirely and the sender field is informational. When BU_ is present,
-- each sender is validated against it.

checkUnknownSender : NameSet → DBCMessage → List ValidationIssue
checkUnknownSender known msg =
  checkUnknownNodeReference known (DBCMessage.sender msg) UnknownMessageSender
    ("Message '" ++ₛ messageNameStr msg
     ++ₛ "': sender '" ++ₛ messageSenderStr msg
     ++ₛ "' not declared in BU_ (nodes) list")

checkAllUnknownMessageSenders : List DBCMessage → List Node → List ValidationIssue
checkAllUnknownMessageSenders _    []             = []
checkAllUnknownMessageSenders msgs nodes@(_ ∷ _) = concatMap (checkUnknownSender (nodeNames nodes)) msgs

-- ============================================================================
-- CHECK 21: UNKNOWN SIGNAL RECEIVER
-- ============================================================================
-- Each receiver listed on a signal should correspond to a declared node.
-- When the DBC has no BU_ section (nodes = []) the check is skipped, same
-- as checkAllUnknownMessageSenders above.

checkUnknownReceiver : NameSet → String → String → Identifier → List ValidationIssue
checkUnknownReceiver known msgName sigName receiver =
  checkUnknownNodeReference known receiver UnknownSignalReceiver
    ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ sigName
     ++ₛ "': receiver '" ++ₛ nameStr receiver
     ++ₛ "' not declared in BU_ (nodes) list")

checkReceiversForSignal : NameSet → String → DBCSignal → List ValidationIssue
checkReceiversForSignal known msgName sig =
  concatMap (checkUnknownReceiver known msgName (signalNameStr sig))
            (CanonicalReceivers.list (DBCSignal.receivers sig))

checkAllUnknownSignalReceivers : List DBCMessage → List Node → List ValidationIssue
checkAllUnknownSignalReceivers _    []             = []
checkAllUnknownSignalReceivers msgs nodes@(_ ∷ _) =
  liftPerSignal (checkReceiversForSignal (nodeNames nodes)) msgs

-- ============================================================================
-- CHECK 22: UNKNOWN ADDITIONAL SENDER (BO_TX_BU_)
-- ============================================================================
-- Each additional transmitter listed on a message's BO_TX_BU_ line should
-- correspond to a declared node. Reuses the UnknownMessageSender issue code
-- (same domain concept — a sender that is not in BU_) and skips when the DBC
-- omits BU_, matching the behavior of checkAllUnknownMessageSenders.

checkUnknownAdditionalSender : NameSet → String → Identifier → List ValidationIssue
checkUnknownAdditionalSender known msgName sender =
  checkUnknownNodeReference known sender UnknownMessageSender
    ("Message '" ++ₛ msgName
     ++ₛ "': additional sender '" ++ₛ nameStr sender
     ++ₛ "' not declared in BU_ (nodes) list")

checkAdditionalSendersForMessage : NameSet → DBCMessage → List ValidationIssue
checkAdditionalSendersForMessage known msg =
  concatMap (checkUnknownAdditionalSender known (messageNameStr msg))
            (DBCMessage.senders msg)

checkAllUnknownAdditionalSenders : List DBCMessage → List Node → List ValidationIssue
checkAllUnknownAdditionalSenders _    []             = []
checkAllUnknownAdditionalSenders msgs nodes@(_ ∷ _) =
  concatMap (checkAdditionalSendersForMessage (nodeNames nodes)) msgs

-- ============================================================================
-- CHECK 23: UNKNOWN VALUE DESCRIPTION TARGET (VAL_)
-- ============================================================================
-- A `VAL_` line carries a `(canId, signalName)` pair plus value-label entries.
-- The text parser preserves entries that did not resolve against the assembled
-- message list on `DBC.unresolvedValueDescs`; the rest
-- are stitched onto their owning `DBCSignal.valueDescriptions` by
-- `attachValueDescs`.  This check walks the residual list and emits one
-- warning per entry.  Unlike CHECK 21/22, the input is a flat list of
-- `RawValueDesc` rather than `(messages, nodes)` — text-roundtrip closure
-- requires `unresolvedValueDescs ≡ []` (`WellFormedTextDBCAgg.unresolved-empty`),
-- so a non-empty list always indicates user-written DBC slop.

checkUnknownValueDescriptionTarget : RawValueDesc → List ValidationIssue
checkUnknownValueDescriptionTarget rvd =
  mkIssue IsWarning UnknownValueDescriptionTarget
    ("VAL_ entry: CAN ID " ++ₛ showCanIdText (RawValueDesc.canId rvd)
     ++ₛ ", signal '" ++ₛ nameStr (RawValueDesc.signalName rvd)
     ++ₛ "' not found (no message with this CAN ID has a signal with this name)")
  ∷ []

checkAllUnknownValueDescriptionTargets : List RawValueDesc → List ValidationIssue
checkAllUnknownValueDescriptionTargets = concatMap checkUnknownValueDescriptionTarget

-- ============================================================================
-- CHECK 24: MULTI-VALUE MUX SELECTOR
-- ============================================================================
-- Warning-class mirror of the text-round-trip checker's `wfps` diagnostic:
-- a signal multiplexed on more than one selector value loads and streams
-- fine, but `.dbc` text cannot express it (the SG_ grammar carries a single
-- selector), so `formatDBCText` refuses the DBC.  The per-signal decider
-- `presenceIssue` is the SSOT, shared with `wfTextIssues`
-- (TextParser/WellFormedCheck/Foundations.agda documents the condition; the
-- E.3 tightness header lives in TextParser/WellFormedCheck.agda); this
-- lifting is the validator's only contribution.  Warning severity: the shape
-- is fully usable for streaming — only the text round-trip is off the table.

checkAllMultiValueMuxSelectors : List DBCMessage → List ValidationIssue
checkAllMultiValueMuxSelectors = concatMap λ msg →
  concatMap presenceIssue (DBCMessage.signals msg)

-- ============================================================================
-- CHECK 25: MUX MASTER INCOHERENT
-- ============================================================================
-- Warning-class mirror of the text-round-trip checker's `mc` diagnostic:
-- a message whose multiplexing is incoherent — no single `Always` master, or
-- a `When` selector naming a different master (the split-master shape loads
-- error-free: CHECK 4 sees each named master present, CHECK 5 sees no cycle).
-- `.dbc` text keeps only one `M` marker, so re-parse would rebind every slave
-- to that master and `formatDBCText` refuses the DBC.  The per-message
-- decider `mcIssue` is the SSOT, shared with `wfTextIssues`; same
-- warning-severity rationale as CHECK 24.

checkAllMuxMasterIncoherent : List DBCMessage → List ValidationIssue
checkAllMuxMasterIncoherent = concatMap λ msg →
  mcIssue (DBCMessage.signals msg)
