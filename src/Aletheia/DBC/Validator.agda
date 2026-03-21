{-# OPTIONS --safe --without-K #-}

-- DBC structural validator: comprehensive issue reporting.
--
-- Purpose: Detect all structural issues in a DBC definition in a single pass,
-- returning every issue found (not stopping at the first).
-- Does NOT replace JSONParser validation (parse errors are separate).
-- Role: Used by Protocol.StreamState to handle validateDBC commands.
--
-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITION: A DBC is "valid" if and only if:
--
--  (a) Every CAN ID is unique across all messages.
--  (b) Signal names are unique within each message.
--  (c) No signal has factor = 0.
--  (d) Every multiplexor reference resolves to an always-present signal.
--  (e) Signal names are globally unique across messages (advisory).
--  (f) For every signal, minimum ≤ maximum.
--  (g) Every signal's bit range fits within its message's DLC × 8 bits.
--      - LE: startBit + bitLength ≤ dlc × 8.
--      - BE: the highest original byte (7 − startBit / 8) < dlc.
--        (Extraction reverses the payload, so reversed byte startBit/8
--         maps to original byte 7 − startBit/8.)
--  (h) Coexisting signals do not share bit positions (linear model).
--  (i) No signal has bitLength = 0.
--  (j) DLC ∈ [0, 8].
--  (k) The declared [minimum, maximum] contains the physical range
--      reachable by factor/offset/bitLength/signedness.
--      Unsigned n-bit: raw ∈ [0, 2^n − 1].
--      Signed   n-bit: raw ∈ [−2^(n−1), 2^(n−1) − 1].
--      Physical = raw × factor + offset; if factor < 0, range inverts.
--  (l) Messages without signals are flagged (advisory).
--  (m) Message names are unique (advisory).
--  (n) startBit < 64 and bitLength ≤ 64 (defense-in-depth, enforced
--      by the JSON parser via % 64 / % 65).
-- ═══════════════════════════════════════════════════════════════════════
--
-- Checks (IsError):
--   1. duplicate_message_id           - Violates (a)
--   2. duplicate_signal_name          - Violates (b)
--   3. factor_zero                    - Violates (c)
--   4. multiplexor_not_found          - Violates (d)
--   5. multiplexor_not_always_present - Violates (d)
--   8. signal_exceeds_dlc             - Violates (g)
--   9. signal_overlap                 - Violates (h)
--  10. bit_length_zero                - Violates (i)
--  12. dlc_out_of_range               - Violates (j), defense-in-depth
-- Checks (IsWarning):
--   6. global_name_collision          - Violates (e)
--   7. min_exceeds_max                - Violates (f)
--  11. duplicate_message_name         - Violates (m)
--  13. offset_scale_range             - Violates (k)
--  14. empty_message                  - Violates (l)
--  15. start_bit_out_of_range         - Violates (n), defense-in-depth
--  16. bit_length_excessive           - Violates (n), defense-in-depth
--
-- Design: Uses decidable types (Dec) for all comparisons, following the
-- convention in DBC/Properties.agda. No raw Bool via ⌊_⌋.
module Aletheia.DBC.Validator where

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When; ValidationIssue; mkIssue; IssueSeverity; IsError; IsWarning; IssueCode; DuplicateMessageId; DuplicateSignalName; FactorZero; MultiplexorNotFound; MultiplexorNotAlwaysPresent; GlobalNameCollision; MinExceedsMax; SignalExceedsDLC; SignalOverlap; BitLengthZero; DuplicateMessageName; DLCOutOfRange; OffsetScaleRange; EmptyMessage; StartBitOutOfRange; BitLengthExcessive)
open import Aletheia.DBC.Properties using (signalPairValid?)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Data.List using (List; []; _∷_; map; filter; concatMap)
  renaming (_++_ to _++ₗ_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _∸_; suc; pred; _/_)
open import Data.Nat.Properties using (_≤?_; _<?_) renaming (_≟_ to _≟ₙ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)
open import Aletheia.Protocol.JSON using (ℕtoℚ)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

-- ============================================================================
-- DECIDABLE HELPERS
-- ============================================================================

-- Decidable CANId equality
_≟-CANId_ : (id₁ id₂ : CANId) → Relation.Nullary.Dec (id₁ ≡ id₂)
CANId.Standard x ≟-CANId CANId.Standard y with x ≟ₙ y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }
CANId.Extended x ≟-CANId CANId.Extended y with x ≟ₙ y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }
CANId.Standard _ ≟-CANId CANId.Extended _ = no λ ()
CANId.Extended _ ≟-CANId CANId.Standard _ = no λ ()

-- Find presence of a named signal (Maybe-returning lookup via Dec)
findSignalPresence : String → List DBCSignal → Maybe SignalPresence
findSignalPresence name [] = nothing
findSignalPresence name (sig ∷ rest) with DBCSignal.name sig ≟ name
... | yes _ = just (DBCSignal.presence sig)
... | no  _ = findSignalPresence name rest

-- ============================================================================
-- CHECK 1: DUPLICATE MESSAGE IDs
-- ============================================================================

checkDupIdPair : DBCMessage → DBCMessage → List ValidationIssue
checkDupIdPair m1 m2 with DBCMessage.id m1 ≟-CANId DBCMessage.id m2
... | yes _ = mkIssue IsError DuplicateMessageId
                ("Messages '" ++ₛ DBCMessage.name m1 ++ₛ "' and '"
                 ++ₛ DBCMessage.name m2 ++ₛ "' share the same CAN ID") ∷ []
... | no  _ = []

checkDupIdAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkDupIdAgainstList _ [] = []
checkDupIdAgainstList m (other ∷ rest) =
  checkDupIdPair m other ++ₗ checkDupIdAgainstList m rest

checkDuplicateMessageIds : List DBCMessage → List ValidationIssue
checkDuplicateMessageIds [] = []
checkDuplicateMessageIds (m ∷ rest) =
  checkDupIdAgainstList m rest ++ₗ checkDuplicateMessageIds rest

-- ============================================================================
-- CHECK 2: DUPLICATE SIGNAL NAMES (within a message)
-- ============================================================================

checkDupSigPair : String → DBCSignal → DBCSignal → List ValidationIssue
checkDupSigPair msgName s1 s2 with DBCSignal.name s1 ≟ DBCSignal.name s2
... | yes _ = mkIssue IsError DuplicateSignalName
                ("Message '" ++ₛ msgName ++ₛ "': duplicate signal name '"
                 ++ₛ DBCSignal.name s1 ++ₛ "'") ∷ []
... | no  _ = []

checkDupSigAgainstList : String → DBCSignal → List DBCSignal → List ValidationIssue
checkDupSigAgainstList _ _ [] = []
checkDupSigAgainstList msgName sig (other ∷ rest) =
  checkDupSigPair msgName sig other ++ₗ checkDupSigAgainstList msgName sig rest

checkDupSigTriangular : String → List DBCSignal → List ValidationIssue
checkDupSigTriangular _ []           = []
checkDupSigTriangular msgName (sig ∷ rest) =
  checkDupSigAgainstList msgName sig rest ++ₗ checkDupSigTriangular msgName rest

checkDuplicateSignalNamesInMsg : DBCMessage → List ValidationIssue
checkDuplicateSignalNamesInMsg msg =
  checkDupSigTriangular (DBCMessage.name msg) (DBCMessage.signals msg)

checkAllDuplicateSignalNames : List DBCMessage → List ValidationIssue
checkAllDuplicateSignalNames [] = []
checkAllDuplicateSignalNames (msg ∷ rest) =
  checkDuplicateSignalNamesInMsg msg ++ₗ checkAllDuplicateSignalNames rest

-- ============================================================================
-- CHECK 3: FACTOR ZERO
-- ============================================================================

checkFactorZeroSig : String → DBCSignal → List ValidationIssue
checkFactorZeroSig msgName sig
  with ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≟ℤ (+ 0)
... | yes _ = mkIssue IsError FactorZero
                ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                 ++ₛ "': factor is zero (constant-zero signal)") ∷ []
... | no  _ = []

checkAllFactorZero : List DBCMessage → List ValidationIssue
checkAllFactorZero [] = []
checkAllFactorZero (msg ∷ rest) =
  concatMap (checkFactorZeroSig (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllFactorZero rest

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
checkAllMuxFound [] = []
checkAllMuxFound (msg ∷ rest) =
  let sigs    = DBCMessage.signals msg
      msgName = DBCMessage.name msg
  in concatMap (checkMuxFoundSig msgName sigs) sigs
     ++ₗ checkAllMuxFound rest

-- ============================================================================
-- CHECK 5: MULTIPLEXOR NOT ALWAYS PRESENT
-- ============================================================================

checkMuxAlwaysPresentSig : String → List DBCSignal → DBCSignal → List ValidationIssue
checkMuxAlwaysPresentSig msgName allSigs sig with DBCSignal.presence sig
... | Always        = []
... | When muxName _ with findSignalPresence muxName allSigs
...   | nothing          = []  -- already caught by check 4
...   | just Always      = []
...   | just (When _ _)  = mkIssue IsError MultiplexorNotAlwaysPresent
                             ("Message '" ++ₛ msgName ++ₛ "', signal '"
                              ++ₛ DBCSignal.name sig ++ₛ "': multiplexor '"
                              ++ₛ muxName
                              ++ₛ "' is itself conditionally present") ∷ []

checkAllMuxAlwaysPresent : List DBCMessage → List ValidationIssue
checkAllMuxAlwaysPresent [] = []
checkAllMuxAlwaysPresent (msg ∷ rest) =
  let sigs    = DBCMessage.signals msg
      msgName = DBCMessage.name msg
  in concatMap (checkMuxAlwaysPresentSig msgName sigs) sigs
     ++ₗ checkAllMuxAlwaysPresent rest

-- ============================================================================
-- CHECK 6: GLOBAL NAME COLLISION (same signal name in different messages)
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
checkGlobalNameAgainstList _ [] = []
checkGlobalNameAgainstList m (other ∷ rest) =
  checkGlobalNamePair m other ++ₗ checkGlobalNameAgainstList m rest

checkAllGlobalNameCollisions : List DBCMessage → List ValidationIssue
checkAllGlobalNameCollisions [] = []
checkAllGlobalNameCollisions (m ∷ rest) =
  checkGlobalNameAgainstList m rest ++ₗ checkAllGlobalNameCollisions rest

-- ============================================================================
-- CHECK 7: MIN EXCEEDS MAX
-- ============================================================================

checkMinMaxSig : String → DBCSignal → List ValidationIssue
checkMinMaxSig msgName sig
  with SignalDef.minimum (DBCSignal.signalDef sig) ≤?ᵣ
       SignalDef.maximum (DBCSignal.signalDef sig)
... | yes _ = []
... | no  _ = mkIssue IsWarning MinExceedsMax
                ("Message '" ++ₛ msgName ++ₛ "', signal '"
                 ++ₛ DBCSignal.name sig
                 ++ₛ "': minimum exceeds maximum") ∷ []

checkAllMinMax : List DBCMessage → List ValidationIssue
checkAllMinMax [] = []
checkAllMinMax (msg ∷ rest) =
  concatMap (checkMinMaxSig (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllMinMax rest

-- ============================================================================
-- CHECK 8: SIGNAL EXCEEDS DLC
-- ============================================================================

checkSignalExceedsDLC-LE : String → ℕ → DBCSignal → List ValidationIssue
checkSignalExceedsDLC-LE msgName dlc sig
  with SignalDef.startBit (DBCSignal.signalDef sig) + SignalDef.bitLength (DBCSignal.signalDef sig) ≤? dlc * 8
... | yes _ = []
... | no  _ = mkIssue IsError SignalExceedsDLC
                ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                 ++ₛ "': bit range exceeds DLC") ∷ []

-- Big-endian extraction does swapBytes (reverse) then extractBits at startBit.
-- Reversed byte startBit/8 maps to original byte 7 - startBit/8.
-- The highest original byte accessed is 7 - startBit/8; must be < dlc.
checkSignalExceedsDLC-BE : String → ℕ → DBCSignal → List ValidationIssue
checkSignalExceedsDLC-BE msgName dlc sig
  with suc (7 ∸ (SignalDef.startBit (DBCSignal.signalDef sig) / 8)) ≤? dlc
... | yes _ = []
... | no  _ = mkIssue IsError SignalExceedsDLC
                ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                 ++ₛ "': bit range exceeds DLC") ∷ []

checkSignalExceedsDLC : String → ℕ → DBCSignal → List ValidationIssue
checkSignalExceedsDLC msgName dlc sig with DBCSignal.byteOrder sig
... | LittleEndian = checkSignalExceedsDLC-LE msgName dlc sig
... | BigEndian    = checkSignalExceedsDLC-BE msgName dlc sig

checkAllSignalExceedsDLC : List DBCMessage → List ValidationIssue
checkAllSignalExceedsDLC [] = []
checkAllSignalExceedsDLC (msg ∷ rest) =
  concatMap (checkSignalExceedsDLC (DBCMessage.name msg) (DBCMessage.dlc msg))
            (DBCMessage.signals msg)
  ++ₗ checkAllSignalExceedsDLC rest

-- ============================================================================
-- CHECK 9: SIGNAL OVERLAP
-- ============================================================================

checkOverlapPair : String → DBCSignal → DBCSignal → List ValidationIssue
checkOverlapPair msgName s1 s2 with signalPairValid? s1 s2
... | yes _ = []
... | no  _ = mkIssue IsError SignalOverlap
                ("Message '" ++ₛ msgName ++ₛ "', signals '" ++ₛ DBCSignal.name s1
                 ++ₛ "' and '" ++ₛ DBCSignal.name s2 ++ₛ "' overlap") ∷ []

checkOverlapAgainstList : String → DBCSignal → List DBCSignal → List ValidationIssue
checkOverlapAgainstList _ _ [] = []
checkOverlapAgainstList msgName sig (other ∷ rest) =
  checkOverlapPair msgName sig other ++ₗ checkOverlapAgainstList msgName sig rest

checkOverlapTriangular : String → List DBCSignal → List ValidationIssue
checkOverlapTriangular _ []           = []
checkOverlapTriangular msgName (sig ∷ rest) =
  checkOverlapAgainstList msgName sig rest ++ₗ checkOverlapTriangular msgName rest

checkOverlapsInMsg : DBCMessage → List ValidationIssue
checkOverlapsInMsg msg =
  checkOverlapTriangular (DBCMessage.name msg) (DBCMessage.signals msg)

checkAllSignalOverlaps : List DBCMessage → List ValidationIssue
checkAllSignalOverlaps [] = []
checkAllSignalOverlaps (msg ∷ rest) =
  checkOverlapsInMsg msg ++ₗ checkAllSignalOverlaps rest

-- ============================================================================
-- CHECK 10: BIT LENGTH ZERO
-- ============================================================================

checkBitLengthZero : String → DBCSignal → List ValidationIssue
checkBitLengthZero msgName sig with SignalDef.bitLength (DBCSignal.signalDef sig) ≟ₙ 0
... | yes _ = mkIssue IsError BitLengthZero
                ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                 ++ₛ "': bit length is zero") ∷ []
... | no  _ = []

checkAllBitLengthZero : List DBCMessage → List ValidationIssue
checkAllBitLengthZero [] = []
checkAllBitLengthZero (msg ∷ rest) =
  concatMap (checkBitLengthZero (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllBitLengthZero rest

-- ============================================================================
-- CHECK 11: DUPLICATE MESSAGE NAME
-- ============================================================================

checkDupNamePair : DBCMessage → DBCMessage → List ValidationIssue
checkDupNamePair m1 m2 with DBCMessage.name m1 ≟ DBCMessage.name m2
... | yes _ = mkIssue IsWarning DuplicateMessageName
                ("Messages '" ++ₛ DBCMessage.name m1 ++ₛ "' and '"
                 ++ₛ DBCMessage.name m2 ++ₛ "' share the same name") ∷ []
... | no  _ = []

checkDupNameAgainstList : DBCMessage → List DBCMessage → List ValidationIssue
checkDupNameAgainstList _ [] = []
checkDupNameAgainstList m (other ∷ rest) =
  checkDupNamePair m other ++ₗ checkDupNameAgainstList m rest

checkDuplicateMessageNames : List DBCMessage → List ValidationIssue
checkDuplicateMessageNames [] = []
checkDuplicateMessageNames (m ∷ rest) =
  checkDupNameAgainstList m rest ++ₗ checkDuplicateMessageNames rest

-- ============================================================================
-- CHECK 12: DLC OUT OF RANGE
-- Defense-in-depth: the DBC JSON parser rejects DLC > 8 at parse time,
-- so this check cannot fire through the validateDBC API.  Retained for
-- programmatically-constructed DBC values that bypass the parser.
-- ============================================================================

checkDLCOutOfRange : DBCMessage → List ValidationIssue
checkDLCOutOfRange msg with DBCMessage.dlc msg ≤? 8
... | yes _ = []
... | no  _ = mkIssue IsError DLCOutOfRange
                ("Message '" ++ₛ DBCMessage.name msg
                 ++ₛ "': DLC exceeds maximum of 8") ∷ []

checkAllDLCOutOfRange : List DBCMessage → List ValidationIssue
checkAllDLCOutOfRange = concatMap checkDLCOutOfRange

-- ============================================================================
-- CHECK 13: OFFSET/SCALE RANGE
-- ============================================================================

-- Physical value = raw × factor + offset.
-- Unsigned n-bit: raw ∈ [0, 2^n − 1].
-- Signed n-bit (two's complement): raw ∈ [−2^(n−1), 2^(n−1) − 1].
-- If factor < 0 the physical range is inverted (physA > physB).
-- Check: the physical range [physMin, physMax] must contain [declaredMin, declaredMax].

-- Embed ℤ into ℚ
ℤtoℚ : ℤ → ℚ
ℤtoℚ z = z /ᵣ 1

-- True when the ℚ numerator is negative
isNegativeℚ : ℚ → Bool
isNegativeℚ q with ℚ.numerator q
... | (+ _)     = false
... | (-[1+ _ ]) = true

checkRangeLow : String → String → ℚ → ℚ → List ValidationIssue
checkRangeLow msgName sigName physMin declaredMin with declaredMin ≤?ᵣ physMin
... | yes _ = []
... | no  _ = mkIssue IsWarning OffsetScaleRange
                ("Message '" ++ₛ msgName ++ₛ "', signal '"
                 ++ₛ sigName
                 ++ₛ "': declared minimum is below physical range") ∷ []

checkRangeHigh : String → String → ℚ → ℚ → List ValidationIssue
checkRangeHigh msgName sigName physMax declaredMax with physMax ≤?ᵣ declaredMax
... | yes _ = []
... | no  _ = mkIssue IsWarning OffsetScaleRange
                ("Message '" ++ₛ msgName ++ₛ "', signal '"
                 ++ₛ sigName
                 ++ₛ "': declared maximum is above physical range") ∷ []

-- physA = rawMin × factor + offset, physB = rawMax × factor + offset.
-- If factor ≥ 0: physMin = physA, physMax = physB.
-- If factor < 0: physMin = physB, physMax = physA.
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
checkAllOffsetScaleRange [] = []
checkAllOffsetScaleRange (msg ∷ rest) =
  concatMap (checkOffsetScaleRange (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllOffsetScaleRange rest

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
-- Defense-in-depth: the DBC JSON parser stores startBit % 64, so
-- startBit ∈ [0,63] and this check cannot fire through validateDBC.
-- ============================================================================

checkStartBitOutOfRange : String → DBCSignal → List ValidationIssue
checkStartBitOutOfRange msgName sig with SignalDef.startBit (DBCSignal.signalDef sig) <? 64
... | yes _ = []
... | no  _ = mkIssue IsWarning StartBitOutOfRange
                ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                 ++ₛ "': start bit ≥ 64") ∷ []

checkAllStartBitOutOfRange : List DBCMessage → List ValidationIssue
checkAllStartBitOutOfRange [] = []
checkAllStartBitOutOfRange (msg ∷ rest) =
  concatMap (checkStartBitOutOfRange (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllStartBitOutOfRange rest

-- ============================================================================
-- CHECK 16: BIT LENGTH EXCESSIVE
-- Defense-in-depth: the DBC JSON parser stores bitLength % 65, so
-- bitLength ∈ [0,64] and this check cannot fire through validateDBC.
-- ============================================================================

checkBitLengthExcessive : String → DBCSignal → List ValidationIssue
checkBitLengthExcessive msgName sig with SignalDef.bitLength (DBCSignal.signalDef sig) ≤? 64
... | yes _ = []
... | no  _ = mkIssue IsWarning BitLengthExcessive
                ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ DBCSignal.name sig
                 ++ₛ "': bit length exceeds 64") ∷ []

checkAllBitLengthExcessive : List DBCMessage → List ValidationIssue
checkAllBitLengthExcessive [] = []
checkAllBitLengthExcessive (msg ∷ rest) =
  concatMap (checkBitLengthExcessive (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllBitLengthExcessive rest

-- ============================================================================
-- FULL VALIDATOR
-- ============================================================================

validateDBCFull : DBC → List ValidationIssue
validateDBCFull dbc =
  let msgs = DBC.messages dbc
  in checkDuplicateMessageIds msgs
     ++ₗ checkAllDuplicateSignalNames msgs
     ++ₗ checkAllFactorZero msgs
     ++ₗ checkAllMuxFound msgs
     ++ₗ checkAllMuxAlwaysPresent msgs
     ++ₗ checkAllGlobalNameCollisions msgs
     ++ₗ checkAllMinMax msgs
     ++ₗ checkAllSignalExceedsDLC msgs
     ++ₗ checkAllSignalOverlaps msgs
     ++ₗ checkAllBitLengthZero msgs
     ++ₗ checkDuplicateMessageNames msgs
     ++ₗ checkAllDLCOutOfRange msgs
     ++ₗ checkAllOffsetScaleRange msgs
     ++ₗ checkAllEmptyMessage msgs
     ++ₗ checkAllStartBitOutOfRange msgs
     ++ₗ checkAllBitLengthExcessive msgs

-- ============================================================================
-- UTILITIES (used by StreamState and Routing)
-- ============================================================================

-- Check if any issue in a list is an error
hasAnyError : List ValidationIssue → Bool
hasAnyError []         = false
hasAnyError (i ∷ rest) with ValidationIssue.severity i
... | IsError   = true
... | IsWarning = hasAnyError rest

-- Format issue list as a single human-readable error string
formatIssuesText : List ValidationIssue → String
formatIssuesText [] = ""
formatIssuesText (i ∷ []) = ValidationIssue.detail i
formatIssuesText (i ∷ rest) = ValidationIssue.detail i ++ₛ "; " ++ₛ formatIssuesText rest

-- Filter only error-severity issues
errorIssues : List ValidationIssue → List ValidationIssue
errorIssues [] = []
errorIssues (i ∷ rest) with ValidationIssue.severity i
... | IsError   = i ∷ errorIssues rest
... | IsWarning = errorIssues rest
