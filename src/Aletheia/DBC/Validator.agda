{-# OPTIONS --safe --without-K #-}

-- DBC structural validator: comprehensive issue reporting.
--
-- Purpose: Detect all structural issues in a DBC definition in a single pass,
-- returning every issue found (not stopping at the first).
-- Does NOT replace JSONParser validation (parse errors are separate).
-- Role: Used by Protocol.StreamState to handle validateDBC commands.
--
-- Checks (IsError):
--   1. duplicate_message_id           - Two messages share the same CAN ID
--   2. duplicate_signal_name          - Two signals in one message share a name
--   3. factor_zero                    - Signal factor numerator is zero
--   4. multiplexor_not_found          - Multiplexor signal referenced but absent
--   5. multiplexor_not_always_present - Multiplexor signal is itself multiplexed
-- Checks (IsWarning):
--   6. global_name_collision          - Same signal name in two different messages
--   7. min_exceeds_max                - Signal minimum > maximum
--
-- Design: Uses decidable types (Dec) for all comparisons, following the
-- convention in DBC/Properties.agda. No raw Bool via ⌊_⌋.
module Aletheia.DBC.Validator where

open import Aletheia.DBC.Types
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_; map; filter; concatMap)
  renaming (_++_ to _++ₗ_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.String.Properties using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ₙ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_)
open import Data.Integer using (ℤ; +_)
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

checkDuplicateSignalNamesInMsg : DBCMessage → List ValidationIssue
checkDuplicateSignalNamesInMsg msg = go (DBCMessage.signals msg)
  where
    msgName : String
    msgName = DBCMessage.name msg
    go : List DBCSignal → List ValidationIssue
    go []           = []
    go (sig ∷ rest) = checkDupSigAgainstList msgName sig rest ++ₗ go rest

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
... | no  _ = mkIssue IsError MinExceedsMax
                ("Message '" ++ₛ msgName ++ₛ "', signal '"
                 ++ₛ DBCSignal.name sig
                 ++ₛ "': minimum exceeds maximum") ∷ []

checkAllMinMax : List DBCMessage → List ValidationIssue
checkAllMinMax [] = []
checkAllMinMax (msg ∷ rest) =
  concatMap (checkMinMaxSig (DBCMessage.name msg)) (DBCMessage.signals msg)
  ++ₗ checkAllMinMax rest

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

-- ============================================================================
-- UTILITIES (used by StreamState for dual-layer validation)
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
