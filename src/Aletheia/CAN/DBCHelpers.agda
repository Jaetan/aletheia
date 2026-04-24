{-# OPTIONS --safe --without-K #-}

-- Shared DBC lookup and comparison utilities.
--
-- Purpose: Centralize common DBC operations to eliminate duplication.
-- Operations: canIdEquals, findMessageById, findSignalByName, findSignalInList.
-- Role: Shared utilities for CAN.SignalExtraction and CAN.BatchFrameBuilding.
--
-- Design: All functions use Bool predicates for runtime efficiency.
module Aletheia.CAN.DBCHelpers where

open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)
open import Aletheia.DBC.Identifier using (Identifier)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Aletheia.Prelude using (findByPredicate; T-irrelevant)

-- ============================================================================
-- CAN ID COMPARISON
-- ============================================================================

-- Decidable CANId equality (canonical definition).
-- After establishing ℕ equality, T-irrelevant closes the proof field.
_≟-CANId_ : (id₁ id₂ : CANId) → Dec (id₁ ≡ id₂)
Standard x p ≟-CANId Standard y q with x ≟ y
... | yes refl = yes (cong (Standard x) (T-irrelevant p q))
... | no  x≢y  = no λ { refl → x≢y refl }
Extended x p ≟-CANId Extended y q with x ≟ y
... | yes refl = yes (cong (Extended x) (T-irrelevant p q))
... | no  x≢y  = no λ { refl → x≢y refl }
Standard _ _ ≟-CANId Extended _ _ = no λ ()
Extended _ _ ≟-CANId Standard _ _ = no λ ()

-- Bool equality: direct ℕ field comparison, no Dec allocation.
canIdEquals : CANId → CANId → Bool
canIdEquals (Standard x _) (Standard y _) = x ≡ᵇ y
canIdEquals (Extended x _) (Extended y _) = x ≡ᵇ y
canIdEquals _ _ = false

-- ============================================================================
-- DBC MESSAGE LOOKUP
-- ============================================================================

-- Find message by CAN ID in DBC (O(n) linear scan)
-- Returns first message whose ID matches (DBC should have unique IDs)
findMessageById : CANId → DBC → Maybe DBCMessage
findMessageById msgId dbc = findByPredicate matchesId (DBC.messages dbc)
  where
    matchesId : DBCMessage → Bool
    matchesId msg = canIdEquals msgId (DBCMessage.id msg)

-- ============================================================================
-- SIGNAL LOOKUP
-- ============================================================================

-- Find signal by name in a signal list (O(n) linear scan, decidable equality)
-- Used by DBC validator for multiplexor lookup on collected signal lists.
--
-- Deferred Bool fast path (AA-16.2): the `_≟ₛ_` Dec call below allocates a
-- yes/no heap cell per comparison on every signal extraction and frame build
-- (this is a hot-path function via SignalExtraction and BatchFrameBuilding).
-- Two refactors are technically possible but both blocked:
--   (a) `Data.String._==_` from the stdlib is defined as `isYes (s₁ ≟ s₂)`
--       (Data/String/Properties.agda:167) — same Dec allocation cost, just
--       wrapped. No throughput gain.
--   (b) `Agda.Builtin.String.primStringEquality` is the only path to a true
--       Bool (compiled directly to Haskell `Text` `==`), but it gives back
--       neither a `Dec` nor a propositional-equality witness. Routing it
--       through the proof callers (SignalExtraction/Properties.agda) is
--       fine because those proofs match on the `Maybe DBCSignal` *result*,
--       not on the internal Dec; but
--       the `_≟ₛ_` call appears in a `with` whose `yes`/`no` cases are
--       structurally examined by `findSignalInList`'s own definition, and
--       a Bool fast path forfeits the propositional-equality bridge that
--       Cache.agda's `updateEntries-All-neq` (line 81) and similar `yes refl`
--       patterns rely on. A complete Prelude-level Bool primitive plus a
--       postulated `prim-string-eq-sound : primStringEquality a b ≡ true → a ≡ b`
--       would unblock this — but the postulate breaks `--safe`.
-- Left as-is pending a separate Prelude design decision about whether to
-- introduce a `*.Unsafe.agda` module for the soundness postulate, or wait
-- for stdlib to expose a Bool-valued `_≟ᵇ_ : String → String → Bool` with
-- a real proof bridge. (See Cache.agda for the same blocker.)
findSignalInList : String → List DBCSignal → Maybe DBCSignal
findSignalInList _ [] = nothing
findSignalInList name (s ∷ ss) with name ≟ₛ signalNameStr s
... | yes _ = just s
... | no  _ = findSignalInList name ss

-- Find signal by name in a message (O(n) linear scan)
-- Returns first signal whose name matches (DBC should have unique names per message)
findSignalByName : String → DBCMessage → Maybe DBCSignal
findSignalByName name msg = findSignalInList name (DBCMessage.signals msg)
