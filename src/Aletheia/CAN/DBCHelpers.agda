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
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.Identifier using (Identifier; _≡csᵇ_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Aletheia.Prelude using (findByPredicate)

-- ============================================================================
-- CAN ID COMPARISON
-- ============================================================================

-- Decidable CANId equality (canonical definition).
-- Proof fields are `.(…)` irrelevant (see CAN/Frame.agda), so ℕ equality alone
-- closes — `Standard n p₁ ≡ Standard n p₂` holds definitionally.
_≟-CANId_ : (id₁ id₂ : CANId) → Dec (id₁ ≡ id₂)
Standard x _ ≟-CANId Standard y _ with x ≟ y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }
Extended x _ ≟-CANId Extended y _ with x ≟ y
... | yes refl = yes refl
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

-- Find signal by name in a signal list (O(n) linear scan, Bool fast path)
-- Used by DBC validator for multiplexor lookup on collected signal lists.
--
-- Bool fast path (`_≡csᵇ_ : List Char → List Char → Bool`) avoids the
-- per-call `Dec` heap cell that `≡-dec _≟ᶜ_` would allocate on every
-- signal extraction and frame build. Soundness/completeness for the
-- case-split (used by `findSignalInList→SigPresent` in
-- `Protocol/Adequacy/StreamingWarm.agda`) is handled by
-- `Identifier.{≡csᵇ-sound, ≡csᵇ-false→≢}` at proof sites — all `--safe`,
-- no `prim-string-eq-sound` postulate.
findSignalInList : List Char → List DBCSignal → Maybe DBCSignal
findSignalInList _ [] = nothing
findSignalInList name (s ∷ ss) =
  if name ≡csᵇ Identifier.name (DBCSignal.name s)
  then just s
  else findSignalInList name ss
  where open import Data.Bool using (if_then_else_)

-- Find signal by name in a message (O(n) linear scan)
-- Returns first signal whose name matches (DBC should have unique names per message)
findSignalByName : List Char → DBCMessage → Maybe DBCSignal
findSignalByName name msg = findSignalInList name (DBCMessage.signals msg)
