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
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ₙ_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Aletheia.Prelude using (findByPredicate)

-- ============================================================================
-- CAN ID COMPARISON
-- ============================================================================

-- Decidable CANId equality (canonical definition)
_≟-CANId_ : (id₁ id₂ : CANId) → Dec (id₁ ≡ id₂)
Standard x ≟-CANId Standard y with x ≟ₙ y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }
Extended x ≟-CANId Extended y with x ≟ₙ y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }
Standard _ ≟-CANId Extended _ = no λ ()
Extended _ ≟-CANId Standard _ = no λ ()

-- Bool equality derived from decidable equality
canIdEquals : CANId → CANId → Bool
canIdEquals a b = ⌊ a ≟-CANId b ⌋

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
findSignalInList : String → List DBCSignal → Maybe DBCSignal
findSignalInList _ [] = nothing
findSignalInList name (s ∷ ss) with name ≟ DBCSignal.name s
... | yes _ = just s
... | no  _ = findSignalInList name ss

-- Find signal by name in a message (O(n) linear scan)
-- Returns first signal whose name matches (DBC should have unique names per message)
findSignalByName : String → DBCMessage → Maybe DBCSignal
findSignalByName name msg = findByPredicate matchesName (DBCMessage.signals msg)
  where
    matchesName : DBCSignal → Bool
    matchesName sig = ⌊ DBCSignal.name sig ≟ name ⌋
