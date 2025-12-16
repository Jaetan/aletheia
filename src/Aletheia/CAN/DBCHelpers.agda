{-# OPTIONS --safe --without-K #-}

-- Shared DBC lookup and comparison utilities.
--
-- Purpose: Centralize common DBC operations to eliminate duplication.
-- Operations: canIdEquals, findMessageById, findSignalByName.
-- Role: Shared utilities for CAN.SignalExtraction and CAN.BatchFrameBuilding.
--
-- Design: All functions use Bool predicates for runtime efficiency.
module Aletheia.CAN.DBCHelpers where

open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_≡ᵇ_)
open import Data.Fin using (toℕ)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (findByPredicate)

-- ============================================================================
-- CAN ID COMPARISON
-- ============================================================================

-- Check if two CAN IDs are equal
-- Standard IDs only match other Standard IDs with same value
-- Extended IDs only match other Extended IDs with same value
canIdEquals : CANId → CANId → Bool
canIdEquals (Standard x) (Standard y) = toℕ x ≡ᵇ toℕ y
canIdEquals (Extended x) (Extended y) = toℕ x ≡ᵇ toℕ y
canIdEquals _ _ = false

-- ============================================================================
-- DBC MESSAGE LOOKUP
-- ============================================================================

-- Find message by CAN ID in DBC
-- Returns first message whose ID matches (DBC should have unique IDs)
findMessageById : CANId → DBC → Maybe DBCMessage
findMessageById msgId dbc = findByPredicate matchesId (DBC.messages dbc)
  where
    matchesId : DBCMessage → Bool
    matchesId msg = canIdEquals msgId (DBCMessage.id msg)

-- ============================================================================
-- SIGNAL LOOKUP
-- ============================================================================

-- Find signal by name in a message
-- Returns first signal whose name matches (DBC should have unique names per message)
findSignalByName : String → DBCMessage → Maybe DBCSignal
findSignalByName name msg = findByPredicate matchesName (DBCMessage.signals msg)
  where
    matchesName : DBCSignal → Bool
    matchesName sig = ⌊ DBCSignal.name sig ≟ name ⌋
