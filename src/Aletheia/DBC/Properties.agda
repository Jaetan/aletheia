{-# OPTIONS --safe --without-K #-}

-- Correctness properties for DBC types and validation.
--
-- Purpose: Define and prove properties of DBC structures and validation.
-- Properties: Bounded values (IDs, start bits, lengths), well-formedness, range consistency.
-- Role: Runtime validation properties; full soundness proofs deferred to Phase 3.
--
-- Status: Runtime semantic checks implemented (signal overlap, range validation).
-- Note: YAML parser removed in Phase 2B (JSON-only protocol).
module Aletheia.DBC.Properties where

open import Aletheia.DBC.Types
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Data.List using (List; []; _∷_; all)
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (Bool; _∧_)
open import Data.Rational using (ℚ; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

-- ============================================================================
-- BASIC STRUCTURAL PROPERTIES
-- ============================================================================

-- Property: Parsed signal start bits are always bounded
startBit-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.startBit (DBCSignal.signalDef sig)) < 64
startBit-bounded sig = toℕ<n (SignalDef.startBit (DBCSignal.signalDef sig))
  where
    open import Data.Fin.Properties using (toℕ<n)

-- Property: Parsed signal bit lengths are always bounded
bitLength-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.bitLength (DBCSignal.signalDef sig)) ≤ 64
bitLength-bounded sig = ≤-pred (toℕ<n (SignalDef.bitLength (DBCSignal.signalDef sig)))
  where
    open import Data.Fin.Properties using (toℕ<n)
    open import Data.Nat.Properties using (≤-pred)

-- Property: Parsed message IDs are valid CAN IDs
messageId-bounded : ∀ (msg : DBCMessage) → toℕ (DBCMessage.id msg) < 2048
messageId-bounded msg = toℕ<n (DBCMessage.id msg)
  where
    open import Data.Fin.Properties using (toℕ<n)

-- Property: Parsed DLC values are valid
dlc-bounded : ∀ (msg : DBCMessage) → toℕ (DBCMessage.dlc msg) ≤ 8
dlc-bounded msg = ≤-pred (toℕ<n (DBCMessage.dlc msg))
  where
    open import Data.Fin.Properties using (toℕ<n)
    open import Data.Nat.Properties using (≤-pred)

-- ============================================================================
-- RUNTIME VALIDATION PROPERTIES
-- ============================================================================

-- Property: Signal value ranges are consistent (minimum ≤ maximum)
-- This is a runtime check since we can't prove it statically without
-- constraints in the parser
signal-ranges-consistent : DBCSignal → Bool
signal-ranges-consistent sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in minimum ≤ᵇ maximum

-- Check all signals in a message have consistent ranges
message-ranges-consistent : DBCMessage → Bool
message-ranges-consistent msg =
  Data.List.all signal-ranges-consistent (DBCMessage.signals msg)
  where
    open import Data.List using (all)

-- Check all messages in a DBC have consistent ranges
dbc-ranges-consistent : DBC → Bool
dbc-ranges-consistent dbc =
  Data.List.all message-ranges-consistent (DBC.messages dbc)
  where
    open import Data.List using (all)

-- ============================================================================
-- VALIDATION INVARIANTS
-- ============================================================================

-- Helper: Check if a signal is well-formed
signal-well-formed : DBCSignal → Bool
signal-well-formed sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in (toℕ startBit Data.Nat.<ᵇ 64) ∧
     (toℕ bitLength Data.Nat.≤ᵇ 64) ∧
     (minimum Data.Rational.≤ᵇ maximum)
  where
    open import Data.Nat using (_<ᵇ_; _≤ᵇ_)

-- Helper: Check if a message is well-formed
message-well-formed : DBCMessage → Bool
message-well-formed msg =
  (toℕ (DBCMessage.dlc msg) Data.Nat.≤ᵇ 8) ∧
  Data.List.all signal-well-formed (DBCMessage.signals msg)
  where
    open import Data.Nat using (_≤ᵇ_)
    open import Data.List using (all)

-- If a DBC parses successfully, all its structural properties hold
dbc-well-formed : DBC → Bool
dbc-well-formed dbc =
  dbc-ranges-consistent dbc ∧
  Data.List.all message-well-formed (DBC.messages dbc)
  where
    open import Data.List using (all)

-- ============================================================================
-- FUTURE PROOF OBLIGATIONS (Phase 3+)
-- ============================================================================

{- TODO Phase 3: Formal DBC validation proofs

   Define formal validation properties and prove:

   1. Well-formedness preservation: Valid JSON → parsed DBC is well-formed
   2. Signal extraction correctness: Extracted values match signal definitions
   3. Range validation: Signal values within min/max bounds

   Phase 5: Pretty-printer and round-trip properties
   - Implement: printDBC : DBC → JSON
   - Prove: parse ∘ print ≡ id (for well-formed DBCs)
-}
