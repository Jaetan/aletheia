-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
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
open import Data.Bool using (Bool; T; false)
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (_≟_; ≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Reflects using (ofⁿ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Aletheia.Prelude using (findByPredicate)

open import Aletheia.Data.Dec0 using (Dec₀; fromBridges; dec₀; does₀)

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

-- Self-certifying Bool equality: `does₀` is the direct ℕ field comparison
-- (no Dec allocation); the erased certificate pins it to propositional CANId
-- equality (the `.(…)`-irrelevant proof fields collapse definitionally, so ℕ
-- equality alone closes each constructor case).  MAlonzo erases the
-- certificate (Dec₀ is a newtype over Bool).
canIdEquals₀ : (id₁ id₂ : CANId) → Dec₀ (id₁ ≡ id₂)
canIdEquals₀ (Standard x p) (Standard y q) = fromBridges (x ≡ᵇ y) sound complete
  where
    @0 sound : T (x ≡ᵇ y) → Standard x p ≡ Standard y q
    sound t with ≡ᵇ⇒≡ x y t
    ... | refl = refl

    @0 complete : Standard x p ≡ Standard y q → T (x ≡ᵇ y)
    complete refl = ≡⇒≡ᵇ x x refl
canIdEquals₀ (Extended x p) (Extended y q) = fromBridges (x ≡ᵇ y) sound complete
  where
    @0 sound : T (x ≡ᵇ y) → Extended x p ≡ Extended y q
    sound t with ≡ᵇ⇒≡ x y t
    ... | refl = refl

    @0 complete : Extended x p ≡ Extended y q → T (x ≡ᵇ y)
    complete refl = ≡⇒≡ᵇ x x refl
canIdEquals₀ (Standard _ _) (Extended _ _) = dec₀ false (ofⁿ λ ())
canIdEquals₀ (Extended _ _) (Standard _ _) = dec₀ false (ofⁿ λ ())

-- Bool equality — definitional projection of `canIdEquals₀` (runtime shape
-- unchanged: direct ℕ field comparison per constructor case).
canIdEquals : CANId → CANId → Bool
canIdEquals id₁ id₂ = does₀ (canIdEquals₀ id₁ id₂)

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
-- case-split (consumed by the cache-correctness proofs in
-- `Protocol/FrameProcessor/Properties/Cache.agda` and the membership
-- machinery in `Protocol/Adequacy/StreamingWarm.agda`) is handled by
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
