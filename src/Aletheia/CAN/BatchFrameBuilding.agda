-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Batch frame building from signal index-value pairs.
--
-- Purpose: Build CAN frames from multiple signal values at once with validation.
-- Operations: buildFrameByIndex (DBC + CAN ID + index-keyed signals → FrameError ⊎ frame),
--             updateFrameByIndex (DBC + CAN ID + frame + index-keyed signals → FrameError ⊎ frame).
-- Role: Batch encoding for the binary FFI path; all language bindings resolve
-- signal names to indices client-side before calling the `*ByIndex` entry points.
--
-- Validation: Signal index bounds, signal overlap detection, multiplexing consistency.
-- Guarantees: Signals partition the frame properly (no corruption).
module Aletheia.CAN.BatchFrameBuilding where

open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.Encoding using (injectSignal)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)
open import Aletheia.DBC.Decidable using (signalPhysicalBits; Intersects; bitsIntersect₀)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary.Reflects using (ofⁿ)

open import Aletheia.Data.Dec0 using (Dec₀; dec₀; or₀; map₀; does₀)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec as Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.Prelude using (listIndex; _>>=ₑ_)
open import Aletheia.Error using
  ( FrameError; SignalIndexOOB; InjectionFailed
  ; SignalsOverlap; CANIdNotFound; CANIdMismatch
  )

-- ============================================================================
-- OVERLAP DETECTION (endianness-aware, precomputation-hoisted)
-- ============================================================================
--
-- Uses the certified `bitsIntersect₀` fast path from
-- `DBC.Decidable.Disjointness`; each fold below carries its own erased
-- Any-membership certificate, and the equivalence with `PhysicallyDisjoint`
-- is proved by `physicallyOverlapᵇ-sound` / `physicallyOverlapᵇ-complete`
-- in `DBC.Properties`, so this check is as trustworthy as the `Dec`-valued
-- `physicallyDisjoint?`.
--
-- Performance note: per-signal physical bit positions are precomputed ONCE
-- in `hasOverlaps`, outside the O(m²) pair loop. This turns the per-frame
-- cost from O(m² × l²) (with Dec-boxed per-bit comparisons, as in the
-- `physicallyDisjoint?` path) into O(m × l) precomputation plus
-- O(m² × l²) cheap Bool operations on precomputed lists. The frame-building
-- hot path sees a >2x throughput recovery on CAN-FD.

-- The proposition the pair loop decides: some list in the collection
-- intersects a LATER list (mirrors the suffix recursion below).
data HasPairOverlap : List (List ℕ) → Set where
  po-here  : ∀ {bs rest} → Any (Intersects bs) rest → HasPairOverlap (bs ∷ rest)
  po-there : ∀ {bs rest} → HasPairOverlap rest      → HasPairOverlap (bs ∷ rest)

-- Self-certifying twins: `does₀` is the same `_∨_` fold over
-- `bitsIntersectᵇ` as the Bool checks below; the erased certificates pin the
-- folds to Any-membership / HasPairOverlap.  MAlonzo erases the certificates
-- (Dec₀ is a newtype over Bool), so the runtime cost is the bare fold.
anyOverlap₀ : (target : List ℕ) (rest : List (List ℕ)) → Dec₀ (Any (Intersects target) rest)
anyOverlap₀ target [] = dec₀ false (ofⁿ λ ())
anyOverlap₀ target (bs ∷ rest) =
  map₀ join split (or₀ (bitsIntersect₀ target bs) (anyOverlap₀ target rest))
  where
    @0 join : Intersects target bs ⊎ Any (Intersects target) rest
            → Any (Intersects target) (bs ∷ rest)
    join (inj₁ i) = here i
    join (inj₂ a) = there a

    @0 split : Any (Intersects target) (bs ∷ rest)
             → Intersects target bs ⊎ Any (Intersects target) rest
    split (here i)  = inj₁ i
    split (there a) = inj₂ a

anyPairOverlap₀ : (bss : List (List ℕ)) → Dec₀ (HasPairOverlap bss)
anyPairOverlap₀ [] = dec₀ false (ofⁿ λ ())
anyPairOverlap₀ (bs ∷ rest) =
  map₀ join split (or₀ (anyOverlap₀ bs rest) (anyPairOverlap₀ rest))
  where
    @0 join : Any (Intersects bs) rest ⊎ HasPairOverlap rest → HasPairOverlap (bs ∷ rest)
    join (inj₁ a) = po-here a
    join (inj₂ h) = po-there h

    @0 split : HasPairOverlap (bs ∷ rest) → Any (Intersects bs) rest ⊎ HasPairOverlap rest
    split (po-here a)  = inj₁ a
    split (po-there h) = inj₂ h

hasOverlaps₀ : (n : ℕ) (sigs : List DBCSignal) → Dec₀ (HasPairOverlap (map (signalPhysicalBits n) sigs))
hasOverlaps₀ n sigs = anyPairOverlap₀ (map (signalPhysicalBits n) sigs)

-- Bool checks — definitional projections of the twins above (runtime shape
-- unchanged: the same `_∨_` folds as before).

-- Check if any precomputed signal bit list overlaps a given target bit list.
anyOverlap : List ℕ → List (List ℕ) → Bool
anyOverlap target rest = does₀ (anyOverlap₀ target rest)

-- Check all pairs of precomputed bit lists for physical overlaps.
anyPairOverlap : List (List ℕ) → Bool
anyPairOverlap bss = does₀ (anyPairOverlap₀ bss)

-- Check all signal pairs for physical overlaps. Precomputes each signal's
-- physical bit list ONCE, then runs the O(m²) pair loop over the cached lists.
-- Returns true if at least one pair of signals occupies the same physical bit.
-- `n` is the frame byte count (8 for CAN 2.0B, up to 64 for CAN-FD).
hasOverlaps : ℕ → List DBCSignal → Bool
hasOverlaps n sigs = does₀ (hasOverlaps₀ n sigs)

-- ============================================================================
-- GENERIC SIGNAL LOOKUP (parameterized by resolution strategy)
-- ============================================================================

-- Import shared DBC lookup utilities
open import Aletheia.CAN.DBCHelpers using (findMessageById; canIdEquals)

-- Lookup strategy: how to resolve a key to a DBCSignal, and how to produce errors.
-- Single instance: `indexStrategy : LookupStrategy ℕ`.  The by-name JSON path
-- was removed in C3b once all bindings switched to resolving names client-side.
-- The abstraction is kept (rather than inlined into `lookupSignalsByIndex` and
-- the two frame builders) because `lookupSignalsG` / `buildFrameG` /
-- `updateFrameG` factor the strategy out of the recursion, keeping the
-- per-key shape (resolve + error) at a single source of truth.
record LookupStrategy (K : Set) : Set where
  field
    resolve : K → DBCMessage → Maybe DBCSignal
    notFoundError : K → FrameError

-- Index-based strategy (binary FFI path — no string allocation)
indexStrategy : LookupStrategy ℕ
indexStrategy = record
  { resolve       = λ idx msg → listIndex idx (DBCMessage.signals msg)
  ; notFoundError = SignalIndexOOB
  }

-- Generic signal lookup: resolve each key to a DBCSignal using the strategy.
lookupSignalsG : ∀ {K} → LookupStrategy K → List (K × ℚ) → DBCMessage → FrameError ⊎ List (DBCSignal × ℚ)
lookupSignalsG _     []                   _   = inj₂ []
lookupSignalsG strat ((key , value) ∷ rest) msg with LookupStrategy.resolve strat key msg
... | nothing = inj₁ (LookupStrategy.notFoundError strat key)
... | just sig = lookupSignalsG strat rest msg >>=ₑ λ restSigs → inj₂ ((sig , value) ∷ restSigs)

-- Index-based lookup (public API consumed by the binary FFI path)
lookupSignalsByIndex : List (ℕ × ℚ) → DBCMessage → FrameError ⊎ List (DBCSignal × ℚ)
lookupSignalsByIndex = lookupSignalsG indexStrategy

-- ============================================================================
-- FRAME BUILDING
-- ============================================================================

-- Inject a single signal into a frame
injectOne : ∀ {n} → CANFrame n → (DBCSignal × ℚ) → FrameError ⊎ CANFrame n
injectOne frame (sig , value) with injectSignal value (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame
... | nothing = inj₁ (InjectionFailed (signalNameStr sig))
... | just f  = inj₂ f

-- Inject all signals into a frame (left-to-right fold)
injectAll : ∀ {n} → CANFrame n → List (DBCSignal × ℚ) → FrameError ⊎ CANFrame n
injectAll frame [] = inj₂ frame
injectAll frame (sig ∷ rest) = injectOne frame sig >>=ₑ λ frame' → injectAll frame' rest

-- Build a CAN frame from signal name-value pairs
-- Returns FrameError if:
-- - CAN ID not found in DBC
-- - Any signal name not found in message
-- - Signals overlap
-- - Signal value out of bounds or injection fails
-- Shared build pipeline: check overlaps, inject into empty frame, extract payload
validateAndBuild : CANId → (dlc : DLC) → List (DBCSignal × ℚ) → FrameError ⊎ Vec Byte (dlcBytes dlc)
validateAndBuild canId dlc defs with hasOverlaps (dlcBytes dlc) (map Data.Product.proj₁ defs)
... | true = inj₁ SignalsOverlap
... | false = injectAll emptyFrame defs >>=ₑ λ finalFrame → inj₂ (CANFrame.payload finalFrame)
  where
    emptyFrame : CANFrame (dlcBytes dlc)
    emptyFrame = record { id = canId ; dlc = dlc ; payload = Vec.replicate (dlcBytes dlc) 0 }

-- ============================================================================
-- GENERIC FRAME BUILDING AND UPDATING
-- ============================================================================

-- Generic build: lookup signals via strategy, validate overlaps, inject into empty frame.
buildFrameG : ∀ {K} → LookupStrategy K → DBC → CANId → (dlc : DLC) → List (K × ℚ) → FrameError ⊎ Vec Byte (dlcBytes dlc)
buildFrameG strat dbc canId dlc signals with findMessageById canId dbc
... | nothing = inj₁ CANIdNotFound
... | just msg = lookupSignalsG strat signals msg >>=ₑ λ signalDefs → validateAndBuild canId dlc signalDefs

-- Generic update: verify CAN ID match, lookup signals, inject into existing frame.
updateFrameG : ∀ {K} → LookupStrategy K → ∀ {n} → DBC → CANId → CANFrame n → List (K × ℚ) → FrameError ⊎ CANFrame n
updateFrameG strat dbc canId frame signals =
  if canIdEquals canId (CANFrame.id frame)
  then findAndInject
  else inj₁ CANIdMismatch
  where
    findAndInject : FrameError ⊎ CANFrame _
    findAndInject with findMessageById canId dbc
    ... | nothing = inj₁ CANIdNotFound
    ... | just msg = lookupSignalsG strat signals msg >>=ₑ λ signalDefs → injectAll frame signalDefs

-- Index-based API (binary FFI path — no string allocation)
buildFrameByIndex : DBC → CANId → (dlc : DLC) → List (ℕ × ℚ) → FrameError ⊎ Vec Byte (dlcBytes dlc)
buildFrameByIndex = buildFrameG indexStrategy

updateFrameByIndex : ∀ {n} → DBC → CANId → CANFrame n → List (ℕ × ℚ) → FrameError ⊎ CANFrame n
updateFrameByIndex = updateFrameG indexStrategy
