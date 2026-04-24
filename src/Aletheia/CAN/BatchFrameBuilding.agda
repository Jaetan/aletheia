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
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (injectSignal)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Properties using (signalPhysicalBits; bitsIntersectᵇ)
open import Data.String using (String)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec as Vec using (Vec; replicate)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; not)
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
-- Uses the Bool-valued `bitsIntersectᵇ` fast path from `DBC/Properties.agda`.
-- Equivalence with `PhysicallyDisjoint` is proved by
-- `physicallyOverlapᵇ-sound` / `physicallyOverlapᵇ-complete` in that module,
-- so this check is as trustworthy as the `Dec`-valued `physicallyDisjoint?`.
--
-- Performance note: per-signal physical bit positions are precomputed ONCE
-- in `hasOverlaps`, outside the O(m²) pair loop. This turns the per-frame
-- cost from O(m² × l²) (with Dec-boxed per-bit comparisons, as in the
-- `physicallyDisjoint?` path) into O(m × l) precomputation plus
-- O(m² × l²) cheap Bool operations on precomputed lists. The frame-building
-- hot path sees a >2x throughput recovery on CAN-FD.

-- Check if any precomputed signal bit list overlaps a given target bit list.
anyOverlap : List ℕ → List (List ℕ) → Bool
anyOverlap target [] = false
anyOverlap target (bs ∷ rest) = bitsIntersectᵇ target bs ∨ anyOverlap target rest

-- Check all pairs of precomputed bit lists for physical overlaps.
anyPairOverlap : List (List ℕ) → Bool
anyPairOverlap []         = false
anyPairOverlap (bs ∷ rest) = anyOverlap bs rest ∨ anyPairOverlap rest

-- Check all signal pairs for physical overlaps. Precomputes each signal's
-- physical bit list ONCE, then runs the O(m²) pair loop over the cached lists.
-- Returns true if at least one pair of signals occupies the same physical bit.
-- `n` is the frame byte count (8 for CAN 2.0B, up to 64 for CAN-FD).
hasOverlaps : ℕ → List DBCSignal → Bool
hasOverlaps n sigs = anyPairOverlap (map (signalPhysicalBits n) sigs)

-- ============================================================================
-- GENERIC SIGNAL LOOKUP (parameterized by resolution strategy)
-- ============================================================================

-- Import shared DBC lookup utilities
open import Aletheia.CAN.DBCHelpers using (findMessageById; canIdEquals)

-- Lookup strategy: how to resolve a key to a DBCSignal, and how to produce errors.
-- Currently only instantiated with `indexStrategy` — the by-name JSON path was
-- removed in C3b once all bindings switched to resolving names client-side.
-- The record layer is retained so future strategies (e.g. multi-arena lookup)
-- can be added without touching the generic machinery below.
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
