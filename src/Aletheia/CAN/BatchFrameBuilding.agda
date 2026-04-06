{-# OPTIONS --safe --without-K #-}

-- Batch frame building from signal name-value pairs.
--
-- Purpose: Build CAN frames from multiple signal values at once with validation.
-- Operations: buildFrame (DBC + CAN ID + signals → FrameError ⊎ frame).
-- Role: Batch encoding for language bindings (Python, C++, Go).
--
-- Validation: Signal name existence, signal overlap detection, multiplexing consistency.
-- Guarantees: Signals partition the frame properly (no corruption).
module Aletheia.CAN.BatchFrameBuilding where

open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (injectSignal)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Data.String using (String)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec as Vec using (Vec; replicate)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.Prelude using (listIndex; _>>=ₑ_)
open import Aletheia.Error using
  ( FrameError; SignalNotFound; SignalIndexOOB; InjectionFailed
  ; SignalsOverlap; CANIdNotFound; CANIdMismatch
  )

-- ============================================================================
-- OVERLAP DETECTION
-- ============================================================================

-- Check if two bit ranges overlap
-- Range 1: [start1 .. start1 + len1 - 1]
-- Range 2: [start2 .. start2 + len2 - 1]
-- Zero-length ranges occupy no bits and never overlap.
--
-- Note: This is defense-in-depth for programmatically-constructed signal lists.
-- Validated DBCs use signalPairValid? (DBC/Properties.agda) which handles
-- zero-length via vacuously-true universal quantification over empty bit ranges,
-- and is endianness-aware (PhysicallyDisjoint).
rangesOverlap : ℕ → ℕ → ℕ → ℕ → Bool
rangesOverlap _      zero   _      _      = false
rangesOverlap _      _      _      zero   = false
rangesOverlap start1 len1   start2 len2   =
  let end1 = start1 + len1 ∸ 1
      end2 = start2 + len2 ∸ 1
  in (start1 ≤ᵇ end2) ∧ (start2 ≤ᵇ end1)

-- Check if a signal overlaps with another signal
signalsOverlap : DBCSignal → DBCSignal → Bool
signalsOverlap sig1 sig2 =
  let def1 = DBCSignal.signalDef sig1
      def2 = DBCSignal.signalDef sig2
      start1 = SignalDef.startBit def1
      len1 = SignalDef.bitLength def1
      start2 = SignalDef.startBit def2
      len2 = SignalDef.bitLength def2
  in rangesOverlap start1 len1 start2 len2

-- Check if any signal in a list overlaps with a given signal
anyOverlap : DBCSignal → List DBCSignal → Bool
anyOverlap sig [] = false
anyOverlap sig (s ∷ rest) = signalsOverlap sig s ∨ anyOverlap sig rest

-- Check all signals for pairwise overlaps
-- Returns true if there is at least one overlap
hasOverlaps : List DBCSignal → Bool
hasOverlaps [] = false
hasOverlaps (sig ∷ rest) = anyOverlap sig rest ∨ hasOverlaps rest

-- ============================================================================
-- GENERIC SIGNAL LOOKUP (parameterized by resolution strategy)
-- ============================================================================

-- Import shared DBC lookup utilities
open import Aletheia.CAN.DBCHelpers using (findSignalByName; findMessageById; canIdEquals)

-- Lookup strategy: how to resolve a key to a DBCSignal, and how to produce errors.
-- Two instances: name-based (String key, findSignalByName) and index-based (ℕ key, listIndex).
record LookupStrategy (K : Set) : Set where
  field
    resolve : K → DBCMessage → Maybe DBCSignal
    notFoundError : K → FrameError

-- Name-based strategy (JSON API path)
nameStrategy : LookupStrategy String
nameStrategy = record
  { resolve       = λ name msg → findSignalByName name msg
  ; notFoundError = SignalNotFound
  }

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

-- Name-based lookup (preserves original API)
lookupSignals : List (String × ℚ) → DBCMessage → FrameError ⊎ List (DBCSignal × ℚ)
lookupSignals = lookupSignalsG nameStrategy

-- Index-based lookup (preserves original API)
lookupSignalsByIndex : List (ℕ × ℚ) → DBCMessage → FrameError ⊎ List (DBCSignal × ℚ)
lookupSignalsByIndex = lookupSignalsG indexStrategy

-- ============================================================================
-- FRAME BUILDING
-- ============================================================================

-- Inject a single signal into a frame
injectOne : ∀ {n} → CANFrame n → (DBCSignal × ℚ) → FrameError ⊎ CANFrame n
injectOne frame (sig , value) with injectSignal value (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame
... | nothing = inj₁ (InjectionFailed (DBCSignal.name sig))
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
validateAndBuild : CANId → (dlc : ℕ) → List (DBCSignal × ℚ) → FrameError ⊎ Vec Byte (dlcToBytes dlc)
validateAndBuild canId dlc defs with hasOverlaps (map Data.Product.proj₁ defs)
... | true = inj₁ SignalsOverlap
... | false = injectAll emptyFrame defs >>=ₑ λ finalFrame → inj₂ (CANFrame.payload finalFrame)
  where
    emptyFrame : CANFrame (dlcToBytes dlc)
    emptyFrame = record { id = canId ; dlc = dlc ; payload = Vec.replicate (dlcToBytes dlc) 0 }

-- ============================================================================
-- GENERIC FRAME BUILDING AND UPDATING
-- ============================================================================

-- Generic build: lookup signals via strategy, validate overlaps, inject into empty frame.
buildFrameG : ∀ {K} → LookupStrategy K → DBC → CANId → (dlc : ℕ) → List (K × ℚ) → FrameError ⊎ Vec Byte (dlcToBytes dlc)
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

-- Name-based API (JSON path)
buildFrame : DBC → CANId → (dlc : ℕ) → List (String × ℚ) → FrameError ⊎ Vec Byte (dlcToBytes dlc)
buildFrame = buildFrameG nameStrategy

updateFrame : ∀ {n} → DBC → CANId → CANFrame n → List (String × ℚ) → FrameError ⊎ CANFrame n
updateFrame = updateFrameG nameStrategy

-- Index-based API (binary FFI path — no string allocation)
buildFrameByIndex : DBC → CANId → (dlc : ℕ) → List (ℕ × ℚ) → FrameError ⊎ Vec Byte (dlcToBytes dlc)
buildFrameByIndex = buildFrameG indexStrategy

updateFrameByIndex : ∀ {n} → DBC → CANId → CANFrame n → List (ℕ × ℚ) → FrameError ⊎ CANFrame n
updateFrameByIndex = updateFrameG indexStrategy
