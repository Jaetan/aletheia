{-# OPTIONS --safe --without-K #-}

-- Multiplexing correctness properties for signal extraction.
--
-- Purpose: Prove soundness and completeness of the multiplexor check
-- used in extractSignalDirect and extractSignalWithContext.
-- Properties:
--   checkMultiplexor-finds-signal   : check passes → mux signal exists in DBC message
--   checkMultiplexor-rejects-missing : mux signal absent → check fails
--   checkSignalPresence-sound       : presence check passes → Always or mux condition holds
--   extractSignalDirect-mux         : mux check fails → extraction returns SignalNotPresent
--
-- Note: extractSignal normalizes to a complex if-then-else on bounds checking,
-- preventing with-abstraction from matching it in the goal type. Properties
-- involving extractSignal's return value are therefore stated at the
-- checkMultiplexor/checkSignalPresence abstraction boundary, which is where
-- multiplexing correctness is decided.
--
-- Runtime cost: zero (proofs erased by MAlonzo compilation).
module Aletheia.CAN.SignalExtraction.Properties where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; SignalNotPresent)
open import Aletheia.CAN.SignalExtraction
    using (checkMultiplexor; checkSignalPresence; extractSignalDirect)
open import Aletheia.CAN.DBCHelpers using (findSignalByName)
open import Aletheia.DBC.Types using (DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to is-just)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)

-- ============================================================================
-- PROPERTY 1: Multiplexor check — signal existence
-- ============================================================================

-- If checkMultiplexor passes, the multiplexor signal exists in the message.
-- This guarantees the DBC reference is valid (the mux signal was defined).
checkMultiplexor-finds-signal : ∀ {n} (frame : CANFrame n) (msg : DBCMessage)
  (muxName : String) (muxValue : ℕ)
  → checkMultiplexor frame msg muxName muxValue ≡ nothing
  → Is-just (findSignalByName muxName msg)
checkMultiplexor-finds-signal frame msg muxName muxValue eq
  with findSignalByName muxName msg
... | nothing  = case eq of λ ()
... | just _   = is-just tt

-- ============================================================================
-- PROPERTY 2: Multiplexor check — rejects missing signal
-- ============================================================================

-- If the multiplexor signal doesn't exist in the message, the check fails.
-- Guarantees that typos or renamed signals are caught.
checkMultiplexor-rejects-missing : ∀ {n} (frame : CANFrame n) (msg : DBCMessage)
  (muxName : String) (muxValue : ℕ)
  → findSignalByName muxName msg ≡ nothing
  → Is-just (checkMultiplexor frame msg muxName muxValue)
checkMultiplexor-rejects-missing frame msg muxName muxValue eq
  with findSignalByName muxName msg
... | nothing = is-just tt
... | just _  = case eq of λ ()

-- ============================================================================
-- PROPERTY 3: Signal presence check soundness
-- ============================================================================

-- If the presence check passes, either the signal is always present
-- or the multiplexor condition holds. This is the key dispatch property:
-- it shows that Always signals bypass multiplexor checks entirely, and
-- When signals require a passing multiplexor check.
checkSignalPresence-sound : ∀ {n} (frame : CANFrame n) (msg : DBCMessage) (sig : DBCSignal)
  → checkSignalPresence frame msg sig ≡ nothing
  → (DBCSignal.presence sig ≡ Always)
    ⊎ (∃[ muxName ] ∃[ muxVal ]
        (DBCSignal.presence sig ≡ When muxName muxVal
         × checkMultiplexor frame msg muxName muxVal ≡ nothing))
checkSignalPresence-sound frame msg sig eq with DBCSignal.presence sig
... | Always             = inj₁ refl
... | When muxName muxVal = inj₂ (muxName , muxVal , refl , eq)

-- ============================================================================
-- PROPERTY 4: Extraction respects multiplexor
-- ============================================================================

-- When the presence check fails, extractSignalDirect returns SignalNotPresent
-- with the failure reason. This guarantees no data is returned for a
-- multiplexed signal whose multiplexor value doesn't match.
extractSignalDirect-mux : ∀ {n} (msg : DBCMessage) (frame : CANFrame n) (sig : DBCSignal)
  (reason : String)
  → checkSignalPresence frame msg sig ≡ just reason
  → extractSignalDirect msg frame sig ≡ SignalNotPresent reason
extractSignalDirect-mux msg frame sig reason eq
  with checkSignalPresence frame msg sig
... | just r = cong SignalNotPresent (just-injective eq)
