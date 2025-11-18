{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.SignalPredicate where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.DBC.Types
open import Data.String using (String; _≟_)
open import Data.Rational as Rat using (ℚ; _/_; _-_; ∣_∣; _≤?_; _<?_)
open import Data.Integer using (+_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Fin using (toℕ)
open import Data.Nat using (_≡ᵇ_)

-- ============================================================================
-- SIGNAL PREDICATES
-- ============================================================================

-- Predicates that can be evaluated over signal values
data SignalPredicate : Set where
  Equals      : (signalName : String) → (value : ℚ) → SignalPredicate
  LessThan    : (signalName : String) → (value : ℚ) → SignalPredicate
  GreaterThan : (signalName : String) → (value : ℚ) → SignalPredicate
  Between     : (signalName : String) → (min : ℚ) → (max : ℚ) → SignalPredicate
  ChangedBy   : (signalName : String) → (delta : ℚ) → SignalPredicate

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

canIdEquals : CANId → CANId → Bool
canIdEquals (Standard x) (Standard y) = toℕ x ≡ᵇ toℕ y
canIdEquals (Extended x) (Extended y) = toℕ x ≡ᵇ toℕ y
canIdEquals _ _ = false

findInList : ∀ {A : Set} → (A → Bool) → List A → Maybe A
findInList pred [] = nothing
findInList pred (x ∷ xs) = if pred x then just x else findInList pred xs

findMessageById : CANId → DBC → Maybe DBCMessage
findMessageById msgId dbc = findInList matchesId (DBC.messages dbc)
  where
    matchesId : DBCMessage → Bool
    matchesId msg = canIdEquals msgId (DBCMessage.id msg)

findSignalByName : String → DBCMessage → Maybe DBCSignal
findSignalByName name msg = findInList matchesName (DBCMessage.signals msg)
  where
    matchesName : DBCSignal → Bool
    matchesName sig = ⌊ DBCSignal.name sig ≟ name ⌋

extractSignalValue : String → DBC → CANFrame → Maybe ℚ
extractSignalValue sigName dbc frame =
  findMessageById (CANFrame.id frame) dbc >>= λ msg →
  findSignalByName sigName msg >>= λ sig →
  extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)

-- ============================================================================
-- COMPARISON HELPERS
-- ============================================================================

-- Efficient Boolean comparison operators
-- These are wrappers around decidable comparisons for runtime checking.
-- Phase 3 can use the decidable versions (_≤?_, _≟_, etc.) for proofs.

_==ℚ_ : ℚ → ℚ → Bool
x ==ℚ y = ⌊ x Rat.≟ y ⌋

_≤ℚ_ : ℚ → ℚ → Bool
x ≤ℚ y = ⌊ x Rat.≤? y ⌋

-- Efficient strict comparison (single check, not double)
_<ℚ_ : ℚ → ℚ → Bool
x <ℚ y = ⌊ x Rat.<? y ⌋

_>ℚ_ : ℚ → ℚ → Bool
x >ℚ y = y <ℚ x

_≥ℚ_ : ℚ → ℚ → Bool
x ≥ℚ y = y ≤ℚ x

-- ============================================================================
-- PREDICATE EVALUATION
-- ============================================================================

evalPredicate : SignalPredicate → DBC → CANFrame → Maybe Bool
evalPredicate (Equals sigName value) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (sigVal ==ℚ value)

evalPredicate (LessThan sigName value) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (sigVal <ℚ value)

evalPredicate (GreaterThan sigName value) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (sigVal >ℚ value)

evalPredicate (Between sigName minVal maxVal) dbc frame =
  extractSignalValue sigName dbc frame >>= λ sigVal →
  just (minVal ≤ℚ sigVal ∧ sigVal ≤ℚ maxVal)

evalPredicate (ChangedBy sigName delta) dbc frame = nothing

evalPredicatePair : SignalPredicate → DBC → CANFrame → CANFrame → Maybe Bool
evalPredicatePair (ChangedBy sigName delta) dbc prevFrame currFrame =
  extractSignalValue sigName dbc prevFrame >>= λ prevVal →
  extractSignalValue sigName dbc currFrame >>= λ currVal →
  let diff = ∣ currVal Rat.- prevVal ∣
  in just ⌊ delta Rat.≤? diff ⌋

evalPredicatePair pred dbc _ currFrame = evalPredicate pred dbc currFrame
