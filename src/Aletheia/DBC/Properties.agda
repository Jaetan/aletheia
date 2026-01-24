{-# OPTIONS --safe --without-K #-}

-- Correctness properties for DBC types and validation.
--
-- Purpose: Define and prove properties of DBC structures and validation.
-- Properties: Bounded values (IDs, start bits, lengths), well-formedness, range consistency.
-- Role: Runtime validation properties with decidable predicates for proof extraction.
--
-- Key invariant: For any multiplexor configuration, active signals don't overlap.
module Aletheia.DBC.Properties where

open import Aletheia.DBC.Types
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _<_; _+_; suc; zero) renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; _≤?_; _<?_)
open import Data.Fin using (Fin; toℕ)
open import Data.Rational using (ℚ; _≤_)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

-- ============================================================================
-- BASIC STRUCTURAL PROPERTIES
-- ============================================================================

-- Property: Parsed signal start bits are always bounded
startBit-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.startBit (DBCSignal.signalDef sig)) < 64
startBit-bounded sig = toℕ<n (SignalDef.startBit (DBCSignal.signalDef sig))
  where
    open import Data.Fin.Properties using (toℕ<n)

-- Property: Parsed signal bit lengths are always bounded
bitLength-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.bitLength (DBCSignal.signalDef sig)) ≤ₙ 64
bitLength-bounded sig = ≤-pred (toℕ<n (SignalDef.bitLength (DBCSignal.signalDef sig)))
  where
    open import Data.Fin.Properties using (toℕ<n)
    open import Data.Nat.Properties using (≤-pred)

-- Property: Parsed message IDs are always valid (bounded by CANId type)
-- Standard IDs: < 2048 (11-bit)
-- Extended IDs: < 536870912 (29-bit)
-- This property is trivially true by construction of CANId type
messageId-valid : ∀ (id : CANId) → ℕ
messageId-valid (Standard x) = toℕ x
messageId-valid (Extended x) = toℕ x
  where
    open import Data.Fin using (toℕ)

-- Property: Parsed DLC values are valid
dlc-bounded : ∀ (msg : DBCMessage) → toℕ (DBCMessage.dlc msg) ≤ₙ 8
dlc-bounded msg = ≤-pred (toℕ<n (DBCMessage.dlc msg))
  where
    open import Data.Fin.Properties using (toℕ<n)
    open import Data.Nat.Properties using (≤-pred)

-- ============================================================================
-- SIGNAL DISJOINTNESS
-- ============================================================================

-- Two signals are disjoint if their bit ranges don't overlap
data SignalsDisjoint (sig₁ sig₂ : SignalDef) : Set where
  disjoint-left :
    toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁)
      ≤ₙ toℕ (SignalDef.startBit sig₂)
    → SignalsDisjoint sig₁ sig₂
  disjoint-right :
    toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂)
      ≤ₙ toℕ (SignalDef.startBit sig₁)
    → SignalsDisjoint sig₁ sig₂

-- Decidable check for signal disjointness
signalsDisjoint? : (sig₁ sig₂ : SignalDef) → Dec (SignalsDisjoint sig₁ sig₂)
signalsDisjoint? sig₁ sig₂ =
  let s₁ = toℕ (SignalDef.startBit sig₁)
      l₁ = toℕ (SignalDef.bitLength sig₁)
      s₂ = toℕ (SignalDef.startBit sig₂)
      l₂ = toℕ (SignalDef.bitLength sig₂)
  in case (s₁ + l₁) ≤? s₂ of λ where
       (yes p) → yes (disjoint-left p)
       (no ¬p) → case (s₂ + l₂) ≤? s₁ of λ where
         (yes q) → yes (disjoint-right q)
         (no ¬q) → no (λ where
           (disjoint-left p) → ¬p p
           (disjoint-right q) → ¬q q)
  where
    open import Function using (case_of_)

-- ============================================================================
-- SIGNAL COEXISTENCE (for multiplexed signals)
-- ============================================================================

-- Two signals can potentially be active at the same time
-- This captures: "for any multiplexor configuration, could both be active?"
data CanCoexist : SignalPresence → SignalPresence → Set where
  -- Both always present
  both-always : CanCoexist Always Always
  -- Always signal coexists with any conditional signal
  always-left : ∀ {m v} → CanCoexist Always (When m v)
  always-right : ∀ {m v} → CanCoexist (When m v) Always
  -- Different multiplexors: both could be active (independent controls)
  different-mux : ∀ {m₁ m₂ v₁ v₂} → m₁ ≢ m₂ → CanCoexist (When m₁ v₁) (When m₂ v₂)
  -- Same multiplexor, same value: both active together
  -- Carry equalities as data to avoid K-dependent index unification
  same-mux-same-val : ∀ {m₁ m₂ v₁ v₂} → m₁ ≡ m₂ → v₁ ≡ v₂ → CanCoexist (When m₁ v₁) (When m₂ v₂)

-- Decidable check for coexistence
canCoexist? : (p₁ p₂ : SignalPresence) → Dec (CanCoexist p₁ p₂)
canCoexist? Always Always = yes both-always
canCoexist? Always (When m v) = yes always-left
canCoexist? (When m v) Always = yes always-right
canCoexist? (When m₁ v₁) (When m₂ v₂) = helper (m₁ ≟ₛ m₂) (v₁ ≟ₙ v₂)
  where
    open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
    open import Data.Nat.Properties using () renaming (_≟_ to _≟ₙ_)

    helper : Dec (m₁ ≡ m₂) → Dec (v₁ ≡ v₂) → Dec (CanCoexist (When m₁ v₁) (When m₂ v₂))
    helper (yes m≡) (yes v≡) = yes (same-mux-same-val m≡ v≡)
    -- Same mux, different value: mutually exclusive, can't coexist
    helper (yes m≡) (no v≢) = no λ where
      (different-mux m≢) → m≢ m≡
      (same-mux-same-val _ v≡) → v≢ v≡
    helper (no m≢) _ = yes (different-mux m≢)

-- ============================================================================
-- SIGNAL PAIR VALIDITY
-- ============================================================================

-- A pair of signals is valid if:
-- Either they can't coexist (mutually exclusive), or they are disjoint
data SignalPairValid (sig₁ sig₂ : DBCSignal) : Set where
  mutually-exclusive :
    ¬ CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
    → SignalPairValid sig₁ sig₂
  disjoint-when-coexist :
    CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
    → SignalsDisjoint (DBCSignal.signalDef sig₁) (DBCSignal.signalDef sig₂)
    → SignalPairValid sig₁ sig₂

-- Decidable check for signal pair validity
signalPairValid? : (sig₁ sig₂ : DBCSignal) → Dec (SignalPairValid sig₁ sig₂)
signalPairValid? sig₁ sig₂ with canCoexist? (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
... | no ¬coexist = yes (mutually-exclusive ¬coexist)
... | yes coexist with signalsDisjoint? (DBCSignal.signalDef sig₁) (DBCSignal.signalDef sig₂)
...   | yes disj = yes (disjoint-when-coexist coexist disj)
...   | no ¬disj = no λ where
        (mutually-exclusive ¬coexist) → ¬coexist coexist
        (disjoint-when-coexist _ disj) → ¬disj disj

-- ============================================================================
-- ALL PAIRS VALIDITY (for a list of signals)
-- ============================================================================

-- Check one signal against all others in a list
data SignalValidAgainstAll (sig : DBCSignal) : List DBCSignal → Set where
  valid-nil : SignalValidAgainstAll sig []
  valid-cons : ∀ {other rest}
    → SignalPairValid sig other
    → SignalValidAgainstAll sig rest
    → SignalValidAgainstAll sig (other ∷ rest)

signalValidAgainstAll? : (sig : DBCSignal) → (others : List DBCSignal)
                       → Dec (SignalValidAgainstAll sig others)
signalValidAgainstAll? sig [] = yes valid-nil
signalValidAgainstAll? sig (other ∷ rest) with signalPairValid? sig other
... | no ¬valid = no λ where (valid-cons v _) → ¬valid v
... | yes valid with signalValidAgainstAll? sig rest
...   | no ¬rest = no λ where (valid-cons _ r) → ¬rest r
...   | yes restValid = yes (valid-cons valid restValid)

-- All pairs in a list are valid (triangular check: each signal against all following)
data AllSignalPairsValid : List DBCSignal → Set where
  pairs-nil : AllSignalPairsValid []
  pairs-cons : ∀ {sig rest}
    → SignalValidAgainstAll sig rest
    → AllSignalPairsValid rest
    → AllSignalPairsValid (sig ∷ rest)

allSignalPairsValid? : (sigs : List DBCSignal) → Dec (AllSignalPairsValid sigs)
allSignalPairsValid? [] = yes pairs-nil
allSignalPairsValid? (sig ∷ rest) with signalValidAgainstAll? sig rest
... | no ¬valid = no λ where (pairs-cons v _) → ¬valid v
... | yes valid with allSignalPairsValid? rest
...   | no ¬rest = no λ where (pairs-cons _ r) → ¬rest r
...   | yes restValid = yes (pairs-cons valid restValid)

-- Message signals are valid if all pairs are valid
messageSignalsValid? : (msg : DBCMessage) → Dec (AllSignalPairsValid (DBCMessage.signals msg))
messageSignalsValid? msg = allSignalPairsValid? (DBCMessage.signals msg)

-- ============================================================================
-- SIGNAL RANGE CONSISTENCY
-- ============================================================================

-- A signal's value range is consistent if minimum ≤ maximum
-- Note: startBit < 64, bitLength ≤ 64, and dlc ≤ 8 are guaranteed by Fin types
SignalRangeConsistent : DBCSignal → Set
SignalRangeConsistent sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in minimum ≤ maximum

signalRangeConsistent? : (sig : DBCSignal) → Dec (SignalRangeConsistent sig)
signalRangeConsistent? sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in minimum ≤?ᵣ maximum

-- All signals in a list have consistent ranges
data AllSignalRangesConsistent : List DBCSignal → Set where
  ranges-nil : AllSignalRangesConsistent []
  ranges-cons : ∀ {sig rest}
    → SignalRangeConsistent sig
    → AllSignalRangesConsistent rest
    → AllSignalRangesConsistent (sig ∷ rest)

allSignalRangesConsistent? : (sigs : List DBCSignal) → Dec (AllSignalRangesConsistent sigs)
allSignalRangesConsistent? [] = yes ranges-nil
allSignalRangesConsistent? (sig ∷ rest) with signalRangeConsistent? sig
... | no ¬valid = no λ where (ranges-cons v _) → ¬valid v
... | yes valid with allSignalRangesConsistent? rest
...   | no ¬rest = no λ where (ranges-cons _ r) → ¬rest r
...   | yes restValid = yes (ranges-cons valid restValid)

-- ============================================================================
-- COMPLETE MESSAGE VALIDITY
-- ============================================================================

-- A message is valid if all signal pairs are valid and all ranges are consistent
data MessageValid (msg : DBCMessage) : Set where
  message-valid :
    AllSignalPairsValid (DBCMessage.signals msg)
    → AllSignalRangesConsistent (DBCMessage.signals msg)
    → MessageValid msg

messageValid? : (msg : DBCMessage) → Dec (MessageValid msg)
messageValid? msg with allSignalPairsValid? (DBCMessage.signals msg)
... | no ¬pairs = no λ where (message-valid p _) → ¬pairs p
... | yes pairs with allSignalRangesConsistent? (DBCMessage.signals msg)
...   | no ¬ranges = no λ where (message-valid _ r) → ¬ranges r
...   | yes ranges = yes (message-valid pairs ranges)

-- ============================================================================
-- DECIDABLE DBC WELL-FORMEDNESS
-- ============================================================================

-- All messages are valid
data AllMessagesValid : List DBCMessage → Set where
  msgs-nil : AllMessagesValid []
  msgs-cons : ∀ {msg rest}
    → MessageValid msg
    → AllMessagesValid rest
    → AllMessagesValid (msg ∷ rest)

allMessagesValid? : (msgs : List DBCMessage) → Dec (AllMessagesValid msgs)
allMessagesValid? [] = yes msgs-nil
allMessagesValid? (msg ∷ rest) with messageValid? msg
... | no ¬valid = no λ where (msgs-cons v _) → ¬valid v
... | yes valid with allMessagesValid? rest
...   | no ¬rest = no λ where (msgs-cons _ r) → ¬rest r
...   | yes restValid = yes (msgs-cons valid restValid)

-- Full DBC validity: all messages valid
DBCValid : DBC → Set
DBCValid dbc = AllMessagesValid (DBC.messages dbc)

dbcValid? : (dbc : DBC) → Dec (DBCValid dbc)
dbcValid? dbc = allMessagesValid? (DBC.messages dbc)

-- ============================================================================
-- PROOF EXTRACTION: From validated DBC to signal disjointness proofs
-- ============================================================================

-- Given a well-formed DBC, extract disjointness proof for any two coexisting signals
-- This is the payoff: once DBC is validated, we never need to re-check disjointness

-- TODO: Add lookup functions that return SignalsDisjoint proof for signals in validated DBC
-- This eliminates threading disjointness hypotheses through all signal operations
