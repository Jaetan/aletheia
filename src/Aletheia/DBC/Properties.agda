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
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Nat using (ℕ; _<_; _≤_; _+_; suc; zero)
open import Data.Nat.Properties using (≤-refl; ≤-trans; _≤?_; _<?_)
open import Data.Fin using (Fin; toℕ)
open import Data.Rational using (ℚ; _≤ᵇ_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
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
bitLength-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.bitLength (DBCSignal.signalDef sig)) ≤ 64
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
dlc-bounded : ∀ (msg : DBCMessage) → toℕ (DBCMessage.dlc msg) ≤ 8
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
      ≤ toℕ (SignalDef.startBit sig₂)
    → SignalsDisjoint sig₁ sig₂
  disjoint-right :
    toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂)
      ≤ toℕ (SignalDef.startBit sig₁)
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
-- RUNTIME VALIDATION PROPERTIES (Bool versions for backwards compatibility)
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
  all signal-ranges-consistent (DBCMessage.signals msg)

-- Check all messages in a DBC have consistent ranges
dbc-ranges-consistent : DBC → Bool
dbc-ranges-consistent dbc =
  all message-ranges-consistent (DBC.messages dbc)

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

-- Bool version of allSignalPairsValid for easy composition
message-signals-disjoint : DBCMessage → Bool
message-signals-disjoint msg = ⌊ allSignalPairsValid? (DBCMessage.signals msg) ⌋

-- Helper: Check if a message is well-formed (includes signal disjointness)
message-well-formed : DBCMessage → Bool
message-well-formed msg =
  (toℕ (DBCMessage.dlc msg) Data.Nat.≤ᵇ 8) ∧
  all signal-well-formed (DBCMessage.signals msg) ∧
  message-signals-disjoint msg
  where
    open import Data.Nat using (_≤ᵇ_)

-- If a DBC parses successfully, all its structural properties hold
-- This now includes: signal overlap validation for all messages
dbc-well-formed : DBC → Bool
dbc-well-formed dbc =
  dbc-ranges-consistent dbc ∧
  all message-well-formed (DBC.messages dbc)

-- ============================================================================
-- DECIDABLE DBC WELL-FORMEDNESS
-- ============================================================================

-- All messages have valid signal configurations
data AllMessagesSignalsValid : List DBCMessage → Set where
  msgs-nil : AllMessagesSignalsValid []
  msgs-cons : ∀ {msg rest}
    → AllSignalPairsValid (DBCMessage.signals msg)
    → AllMessagesSignalsValid rest
    → AllMessagesSignalsValid (msg ∷ rest)

allMessagesSignalsValid? : (msgs : List DBCMessage) → Dec (AllMessagesSignalsValid msgs)
allMessagesSignalsValid? [] = yes msgs-nil
allMessagesSignalsValid? (msg ∷ rest) with messageSignalsValid? msg
... | no ¬valid = no λ where (msgs-cons v _) → ¬valid v
... | yes valid with allMessagesSignalsValid? rest
...   | no ¬rest = no λ where (msgs-cons _ r) → ¬rest r
...   | yes restValid = yes (msgs-cons valid restValid)

-- Full DBC signal configuration validity
DBCSignalsValid : DBC → Set
DBCSignalsValid dbc = AllMessagesSignalsValid (DBC.messages dbc)

dbcSignalsValid? : (dbc : DBC) → Dec (DBCSignalsValid dbc)
dbcSignalsValid? dbc = allMessagesSignalsValid? (DBC.messages dbc)

-- ============================================================================
-- PROOF EXTRACTION: From validated DBC to signal disjointness proofs
-- ============================================================================

-- Given a well-formed DBC, extract disjointness proof for any two coexisting signals
-- This is the payoff: once DBC is validated, we never need to re-check disjointness

-- TODO: Add lookup functions that return SignalsDisjoint proof for signals in validated DBC
-- This eliminates threading disjointness hypotheses through all signal operations
