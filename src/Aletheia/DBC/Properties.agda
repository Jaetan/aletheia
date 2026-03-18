{-# OPTIONS --safe --without-K #-}

-- Correctness properties for DBC types and validation.
--
-- Purpose: Define and prove properties of DBC structures and validation.
-- Properties: Bounded values (IDs, start bits, lengths), well-formedness, range consistency.
-- Role: Runtime validation properties with decidable predicates for proof extraction.
--
-- Key invariant: For any multiplexor configuration, active signals don't overlap.
module Aletheia.DBC.Properties where

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_) renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties using (_≤?_) renaming (_≟_ to _≟ₙ_)
open import Data.Rational using (ℚ; _≤_)
open import Data.Rational.Properties using () renaming (_≤?_ to _≤?ᵣ_)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)

-- ============================================================================
-- BASIC STRUCTURAL PROPERTIES
-- ============================================================================

-- Note: Signal start bits, bit lengths, DLC, and CAN IDs are now ℕ.
-- Bounds are enforced at construction sites (% 64, % 65, % 9, % 2048)
-- rather than by Fin types. The proofs that relied on Fin bounds
-- (startBit-bounded, bitLength-bounded, dlc-bounded, messageId-valid)
-- have been removed as they are no longer type-level guarantees.

-- Extractors for CAN ID values (now just identity since fields are ℕ)
messageId-value : CANId → ℕ
messageId-value (Standard x) = x
messageId-value (Extended x) = x

-- ============================================================================
-- SIGNAL DISJOINTNESS
-- ============================================================================

-- Two signals are disjoint if their bit ranges don't overlap
data SignalsDisjoint (sig₁ sig₂ : SignalDef) : Set where
  disjoint-left :
    SignalDef.startBit sig₁ + SignalDef.bitLength sig₁
      ≤ₙ SignalDef.startBit sig₂
    → SignalsDisjoint sig₁ sig₂
  disjoint-right :
    SignalDef.startBit sig₂ + SignalDef.bitLength sig₂
      ≤ₙ SignalDef.startBit sig₁
    → SignalsDisjoint sig₁ sig₂

-- Decidable check for signal disjointness
signalsDisjoint? : (sig₁ sig₂ : SignalDef) → Dec (SignalsDisjoint sig₁ sig₂)
signalsDisjoint? sig₁ sig₂ =
  let s₁ = SignalDef.startBit sig₁
      l₁ = SignalDef.bitLength sig₁
      s₂ = SignalDef.startBit sig₂
      l₂ = SignalDef.bitLength sig₂
  in case (s₁ + l₁) ≤? s₂ of λ where
       (yes p) → yes (disjoint-left p)
       (no ¬p) → case (s₂ + l₂) ≤? s₁ of λ where
         (yes q) → yes (disjoint-right q)
         (no ¬q) → no (λ where
           (disjoint-left p) → ¬p p
           (disjoint-right q) → ¬q q)

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
-- Note: startBit < 64, bitLength ≤ 64, and dlc ≤ 8 are enforced at construction sites
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

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)

-- Extract SignalPairValid from SignalValidAgainstAll
-- If sig₂ is in the list that sig₁ was validated against, we have the proof
extractFromValidAgainstAll : ∀ {sig₁ sig₂ sigs}
  → SignalValidAgainstAll sig₁ sigs
  → sig₂ ∈ sigs
  → SignalPairValid sig₁ sig₂
extractFromValidAgainstAll (valid-cons pv _) (here refl) = pv
extractFromValidAgainstAll (valid-cons _ rest) (there sig₂∈) = extractFromValidAgainstAll rest sig₂∈

-- CanCoexist is symmetric
canCoexist-sym : ∀ {p₁ p₂} → CanCoexist p₁ p₂ → CanCoexist p₂ p₁
canCoexist-sym both-always = both-always
canCoexist-sym always-left = always-right
canCoexist-sym always-right = always-left
canCoexist-sym (different-mux m≢) = different-mux (λ eq → m≢ (sym eq))
canCoexist-sym (same-mux-same-val m≡ v≡) = same-mux-same-val (sym m≡) (sym v≡)

-- SignalsDisjoint is symmetric
signalsDisjoint-sym : ∀ {s₁ s₂} → SignalsDisjoint s₁ s₂ → SignalsDisjoint s₂ s₁
signalsDisjoint-sym (disjoint-left p) = disjoint-right p
signalsDisjoint-sym (disjoint-right p) = disjoint-left p

-- SignalPairValid is symmetric: if (sig₁, sig₂) is valid, so is (sig₂, sig₁)
signalPairValid-sym : ∀ {sig₁ sig₂} → SignalPairValid sig₁ sig₂ → SignalPairValid sig₂ sig₁
signalPairValid-sym (mutually-exclusive ¬coexist) =
  mutually-exclusive (λ coexist → ¬coexist (canCoexist-sym coexist))
signalPairValid-sym (disjoint-when-coexist coexist disj) =
  disjoint-when-coexist (canCoexist-sym coexist) (signalsDisjoint-sym disj)

-- Extract SignalPairValid from AllSignalPairsValid for any two distinct signals
-- Uses direct pattern matching on membership proofs to determine ordering
lookupSignalPairValid : ∀ {sig₁ sig₂ sigs}
  → AllSignalPairsValid sigs
  → sig₁ ∈ sigs
  → sig₂ ∈ sigs
  → sig₁ ≢ sig₂
  → SignalPairValid sig₁ sig₂
lookupSignalPairValid {sig₁} {sig₂} allValid sig₁∈ sig₂∈ sig₁≢sig₂ =
  extractHelper allValid sig₁∈ sig₂∈
  where
    -- Walk through both membership proofs to determine ordering and extract
    extractHelper : ∀ {sigs}
      → AllSignalPairsValid sigs
      → sig₁ ∈ sigs
      → sig₂ ∈ sigs
      → SignalPairValid sig₁ sig₂
    -- sig₁ is head, sig₂ is in tail → sig₁ before sig₂
    extractHelper (pairs-cons againstAll _) (here refl) (there sig₂∈) =
      extractFromValidAgainstAll againstAll sig₂∈
    -- sig₂ is head, sig₁ is in tail → sig₂ before sig₁, use symmetry
    extractHelper (pairs-cons againstAll _) (there sig₁∈) (here refl) =
      signalPairValid-sym (extractFromValidAgainstAll againstAll sig₁∈)
    -- Both in tail → recurse
    extractHelper (pairs-cons _ rest) (there sig₁∈) (there sig₂∈) =
      extractHelper rest sig₁∈ sig₂∈
    -- Both point to head → contradiction with sig₁ ≢ sig₂
    extractHelper _ (here refl) (here refl) = ⊥-elim (sig₁≢sig₂ refl)

-- Extract SignalsDisjoint from SignalPairValid when signals can coexist
extractDisjointness : ∀ {sig₁ sig₂}
  → SignalPairValid sig₁ sig₂
  → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
  → SignalsDisjoint (DBCSignal.signalDef sig₁) (DBCSignal.signalDef sig₂)
extractDisjointness (mutually-exclusive ¬coexist) coexist = ⊥-elim (¬coexist coexist)
extractDisjointness (disjoint-when-coexist _ disj) _ = disj

-- ============================================================================
-- CONVENIENCE: Full lookup from validated message
-- ============================================================================

-- Extract MessageValid from AllMessagesValid
extractMessageValid : ∀ {msg msgs}
  → AllMessagesValid msgs
  → msg ∈ msgs
  → MessageValid msg
extractMessageValid (msgs-cons mv _) (here refl) = mv
extractMessageValid (msgs-cons _ rest) (there msg∈) = extractMessageValid rest msg∈

-- Extract AllSignalPairsValid from MessageValid
extractSignalPairs : ∀ {msg} → MessageValid msg → AllSignalPairsValid (DBCMessage.signals msg)
extractSignalPairs (message-valid pairs _) = pairs

-- Full pipeline: from DBCValid to SignalsDisjoint
-- Given a valid DBC, a message in it, two distinct coexisting signals in that message,
-- extract the proof that they are disjoint
lookupDisjointFromDBC : ∀ {dbc msg sig₁ sig₂}
  → DBCValid dbc
  → msg ∈ DBC.messages dbc
  → sig₁ ∈ DBCMessage.signals msg
  → sig₂ ∈ DBCMessage.signals msg
  → sig₁ ≢ sig₂
  → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
  → SignalsDisjoint (DBCSignal.signalDef sig₁) (DBCSignal.signalDef sig₂)
lookupDisjointFromDBC dbcValid msg∈ sig₁∈ sig₂∈ sig≢ coexist =
  let msgValid = extractMessageValid dbcValid msg∈
      pairsValid = extractSignalPairs msgValid
      pairValid = lookupSignalPairValid pairsValid sig₁∈ sig₂∈ sig≢
  in extractDisjointness pairValid coexist
