-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal coexistence, pair validity, and message/DBC well-formedness, with their
-- decision procedures.
--
-- Runtime-facing: the predicates (`CanCoexist`, `SignalPairValid`, `MessageValid`,
-- `DBCValid`, …) and their deciders live here. The symmetry lemmas and the
-- proof-extraction functions (from a validated DBC to `PhysicallyDisjoint`
-- witnesses) live in the proof-only `Aletheia.DBC.Properties.WellFormedness`.
module Aletheia.DBC.Decidable.WellFormedness where

open import Aletheia.DBC.Decidable.Disjointness using (PhysicallyDisjoint; physicallyDisjoint?)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.Char using () renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List; []; _∷_)
import Data.List.Properties as ListProps
open import Data.List.NonEmpty using (List⁺; toList)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Aletheia.DBC.DecRat using (_≤ᵈ_; _≤?ᵈ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- ============================================================================
-- SIGNAL COEXISTENCE (for multiplexed signals)
-- ============================================================================

ValuesOverlap : List⁺ ℕ → List⁺ ℕ → Set
ValuesOverlap vs₁ vs₂ = Any (λ v → Any (v ≡_) (toList vs₂)) (toList vs₁)

valuesOverlap? : (vs₁ vs₂ : List⁺ ℕ) → Dec (ValuesOverlap vs₁ vs₂)
valuesOverlap? vs₁ vs₂ = any? (λ v → any? (v ≟_) (toList vs₂)) (toList vs₁)

-- Same-multiplexor predicate: two `When` presences share a multiplexor iff
-- their name Strings are propositionally equal.  Using name equality (rather
-- than `_≡_` on Identifier) avoids having to prove proof irrelevance for the
-- `@0 valid` witness, which would need the `fromList∘toList` axiom.
data CanCoexist : SignalPresence → SignalPresence → Set where
  both-always : CanCoexist Always Always
  always-left : ∀ {m vs} → CanCoexist Always (When m vs)
  always-right : ∀ {m vs} → CanCoexist (When m vs) Always
  different-mux : ∀ {m₁ m₂ vs₁ vs₂} → Identifier.name m₁ ≢ Identifier.name m₂
    → CanCoexist (When m₁ vs₁) (When m₂ vs₂)
  same-mux-overlap : ∀ {m₁ m₂ vs₁ vs₂} → Identifier.name m₁ ≡ Identifier.name m₂
    → ValuesOverlap vs₁ vs₂ → CanCoexist (When m₁ vs₁) (When m₂ vs₂)

canCoexist? : (p₁ p₂ : SignalPresence) → Dec (CanCoexist p₁ p₂)
canCoexist? Always Always = yes both-always
canCoexist? Always (When m vs) = yes always-left
canCoexist? (When m vs) Always = yes always-right
canCoexist? (When m₁ vs₁) (When m₂ vs₂) =
    helper (ListProps.≡-dec _≟ᶜ_ (Identifier.name m₁) (Identifier.name m₂))
           (valuesOverlap? vs₁ vs₂)
  where
    helper : Dec (Identifier.name m₁ ≡ Identifier.name m₂) → Dec (ValuesOverlap vs₁ vs₂)
      → Dec (CanCoexist (When m₁ vs₁) (When m₂ vs₂))
    helper (yes m≡) (yes ovl) = yes (same-mux-overlap m≡ ovl)
    helper (yes m≡) (no ¬ovl) = no λ where
      (different-mux m≢) → m≢ m≡
      (same-mux-overlap _ ovl) → ¬ovl ovl
    helper (no m≢) _ = yes (different-mux m≢)

-- ============================================================================
-- SIGNAL PAIR VALIDITY
-- ============================================================================

data SignalPairValid (n : ℕ) (sig₁ sig₂ : DBCSignal) : Set where
  mutually-exclusive :
    ¬ CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
    → SignalPairValid n sig₁ sig₂
  disjoint-when-coexist :
    CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
    → PhysicallyDisjoint n sig₁ sig₂
    → SignalPairValid n sig₁ sig₂

signalPairValid? : (n : ℕ) → (sig₁ sig₂ : DBCSignal) → Dec (SignalPairValid n sig₁ sig₂)
signalPairValid? n sig₁ sig₂ with canCoexist? (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
... | no ¬coexist = yes (mutually-exclusive ¬coexist)
... | yes coexist with physicallyDisjoint? n sig₁ sig₂
...   | yes disj = yes (disjoint-when-coexist coexist disj)
...   | no ¬disj = no λ where
        (mutually-exclusive ¬coexist) → ¬coexist coexist
        (disjoint-when-coexist _ disj) → ¬disj disj

-- ============================================================================
-- ALL PAIRS VALIDITY
-- ============================================================================

data SignalValidAgainstAll (n : ℕ) (sig : DBCSignal) : List DBCSignal → Set where
  valid-nil : SignalValidAgainstAll n sig []
  valid-cons : ∀ {other rest}
    → SignalPairValid n sig other
    → SignalValidAgainstAll n sig rest
    → SignalValidAgainstAll n sig (other ∷ rest)

signalValidAgainstAll? : (n : ℕ) → (sig : DBCSignal) → (others : List DBCSignal)
                       → Dec (SignalValidAgainstAll n sig others)
signalValidAgainstAll? n sig [] = yes valid-nil
signalValidAgainstAll? n sig (other ∷ rest) with signalPairValid? n sig other
... | no ¬valid = no λ where (valid-cons v _) → ¬valid v
... | yes valid with signalValidAgainstAll? n sig rest
...   | no ¬rest = no λ where (valid-cons _ r) → ¬rest r
...   | yes restValid = yes (valid-cons valid restValid)

data AllSignalPairsValid (n : ℕ) : List DBCSignal → Set where
  pairs-nil : AllSignalPairsValid n []
  pairs-cons : ∀ {sig rest}
    → SignalValidAgainstAll n sig rest
    → AllSignalPairsValid n rest
    → AllSignalPairsValid n (sig ∷ rest)

allSignalPairsValid? : (n : ℕ) → (sigs : List DBCSignal) → Dec (AllSignalPairsValid n sigs)
allSignalPairsValid? n [] = yes pairs-nil
allSignalPairsValid? n (sig ∷ rest) with signalValidAgainstAll? n sig rest
... | no ¬valid = no λ where (pairs-cons v _) → ¬valid v
... | yes valid with allSignalPairsValid? n rest
...   | no ¬rest = no λ where (pairs-cons _ r) → ¬rest r
...   | yes restValid = yes (pairs-cons valid restValid)

messageSignalsValid? : (msg : DBCMessage)
                     → Dec (AllSignalPairsValid (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg))
messageSignalsValid? msg = allSignalPairsValid? (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg)

-- ============================================================================
-- SIGNAL RANGE CONSISTENCY
-- ============================================================================

SignalRangeConsistent : DBCSignal → Set
SignalRangeConsistent sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in minimum ≤ᵈ maximum

signalRangeConsistent? : (sig : DBCSignal) → Dec (SignalRangeConsistent sig)
signalRangeConsistent? sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in minimum ≤?ᵈ maximum

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
-- COMPLETE MESSAGE AND DBC VALIDITY
-- ============================================================================

data MessageValid (msg : DBCMessage) : Set where
  message-valid :
    AllSignalPairsValid (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg)
    → AllSignalRangesConsistent (DBCMessage.signals msg)
    → MessageValid msg

messageValid? : (msg : DBCMessage) → Dec (MessageValid msg)
messageValid? msg with messageSignalsValid? msg
... | no ¬pairs = no λ where (message-valid p _) → ¬pairs p
... | yes pairs with allSignalRangesConsistent? (DBCMessage.signals msg)
...   | no ¬ranges = no λ where (message-valid _ r) → ¬ranges r
...   | yes ranges = yes (message-valid pairs ranges)

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

DBCValid : DBC → Set
DBCValid dbc = AllMessagesValid (DBC.messages dbc)

dbcValid? : (dbc : DBC) → Dec (DBCValid dbc)
dbcValid? dbc = allMessagesValid? (DBC.messages dbc)
