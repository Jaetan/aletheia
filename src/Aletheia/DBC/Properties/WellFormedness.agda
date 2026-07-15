-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Proofs about DBC well-formedness: symmetry of the coexistence and
-- pair-validity relations, and proof extraction from a validated DBC to
-- `PhysicallyDisjoint` witnesses for any two coexisting signals of a message.
--
-- Proof-only: the predicates and their decision procedures live in the
-- runtime-facing `Aletheia.DBC.Decidable.WellFormedness`; this module proves
-- properties over them.
module Aletheia.DBC.Properties.WellFormedness where

open import Aletheia.DBC.Decidable.WellFormedness using
  ( ValuesOverlap
  ; CanCoexist; both-always; always-left; always-right; different-mux; same-mux-overlap
  ; SignalPairValid; mutually-exclusive; disjoint-when-coexist
  ; SignalValidAgainstAll; valid-cons
  ; AllSignalPairsValid; pairs-cons
  ; MessageValid; message-valid
  ; AllMessagesValid; msgs-cons
  ; DBCValid )
open import Aletheia.DBC.Decidable.Disjointness using (PhysicallyDisjoint)
open import Aletheia.DBC.Properties.Disjointness using (physicallyDisjoint-sym)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Data.List using (List; _∷_)
open import Data.List.NonEmpty using (toList)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

-- ============================================================================
-- SYMMETRY LEMMAS
-- ============================================================================

private
  insert-at : ∀ (v : ℕ) (xs ys : List ℕ) → Any (v ≡_) ys
    → Any (λ w → Any (w ≡_) (v ∷ xs)) ys
  insert-at v xs (_ ∷ _) (here v≡y) = here (here (sym v≡y))
  insert-at v xs (_ ∷ ys) (there rest) = there (insert-at v xs ys rest)

  weaken-any : ∀ {x : ℕ} {xs} (ys : List ℕ) → Any (λ w → Any (w ≡_) xs) ys
    → Any (λ w → Any (w ≡_) (x ∷ xs)) ys
  weaken-any (_ ∷ _)  (here inner)  = here (there inner)
  weaken-any (_ ∷ ys) (there rest)  = there (weaken-any ys rest)

  swap-any : ∀ (xs ys : List ℕ) → Any (λ v → Any (v ≡_) ys) xs
    → Any (λ v → Any (v ≡_) xs) ys
  swap-any (_ ∷ _)  ys (here inner)  = insert-at _ _ ys inner
  swap-any (_ ∷ xs) ys (there rest)  = weaken-any ys (swap-any xs ys rest)

valuesOverlap-sym : ∀ {vs₁ vs₂} → ValuesOverlap vs₁ vs₂ → ValuesOverlap vs₂ vs₁
valuesOverlap-sym {vs₁} {vs₂} = swap-any (toList vs₁) (toList vs₂)

canCoexist-sym : ∀ {p₁ p₂} → CanCoexist p₁ p₂ → CanCoexist p₂ p₁
canCoexist-sym both-always = both-always
canCoexist-sym always-left = always-right
canCoexist-sym always-right = always-left
canCoexist-sym (different-mux m≢) = different-mux (λ eq → m≢ (sym eq))
canCoexist-sym (same-mux-overlap m≡ ovl) = same-mux-overlap (sym m≡) (valuesOverlap-sym ovl)

-- ============================================================================
-- SIGNAL PAIR VALIDITY SYMMETRY
-- ============================================================================

signalPairValid-sym : ∀ {n sig₁ sig₂} → SignalPairValid n sig₁ sig₂ → SignalPairValid n sig₂ sig₁
signalPairValid-sym (mutually-exclusive ¬coexist) =
  mutually-exclusive (λ coexist → ¬coexist (canCoexist-sym coexist))
signalPairValid-sym {_} {sig₁} {sig₂} (disjoint-when-coexist coexist disj) =
  disjoint-when-coexist (canCoexist-sym coexist) (physicallyDisjoint-sym {_} {sig₁} {sig₂} disj)

-- ============================================================================
-- PROOF EXTRACTION: From validated DBC to signal disjointness proofs
-- ============================================================================

extractFromValidAgainstAll : ∀ {n sig₁ sig₂ sigs}
  → SignalValidAgainstAll n sig₁ sigs
  → sig₂ ∈ sigs
  → SignalPairValid n sig₁ sig₂
extractFromValidAgainstAll (valid-cons pv _) (here refl) = pv
extractFromValidAgainstAll (valid-cons _ rest) (there sig₂∈) = extractFromValidAgainstAll rest sig₂∈

lookupSignalPairValid : ∀ {n sig₁ sig₂ sigs}
  → AllSignalPairsValid n sigs
  → sig₁ ∈ sigs
  → sig₂ ∈ sigs
  → sig₁ ≢ sig₂
  → SignalPairValid n sig₁ sig₂
lookupSignalPairValid {_} {sig₁} {sig₂} allValid sig₁∈ sig₂∈ sig₁≢sig₂ =
  extractHelper allValid sig₁∈ sig₂∈
  where
    extractHelper : ∀ {sigs}
      → AllSignalPairsValid _ sigs
      → sig₁ ∈ sigs
      → sig₂ ∈ sigs
      → SignalPairValid _ sig₁ sig₂
    extractHelper (pairs-cons againstAll _) (here refl) (there sig₂∈) =
      extractFromValidAgainstAll againstAll sig₂∈
    extractHelper (pairs-cons againstAll _) (there sig₁∈) (here refl) =
      signalPairValid-sym (extractFromValidAgainstAll againstAll sig₁∈)
    extractHelper (pairs-cons _ rest) (there sig₁∈) (there sig₂∈) =
      extractHelper rest sig₁∈ sig₂∈
    extractHelper _ (here refl) (here refl) = ⊥-elim (sig₁≢sig₂ refl)

extractDisjointness : ∀ {n sig₁ sig₂}
  → SignalPairValid n sig₁ sig₂
  → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
  → PhysicallyDisjoint n sig₁ sig₂
extractDisjointness (mutually-exclusive ¬coexist) coexist = ⊥-elim (¬coexist coexist)
extractDisjointness (disjoint-when-coexist _ disj) _ = disj

extractMessageValid : ∀ {msg msgs}
  → AllMessagesValid msgs
  → msg ∈ msgs
  → MessageValid msg
extractMessageValid (msgs-cons mv _) (here refl) = mv
extractMessageValid (msgs-cons _ rest) (there msg∈) = extractMessageValid rest msg∈

extractSignalPairs : ∀ {msg}
  → MessageValid msg → AllSignalPairsValid (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg)
extractSignalPairs (message-valid pairs _) = pairs

lookupDisjointFromDBC : ∀ {dbc msg sig₁ sig₂}
  → DBCValid dbc
  → msg ∈ DBC.messages dbc
  → sig₁ ∈ DBCMessage.signals msg
  → sig₂ ∈ DBCMessage.signals msg
  → sig₁ ≢ sig₂
  → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
  → PhysicallyDisjoint (dlcBytes (DBCMessage.dlc msg)) sig₁ sig₂
lookupDisjointFromDBC dbcValid msg∈ sig₁∈ sig₂∈ sig≢ coexist =
  let msgValid = extractMessageValid dbcValid msg∈
      pairsValid = extractSignalPairs msgValid
      pairValid = lookupSignalPairValid pairsValid sig₁∈ sig₂∈ sig≢
  in extractDisjointness pairValid coexist
