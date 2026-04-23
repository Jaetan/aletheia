{-# OPTIONS --safe --without-K #-}

-- Signal coexistence, pair validity, DBC well-formedness, and proof extraction.
--
-- Purpose: Define when signal pairs are valid (mutually exclusive or physically
--   disjoint), compose into message/DBC validity, and provide proof extraction
--   from validated DBCs to PhysicallyDisjoint witnesses.
-- Key results: DBCValid, lookupDisjointFromDBC.
module Aletheia.DBC.Properties.WellFormedness where

open import Aletheia.DBC.Properties.Disjointness using
  ( PhysicallyDisjoint; physicallyDisjoint-sym; physicallyDisjoint?
  ; SignalsDisjoint; signalsDisjoint-sym)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; toList)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Aletheia.DBC.DecRat using (_≤ᵈ_; _≤?ᵈ_)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)

-- ============================================================================
-- SIGNAL COEXISTENCE (for multiplexed signals)
-- ============================================================================

ValuesOverlap : List⁺ ℕ → List⁺ ℕ → Set
ValuesOverlap vs₁ vs₂ = Any (λ v → Any (v ≡_) (toList vs₂)) (toList vs₁)

valuesOverlap? : (vs₁ vs₂ : List⁺ ℕ) → Dec (ValuesOverlap vs₁ vs₂)
valuesOverlap? vs₁ vs₂ = any? (λ v → any? (v ≟_) (toList vs₂)) (toList vs₁)

data CanCoexist : SignalPresence → SignalPresence → Set where
  both-always : CanCoexist Always Always
  always-left : ∀ {m vs} → CanCoexist Always (When m vs)
  always-right : ∀ {m vs} → CanCoexist (When m vs) Always
  different-mux : ∀ {m₁ m₂ vs₁ vs₂} → m₁ ≢ m₂ → CanCoexist (When m₁ vs₁) (When m₂ vs₂)
  same-mux-overlap : ∀ {m₁ m₂ vs₁ vs₂} → m₁ ≡ m₂ → ValuesOverlap vs₁ vs₂ → CanCoexist (When m₁ vs₁) (When m₂ vs₂)

canCoexist? : (p₁ p₂ : SignalPresence) → Dec (CanCoexist p₁ p₂)
canCoexist? Always Always = yes both-always
canCoexist? Always (When m vs) = yes always-left
canCoexist? (When m vs) Always = yes always-right
canCoexist? (When m₁ vs₁) (When m₂ vs₂) = helper (m₁ ≟ₛ m₂) (valuesOverlap? vs₁ vs₂)
  where
    helper : Dec (m₁ ≡ m₂) → Dec (ValuesOverlap vs₁ vs₂) → Dec (CanCoexist (When m₁ vs₁) (When m₂ vs₂))
    helper (yes m≡) (yes ovl) = yes (same-mux-overlap m≡ ovl)
    helper (yes m≡) (no ¬ovl) = no λ where
      (different-mux m≢) → m≢ m≡
      (same-mux-overlap _ ovl) → ¬ovl ovl
    helper (no m≢) _ = yes (different-mux m≢)

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

signalPairValid-sym : ∀ {n sig₁ sig₂} → SignalPairValid n sig₁ sig₂ → SignalPairValid n sig₂ sig₁
signalPairValid-sym (mutually-exclusive ¬coexist) =
  mutually-exclusive (λ coexist → ¬coexist (canCoexist-sym coexist))
signalPairValid-sym {_} {sig₁} {sig₂} (disjoint-when-coexist coexist disj) =
  disjoint-when-coexist (canCoexist-sym coexist) (physicallyDisjoint-sym {_} {sig₁} {sig₂} disj)

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
