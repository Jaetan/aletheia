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
open import Aletheia.CAN.Endianness using (ByteOrder; physicalBitPos; _≟-ByteOrder_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_) renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties using (_≤?_) renaming (_≟_ to _≟ₙ_)
open import Data.Rational using (ℚ; _≤_)
open import Data.Rational.Properties using () renaming (_≟_ to _≟ᵣ_; _≤?_ to _≤?ᵣ_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)

-- ============================================================================
-- BASIC STRUCTURAL PROPERTIES
-- ============================================================================

-- Note: Signal start bits, bit lengths, DLC, and CAN IDs are now ℕ.
-- Bounds are enforced at parse time: JSONParser uses % max-physical-bits (512)
-- for startBit, % (1 + max-physical-bits) for bitLength; Routing uses
-- % standard-can-id-max / % extended-can-id-max for CAN IDs, and ≤? 15 for DLC.

-- ============================================================================
-- DECIDABLE EQUALITY FOR DBC TYPES
-- ============================================================================

-- Decidable equality for SignalPresence
_≟-SignalPresence_ : (p₁ p₂ : SignalPresence) → Dec (p₁ ≡ p₂)
Always     ≟-SignalPresence Always     = yes refl
Always     ≟-SignalPresence When _ _   = no (λ ())
When _ _   ≟-SignalPresence Always     = no (λ ())
When m₁ v₁ ≟-SignalPresence When m₂ v₂ with m₁ ≟ₛ m₂ | v₁ ≟ₙ v₂
... | yes refl | yes refl = yes refl
... | no  m≢   | _        = no (λ { refl → m≢ refl })
... | _        | no  v≢   = no (λ { refl → v≢ refl })

-- Decidable equality for SignalDef (7 fields)
_≟-SignalDef_ : (s₁ s₂ : SignalDef) → Dec (s₁ ≡ s₂)
s₁ ≟-SignalDef s₂
  with SignalDef.startBit s₁ ≟ₙ SignalDef.startBit s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.startBit eq))
... | yes refl
  with SignalDef.bitLength s₁ ≟ₙ SignalDef.bitLength s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.bitLength eq))
... | yes refl
  with SignalDef.isSigned s₁ ≟ᵇ SignalDef.isSigned s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.isSigned eq))
... | yes refl
  with SignalDef.factor s₁ ≟ᵣ SignalDef.factor s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.factor eq))
... | yes refl
  with SignalDef.offset s₁ ≟ᵣ SignalDef.offset s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.offset eq))
... | yes refl
  with SignalDef.minimum s₁ ≟ᵣ SignalDef.minimum s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.minimum eq))
... | yes refl
  with SignalDef.maximum s₁ ≟ᵣ SignalDef.maximum s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.maximum eq))
... | yes refl = yes refl

-- Decidable equality for DBCSignal (5 fields)
_≟-DBCSignal_ : (s₁ s₂ : DBCSignal) → Dec (s₁ ≡ s₂)
s₁ ≟-DBCSignal s₂
  with DBCSignal.name s₁ ≟ₛ DBCSignal.name s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.name eq))
... | yes refl
  with DBCSignal.signalDef s₁ ≟-SignalDef DBCSignal.signalDef s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.signalDef eq))
... | yes refl
  with DBCSignal.byteOrder s₁ ≟-ByteOrder DBCSignal.byteOrder s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.byteOrder eq))
... | yes refl
  with DBCSignal.unit s₁ ≟ₛ DBCSignal.unit s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.unit eq))
... | yes refl
  with DBCSignal.presence s₁ ≟-SignalPresence DBCSignal.presence s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.presence eq))
... | yes refl = yes refl

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
-- PHYSICAL DISJOINTNESS (for mixed byte order support)
-- ============================================================================

-- Two signals are physically disjoint if no physical bit positions overlap.
-- This is the correct disjointness notion for mixed byte orders:
-- LE signals use identity mapping, BE signals use byte-reversed mapping.
-- n is the frame byte count (e.g. 8 for CAN 2.0B, up to 64 for CAN-FD).
PhysicallyDisjoint : ℕ → DBCSignal → DBCSignal → Set
PhysicallyDisjoint n sig₁ sig₂ =
  ∀ k₁ → k₁ < SignalDef.bitLength (DBCSignal.signalDef sig₁)
  → ∀ k₂ → k₂ < SignalDef.bitLength (DBCSignal.signalDef sig₂)
  → physicalBitPos n (DBCSignal.byteOrder sig₁)
      (SignalDef.startBit (DBCSignal.signalDef sig₁) + k₁)
    ≢ physicalBitPos n (DBCSignal.byteOrder sig₂)
      (SignalDef.startBit (DBCSignal.signalDef sig₂) + k₂)

-- Symmetry of physical disjointness
physicallyDisjoint-sym : ∀ {n sig₁ sig₂}
  → PhysicallyDisjoint n sig₁ sig₂ → PhysicallyDisjoint n sig₂ sig₁
physicallyDisjoint-sym pd k₂ k₂<l₂ k₁ k₁<l₁ eq = pd k₁ k₁<l₁ k₂ k₂<l₂ (sym eq)

-- Decidable bounded universal quantifier
private
  allBounded : ∀ {P : ℕ → Set}
    → (∀ k → Dec (P k))
    → (n : ℕ)
    → Dec (∀ k → k < n → P k)
  allBounded _ zero = yes (λ _ ())
  allBounded decide (suc n) with decide n | allBounded decide n
  ... | no ¬pn | _ = no (λ f → ¬pn (f n (Data.Nat.Properties.≤-refl)))
    where open import Data.Nat.Properties using (≤-refl)
  ... | _ | no ¬rest = no (λ f → ¬rest (λ k k<n → f k (Data.Nat.Properties.m≤n⇒m≤1+n k<n)))
    where open import Data.Nat.Properties using (m≤n⇒m≤1+n)
  ... | yes pn | yes rest = yes lemma
    where
      open import Data.Nat using (z≤n; s≤s)
      lemma : ∀ k → k < suc n → _
      lemma k (s≤s k≤n) with k ≟ₙ n
      ... | yes refl = pn
      ... | no k≢n = rest k (Data.Nat.Properties.≤∧≢⇒< k≤n k≢n)
        where open import Data.Nat.Properties using (≤∧≢⇒<)

-- Decidable check for physical disjointness
physicallyDisjoint? : (n : ℕ) → (sig₁ sig₂ : DBCSignal) → Dec (PhysicallyDisjoint n sig₁ sig₂)
physicallyDisjoint? n sig₁ sig₂ =
  allBounded
    (λ k₁ → allBounded
      (λ k₂ → case physicalBitPos n bo₁ (s₁ + k₁) ≟ₙ physicalBitPos n bo₂ (s₂ + k₂) of λ where
        (yes eq) → no (λ neq → neq eq)
        (no neq) → yes neq)
      l₂)
    l₁
  where
    open SignalDef (DBCSignal.signalDef sig₁) renaming (startBit to s₁; bitLength to l₁)
    open SignalDef (DBCSignal.signalDef sig₂) renaming (startBit to s₂; bitLength to l₂)
    bo₁ = DBCSignal.byteOrder sig₁
    bo₂ = DBCSignal.byteOrder sig₂

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
-- Either they can't coexist (mutually exclusive), or they are physically disjoint
data SignalPairValid (n : ℕ) (sig₁ sig₂ : DBCSignal) : Set where
  mutually-exclusive :
    ¬ CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
    → SignalPairValid n sig₁ sig₂
  disjoint-when-coexist :
    CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
    → PhysicallyDisjoint n sig₁ sig₂
    → SignalPairValid n sig₁ sig₂

-- Decidable check for signal pair validity
signalPairValid? : (n : ℕ) → (sig₁ sig₂ : DBCSignal) → Dec (SignalPairValid n sig₁ sig₂)
signalPairValid? n sig₁ sig₂ with canCoexist? (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
... | no ¬coexist = yes (mutually-exclusive ¬coexist)
... | yes coexist with physicallyDisjoint? n sig₁ sig₂
...   | yes disj = yes (disjoint-when-coexist coexist disj)
...   | no ¬disj = no λ where
        (mutually-exclusive ¬coexist) → ¬coexist coexist
        (disjoint-when-coexist _ disj) → ¬disj disj

-- ============================================================================
-- ALL PAIRS VALIDITY (for a list of signals)
-- ============================================================================

-- Check one signal against all others in a list
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

-- All pairs in a list are valid (triangular check: each signal against all following)
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

-- Message signals are valid if all pairs are valid (using message's own DLC as byte count)
messageSignalsValid? : (msg : DBCMessage)
                     → Dec (AllSignalPairsValid (DBCMessage.dlc msg) (DBCMessage.signals msg))
messageSignalsValid? msg = allSignalPairsValid? (DBCMessage.dlc msg) (DBCMessage.signals msg)

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
-- Uses the message's own DLC for physical disjointness checking
data MessageValid (msg : DBCMessage) : Set where
  message-valid :
    AllSignalPairsValid (DBCMessage.dlc msg) (DBCMessage.signals msg)
    → AllSignalRangesConsistent (DBCMessage.signals msg)
    → MessageValid msg

messageValid? : (msg : DBCMessage) → Dec (MessageValid msg)
messageValid? msg with messageSignalsValid? msg
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
extractFromValidAgainstAll : ∀ {n sig₁ sig₂ sigs}
  → SignalValidAgainstAll n sig₁ sigs
  → sig₂ ∈ sigs
  → SignalPairValid n sig₁ sig₂
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
signalPairValid-sym : ∀ {n sig₁ sig₂} → SignalPairValid n sig₁ sig₂ → SignalPairValid n sig₂ sig₁
signalPairValid-sym (mutually-exclusive ¬coexist) =
  mutually-exclusive (λ coexist → ¬coexist (canCoexist-sym coexist))
signalPairValid-sym {_} {sig₁} {sig₂} (disjoint-when-coexist coexist disj) =
  disjoint-when-coexist (canCoexist-sym coexist) (physicallyDisjoint-sym {_} {sig₁} {sig₂} disj)

-- Extract SignalPairValid from AllSignalPairsValid for any two distinct signals
-- Uses direct pattern matching on membership proofs to determine ordering
lookupSignalPairValid : ∀ {n sig₁ sig₂ sigs}
  → AllSignalPairsValid n sigs
  → sig₁ ∈ sigs
  → sig₂ ∈ sigs
  → sig₁ ≢ sig₂
  → SignalPairValid n sig₁ sig₂
lookupSignalPairValid {_} {sig₁} {sig₂} allValid sig₁∈ sig₂∈ sig₁≢sig₂ =
  extractHelper allValid sig₁∈ sig₂∈
  where
    -- Walk through both membership proofs to determine ordering and extract
    extractHelper : ∀ {sigs}
      → AllSignalPairsValid _ sigs
      → sig₁ ∈ sigs
      → sig₂ ∈ sigs
      → SignalPairValid _ sig₁ sig₂
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

-- Extract PhysicallyDisjoint from SignalPairValid when signals can coexist
extractDisjointness : ∀ {n sig₁ sig₂}
  → SignalPairValid n sig₁ sig₂
  → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
  → PhysicallyDisjoint n sig₁ sig₂
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
extractSignalPairs : ∀ {msg}
  → MessageValid msg → AllSignalPairsValid (DBCMessage.dlc msg) (DBCMessage.signals msg)
extractSignalPairs (message-valid pairs _) = pairs

-- Full pipeline: from DBCValid to PhysicallyDisjoint
-- Given a valid DBC, a message in it, two distinct coexisting signals in that message,
-- extract the proof that they are physically disjoint (using the message's DLC)
lookupDisjointFromDBC : ∀ {dbc msg sig₁ sig₂}
  → DBCValid dbc
  → msg ∈ DBC.messages dbc
  → sig₁ ∈ DBCMessage.signals msg
  → sig₂ ∈ DBCMessage.signals msg
  → sig₁ ≢ sig₂
  → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
  → PhysicallyDisjoint (DBCMessage.dlc msg) sig₁ sig₂
lookupDisjointFromDBC dbcValid msg∈ sig₁∈ sig₂∈ sig≢ coexist =
  let msgValid = extractMessageValid dbcValid msg∈
      pairsValid = extractSignalPairs msgValid
      pairValid = lookupSignalPairValid pairsValid sig₁∈ sig₂∈ sig≢
  in extractDisjointness pairValid coexist
