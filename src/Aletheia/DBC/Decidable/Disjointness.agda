-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal disjointness predicates with their decision procedures, plus the fast
-- Bool-valued physical-overlap check.
--
-- Runtime-facing: the decision procedures (`signalsDisjoint?`,
-- `physicallyDisjoint?`) and the precomputation-friendly overlap check
-- (`signalsPhysicallyOverlapᵇ`) live here. Their soundness/completeness proofs
-- linking the Bool check to `PhysicallyDisjoint` live in the proof-only
-- `Aletheia.DBC.Properties.Disjointness`.
module Aletheia.DBC.Decidable.Disjointness where

open import Aletheia.DBC.Types using (DBCSignal)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; physicalBitPos)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≡ᵇ_; s≤s)
open import Data.Nat.Properties using (_≟_; _≤?_; ≤-refl; m≤n⇒m≤1+n; ≤∧≢⇒<)
open import Data.Bool using (Bool; false; _∨_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (case_of_)

-- ============================================================================
-- LOGICAL SIGNAL DISJOINTNESS
-- ============================================================================

-- Two signals are disjoint if their bit ranges don't overlap
data SignalsDisjoint (sig₁ sig₂ : SignalDef) : Set where
  disjoint-left :
    SignalDef.startBit sig₁ + SignalDef.bitLength sig₁
      ≤ SignalDef.startBit sig₂
    → SignalsDisjoint sig₁ sig₂
  disjoint-right :
    SignalDef.startBit sig₂ + SignalDef.bitLength sig₂
      ≤ SignalDef.startBit sig₁
    → SignalsDisjoint sig₁ sig₂

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

-- n is the frame byte count (e.g. 8 for CAN 2.0B, up to 64 for CAN-FD).
PhysicallyDisjoint : ℕ → DBCSignal → DBCSignal → Set
PhysicallyDisjoint n sig₁ sig₂ =
  ∀ k₁ → k₁ < SignalDef.bitLength (DBCSignal.signalDef sig₁)
  → ∀ k₂ → k₂ < SignalDef.bitLength (DBCSignal.signalDef sig₂)
  → physicalBitPos n (DBCSignal.byteOrder sig₁)
      (SignalDef.startBit (DBCSignal.signalDef sig₁) + k₁)
    ≢ physicalBitPos n (DBCSignal.byteOrder sig₂)
      (SignalDef.startBit (DBCSignal.signalDef sig₂) + k₂)

-- Decidable bounded universal quantifier
private
  allBounded : ∀ {P : ℕ → Set}
    → (∀ k → Dec (P k))
    → (n : ℕ)
    → Dec (∀ k → k < n → P k)
  allBounded _ zero = yes (λ _ ())
  allBounded decide (suc n) with decide n | allBounded decide n
  ... | no ¬pn | _ = no (λ f → ¬pn (f n (Data.Nat.Properties.≤-refl)))

  ... | _ | no ¬rest = no (λ f → ¬rest (λ k k<n → f k (Data.Nat.Properties.m≤n⇒m≤1+n k<n)))

  ... | yes pn | yes rest = yes lemma
    where
      lemma : ∀ k → k < suc n → _
      lemma k (s≤s k≤n) with k ≟ n
      ... | yes refl = pn
      ... | no k≢n = rest k (Data.Nat.Properties.≤∧≢⇒< k≤n k≢n)


physicallyDisjoint? : (n : ℕ) → (sig₁ sig₂ : DBCSignal) → Dec (PhysicallyDisjoint n sig₁ sig₂)
physicallyDisjoint? n sig₁ sig₂ =
  allBounded
    (λ k₁ → allBounded
      (λ k₂ → case physicalBitPos n bo₁ (s₁ + k₁) ≟ physicalBitPos n bo₂ (s₂ + k₂) of λ where
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
-- FAST PHYSICAL OVERLAP CHECK (Bool-valued, precomputation-friendly)
-- ============================================================================

buildPhysicalBits : (n : ℕ) → ByteOrder → (s r k : ℕ) → List ℕ
buildPhysicalBits n bo s zero    _ = []
buildPhysicalBits n bo s (suc r) k =
  physicalBitPos n bo (s + k) ∷ buildPhysicalBits n bo s r (suc k)

signalPhysicalBits : ℕ → DBCSignal → List ℕ
signalPhysicalBits n sig =
  buildPhysicalBits n
    (DBCSignal.byteOrder sig)
    (SignalDef.startBit (DBCSignal.signalDef sig))
    (SignalDef.bitLength (DBCSignal.signalDef sig))
    0

bitsMemberᵇ : ℕ → List ℕ → Bool
bitsMemberᵇ _ []       = false
bitsMemberᵇ x (y ∷ ys) = (x ≡ᵇ y) ∨ bitsMemberᵇ x ys

bitsIntersectᵇ : List ℕ → List ℕ → Bool
bitsIntersectᵇ []       _   = false
bitsIntersectᵇ (x ∷ xs) ys  = bitsMemberᵇ x ys ∨ bitsIntersectᵇ xs ys

signalsPhysicallyOverlapᵇ : ℕ → DBCSignal → DBCSignal → Bool
signalsPhysicallyOverlapᵇ n sig₁ sig₂ =
  bitsIntersectᵇ (signalPhysicalBits n sig₁) (signalPhysicalBits n sig₂)
