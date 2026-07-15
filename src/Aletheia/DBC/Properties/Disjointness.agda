-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Proofs about signal disjointness: symmetry of the disjointness relations, and
-- soundness/completeness of the fast Bool-valued overlap check against the
-- semantic `PhysicallyDisjoint` predicate.
--
-- Proof-only: the predicates and their decision procedures live in the
-- runtime-facing `Aletheia.DBC.Decidable.Disjointness`; this module proves the
-- properties that relate them (`physicallyOverlapᵇ-sound`,
-- `physicallyOverlapᵇ-complete`).
module Aletheia.DBC.Properties.Disjointness where

open import Aletheia.DBC.Decidable.Disjointness using
  ( SignalsDisjoint; disjoint-left; disjoint-right
  ; PhysicallyDisjoint
  ; buildPhysicalBits; signalPhysicalBits
  ; bitsMemberᵇ; bitsIntersectᵇ; signalsPhysicallyOverlapᵇ
  )
open import Aletheia.DBC.Types using (DBCSignal)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (physicalBitPos)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-identityʳ; +-suc)
open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Bool.Properties using (∨-conicalˡ; ∨-conicalʳ)

-- Symmetry
signalsDisjoint-sym : ∀ {s₁ s₂} → SignalsDisjoint s₁ s₂ → SignalsDisjoint s₂ s₁
signalsDisjoint-sym (disjoint-left p) = disjoint-right p
signalsDisjoint-sym (disjoint-right p) = disjoint-left p

physicallyDisjoint-sym : ∀ {n sig₁ sig₂}
  → PhysicallyDisjoint n sig₁ sig₂ → PhysicallyDisjoint n sig₂ sig₁
physicallyDisjoint-sym pd k₂ k₂<l₂ k₁ k₁<l₁ eq = pd k₁ k₁<l₁ k₂ k₂<l₂ (sym eq)

-- ============================================================================
-- EQUIVALENCE: signalsPhysicallyOverlapᵇ ⇔ ¬ PhysicallyDisjoint
-- ============================================================================

private
  ∨-true-split : ∀ {x y} → x ∨ y ≡ true → (x ≡ true) ⊎ (y ≡ true)
  ∨-true-split {true}  {_}     _  = inj₁ refl
  ∨-true-split {false} {true}  _  = inj₂ refl
  ∨-true-split {false} {false} ()

  ≡ᵇ-false→≢ : ∀ x y → (x ≡ᵇ y) ≡ false → x ≢ y
  ≡ᵇ-false→≢ x y eq x≡y = subst T eq (≡⇒≡ᵇ x y x≡y)

bitsMemberᵇ-false-absent : ∀ x xs
  → bitsMemberᵇ x xs ≡ false
  → (y : ℕ) → Any (_≡_ y) xs → x ≢ y
bitsMemberᵇ-false-absent x [] _ _ ()
bitsMemberᵇ-false-absent x (z ∷ zs) eq y (here y≡z) x≡y =
  ≡ᵇ-false→≢ x z (∨-conicalˡ _ _ eq) (trans x≡y y≡z)
bitsMemberᵇ-false-absent x (z ∷ zs) eq y (there y∈zs) =
  bitsMemberᵇ-false-absent x zs (∨-conicalʳ _ _ eq) y y∈zs

bitsIntersectᵇ-false-disjoint : ∀ xs ys
  → bitsIntersectᵇ xs ys ≡ false
  → (x y : ℕ) → Any (_≡_ x) xs → Any (_≡_ y) ys → x ≢ y
bitsIntersectᵇ-false-disjoint [] _ _ _ _ () _
bitsIntersectᵇ-false-disjoint (z ∷ zs) ys eq x y (here x≡z) y∈ys x≡y =
  bitsMemberᵇ-false-absent z ys (∨-conicalˡ _ _ eq) y y∈ys
    (trans (sym x≡z) x≡y)
bitsIntersectᵇ-false-disjoint (z ∷ zs) ys eq x y (there x∈zs) y∈ys =
  bitsIntersectᵇ-false-disjoint zs ys (∨-conicalʳ _ _ eq) x y x∈zs y∈ys

buildPhysicalBits-∈ : ∀ n bo s r k i
  → i < r
  → Any (physicalBitPos n bo (s + (k + i)) ≡_) (buildPhysicalBits n bo s r k)
buildPhysicalBits-∈ n bo s (suc r) k zero (s≤s z≤n)
  rewrite +-identityʳ k = here refl
buildPhysicalBits-∈ n bo s (suc r) k (suc i) (s≤s i<r)
  rewrite +-suc k i = there (buildPhysicalBits-∈ n bo s r (suc k) i i<r)

signalPhysicalBits-∈ : ∀ n sig i
  → i < SignalDef.bitLength (DBCSignal.signalDef sig)
  → Any (physicalBitPos n (DBCSignal.byteOrder sig)
          (SignalDef.startBit (DBCSignal.signalDef sig) + i) ≡_)
         (signalPhysicalBits n sig)
signalPhysicalBits-∈ n sig i i<l =
  buildPhysicalBits-∈ n
    (DBCSignal.byteOrder sig)
    (SignalDef.startBit (DBCSignal.signalDef sig))
    (SignalDef.bitLength (DBCSignal.signalDef sig))
    0 i i<l

-- Soundness: fast check reports no overlap → PhysicallyDisjoint holds
physicallyOverlapᵇ-sound : ∀ n sig₁ sig₂
  → signalsPhysicallyOverlapᵇ n sig₁ sig₂ ≡ false
  → PhysicallyDisjoint n sig₁ sig₂
physicallyOverlapᵇ-sound n sig₁ sig₂ no-overlap k₁ k₁<l₁ k₂ k₂<l₂ bit-eq =
  bitsIntersectᵇ-false-disjoint
    (signalPhysicalBits n sig₁)
    (signalPhysicalBits n sig₂)
    no-overlap
    _ _
    (signalPhysicalBits-∈ n sig₁ k₁ k₁<l₁)
    (signalPhysicalBits-∈ n sig₂ k₂ k₂<l₂)
    bit-eq

buildPhysicalBits-∈→offset : ∀ n bo s r k x
  → Any (_≡_ x) (buildPhysicalBits n bo s r k)
  → Σ[ i ∈ ℕ ] (i < r × x ≡ physicalBitPos n bo (s + (k + i)))
buildPhysicalBits-∈→offset n bo s zero k x ()
buildPhysicalBits-∈→offset n bo s (suc r) k x (here x≡p) =
  0 , s≤s z≤n ,
  trans x≡p (cong (λ t → physicalBitPos n bo (s + t)) (sym (+-identityʳ k)))
buildPhysicalBits-∈→offset n bo s (suc r) k x (there rest)
  with buildPhysicalBits-∈→offset n bo s r (suc k) x rest
... | i , i<r , x≡p =
  suc i , s≤s i<r ,
  trans x≡p (cong (λ t → physicalBitPos n bo (s + t)) (sym (+-suc k i)))

signalPhysicalBits-∈→offset : ∀ n sig x
  → Any (_≡_ x) (signalPhysicalBits n sig)
  → Σ[ k ∈ ℕ ] (k < SignalDef.bitLength (DBCSignal.signalDef sig)
              × x ≡ physicalBitPos n (DBCSignal.byteOrder sig)
                    (SignalDef.startBit (DBCSignal.signalDef sig) + k))
signalPhysicalBits-∈→offset n sig x mem =
  buildPhysicalBits-∈→offset n
    (DBCSignal.byteOrder sig)
    (SignalDef.startBit (DBCSignal.signalDef sig))
    (SignalDef.bitLength (DBCSignal.signalDef sig))
    0 x mem

bitsMemberᵇ-true→∈ : ∀ x xs → bitsMemberᵇ x xs ≡ true → Any (_≡_ x) xs
bitsMemberᵇ-true→∈ x [] ()
bitsMemberᵇ-true→∈ x (y ∷ ys) eq with ∨-true-split {x ≡ᵇ y} {bitsMemberᵇ x ys} eq
... | inj₁ ≡ᵇ-true  = here (≡ᵇ⇒≡ x y (subst T (sym ≡ᵇ-true) tt))
... | inj₂ mem-true = there (bitsMemberᵇ-true→∈ x ys mem-true)

bitsIntersectᵇ-true→witness : ∀ xs ys
  → bitsIntersectᵇ xs ys ≡ true
  → Σ[ x ∈ ℕ ] (Any (_≡_ x) xs × Any (_≡_ x) ys)
bitsIntersectᵇ-true→witness [] _ ()
bitsIntersectᵇ-true→witness (x ∷ xs) ys eq with ∨-true-split {bitsMemberᵇ x ys} {bitsIntersectᵇ xs ys} eq
... | inj₁ mem-true  = x , here refl , bitsMemberᵇ-true→∈ x ys mem-true
... | inj₂ rest-true with bitsIntersectᵇ-true→witness xs ys rest-true
... | w , w∈xs , w∈ys = w , there w∈xs , w∈ys

-- Completeness: PhysicallyDisjoint holds → fast check reports no overlap
physicallyOverlapᵇ-complete : ∀ n sig₁ sig₂
  → PhysicallyDisjoint n sig₁ sig₂
  → signalsPhysicallyOverlapᵇ n sig₁ sig₂ ≡ false
physicallyOverlapᵇ-complete n sig₁ sig₂ disj
  with signalsPhysicallyOverlapᵇ n sig₁ sig₂ in overlap-eq
... | false = refl
... | true  = ⊥-elim (contradiction overlap-eq)
  where
    contradiction : signalsPhysicallyOverlapᵇ n sig₁ sig₂ ≡ true → ⊥
    contradiction eq
      with bitsIntersectᵇ-true→witness (signalPhysicalBits n sig₁) (signalPhysicalBits n sig₂) eq
    ... | x , x∈₁ , x∈₂
      with signalPhysicalBits-∈→offset n sig₁ x x∈₁
         | signalPhysicalBits-∈→offset n sig₂ x x∈₂
    ... | k₁ , k₁<l₁ , x≡₁ | k₂ , k₂<l₂ , x≡₂ =
      disj k₁ k₁<l₁ k₂ k₂<l₂ (trans (sym x≡₁) x≡₂)
