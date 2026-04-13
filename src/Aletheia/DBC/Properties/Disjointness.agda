{-# OPTIONS --safe --without-K #-}

-- Physical disjointness and Bool-valued overlap check with equivalence proofs.
--
-- Purpose: Define PhysicallyDisjoint for mixed byte orders, provide a fast
--   Bool-valued overlap check (signalsPhysicallyOverlapᵇ) with formal
--   soundness/completeness linking it to the semantic predicate.
-- Key results: physicallyOverlapᵇ-sound, physicallyOverlapᵇ-complete.
module Aletheia.DBC.Properties.Disjointness where

open import Aletheia.DBC.Types using (DBCSignal)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; physicalBitPos)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_; _≤?_; ≡ᵇ⇒≡; ≡⇒≡ᵇ; +-identityʳ; +-suc)
open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
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

-- Symmetry
signalsDisjoint-sym : ∀ {s₁ s₂} → SignalsDisjoint s₁ s₂ → SignalsDisjoint s₂ s₁
signalsDisjoint-sym (disjoint-left p) = disjoint-right p
signalsDisjoint-sym (disjoint-right p) = disjoint-left p

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
      lemma : ∀ k → k < suc n → _
      lemma k (s≤s k≤n) with k ≟ n
      ... | yes refl = pn
      ... | no k≢n = rest k (Data.Nat.Properties.≤∧≢⇒< k≤n k≢n)
        where open import Data.Nat.Properties using (≤∧≢⇒<)

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

-- ============================================================================
-- EQUIVALENCE: signalsPhysicallyOverlapᵇ ⇔ ¬ PhysicallyDisjoint
-- ============================================================================

open import Data.Bool.Properties using (∨-conicalˡ; ∨-conicalʳ)

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
