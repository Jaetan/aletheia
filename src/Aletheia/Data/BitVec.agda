{-# OPTIONS --safe --without-K #-}

-- Bit vectors with structural operations (not arithmetic).
--
-- Purpose: Provide a bitvector abstraction with bit-level operations.
-- Operations: testBit, setBit, with trivial structural proofs.
-- Role: Foundation for CAN frame bit manipulation, avoiding arithmetic traps.
--
-- Philosophy: Bit independence is a structural property, not an arithmetic theorem.
-- Proofs at this level are trivial because we use the right representation.
module Aletheia.Data.BitVec where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; lookup; updateAt)
open import Data.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Function using (const; _∘_)

-- ============================================================================
-- BITVECTOR TYPE
-- ============================================================================

-- A bitvector is a vector of booleans
-- This is the correct abstraction for reasoning about independent bits
BitVec : ℕ → Set
BitVec n = Vec Bool n

-- ============================================================================
-- BASIC OPERATIONS
-- ============================================================================

-- Test if bit at position k is set
testBit : ∀ {n} → BitVec n → Fin n → Bool
testBit bits k = lookup bits k

-- Set bit at position k to value v
setBit : ∀ {n} → BitVec n → Fin n → Bool → BitVec n
setBit bits k v = updateAt bits k (const v)

-- ============================================================================
-- STRUCTURAL PROPERTIES (TRIVIAL PROOFS)
-- ============================================================================

-- These proofs are one-liners because we're working at the right abstraction level.
-- No arithmetic, no carries, no power-of-2 lemmas needed.

-- Testing a bit after setting it returns the set value
testBit-setBit-same : ∀ {n} (bits : BitVec n) (k : Fin n) (v : Bool)
  → testBit (setBit bits k v) k ≡ v
testBit-setBit-same {zero} bits () v
testBit-setBit-same {suc n} (b ∷ bs) Fin.zero v = refl
testBit-setBit-same {suc n} (b ∷ bs) (Fin.suc k) v =
  testBit-setBit-same bs k v

-- Testing a different bit after setting is unchanged
testBit-setBit-diff : ∀ {n} (bits : BitVec n) (k₁ k₂ : Fin n) (v : Bool)
  → k₁ ≢ k₂
  → testBit (setBit bits k₁ v) k₂ ≡ testBit bits k₂
testBit-setBit-diff {zero} bits () k₂ v k₁≢k₂
testBit-setBit-diff {suc n} (b ∷ bs) Fin.zero Fin.zero v k₁≢k₂ = ⊥-elim (k₁≢k₂ refl)
  where open import Data.Empty using (⊥-elim)
testBit-setBit-diff {suc n} (b ∷ bs) Fin.zero (Fin.suc k₂) v k₁≢k₂ = refl
testBit-setBit-diff {suc n} (b ∷ bs) (Fin.suc k₁) Fin.zero v k₁≢k₂ = refl
testBit-setBit-diff {suc n} (b ∷ bs) (Fin.suc k₁) (Fin.suc k₂) v k₁≢k₂ =
  testBit-setBit-diff bs k₁ k₂ v (k₁≢k₂ ∘ cong Fin.suc)

-- Setting a bit twice: second write wins
setBit-setBit-same : ∀ {n} (bits : BitVec n) (k : Fin n) (v₁ v₂ : Bool)
  → setBit (setBit bits k v₁) k v₂ ≡ setBit bits k v₂
setBit-setBit-same {zero} bits () v₁ v₂
setBit-setBit-same {suc n} (b ∷ bs) Fin.zero v₁ v₂ = refl
setBit-setBit-same {suc n} (b ∷ bs) (Fin.suc k) v₁ v₂ =
  cong (b ∷_) (setBit-setBit-same bs k v₁ v₂)

-- Setting different bits commutes
setBit-setBit-comm : ∀ {n} (bits : BitVec n) (k₁ k₂ : Fin n) (v₁ v₂ : Bool)
  → k₁ ≢ k₂
  → setBit (setBit bits k₁ v₁) k₂ v₂ ≡ setBit (setBit bits k₂ v₂) k₁ v₁
setBit-setBit-comm {zero} bits () k₂ v₁ v₂ k₁≢k₂
setBit-setBit-comm {suc n} (b ∷ bs) Fin.zero Fin.zero v₁ v₂ k₁≢k₂ = ⊥-elim (k₁≢k₂ refl)
  where open import Data.Empty using (⊥-elim)
setBit-setBit-comm {suc n} (b ∷ bs) Fin.zero (Fin.suc k₂) v₁ v₂ k₁≢k₂ = refl
setBit-setBit-comm {suc n} (b ∷ bs) (Fin.suc k₁) Fin.zero v₁ v₂ k₁≢k₂ = refl
setBit-setBit-comm {suc n} (b ∷ bs) (Fin.suc k₁) (Fin.suc k₂) v₁ v₂ k₁≢k₂ =
  cong (b ∷_) (setBit-setBit-comm bs k₁ k₂ v₁ v₂ (k₁≢k₂ ∘ cong Fin.suc))

