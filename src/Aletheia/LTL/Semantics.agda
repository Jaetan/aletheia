{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.Semantics where

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.Stream
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.List using (List; []; _∷_; length; drop)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- BOUNDED LTL SEMANTICS
-- ============================================================================

-- For Phase 2A, we implement bounded semantics over finite trace prefixes.
-- This is practical for real-world CAN trace analysis where we check
-- properties over recorded traces of finite length.

-- Check if a finite trace (as a list) satisfies an LTL formula at position 0
satisfiesAt : ∀ {A : Set} → List A → LTL (A → Bool) → Bool
satisfiesAt [] (Atomic _) = false
satisfiesAt (x ∷ _) (Atomic pred) = pred x

satisfiesAt trace (Not φ) = not (satisfiesAt trace φ)

satisfiesAt trace (And φ ψ) = satisfiesAt trace φ ∧ satisfiesAt trace ψ

satisfiesAt trace (Or φ ψ) = satisfiesAt trace φ ∨ satisfiesAt trace ψ

satisfiesAt [] (Next _) = false
satisfiesAt (_ ∷ rest) (Next φ) = satisfiesAt rest φ

satisfiesAt [] (Always _) = true
satisfiesAt trace@(x ∷ rest) (Always φ) = satisfiesAt trace φ ∧ satisfiesAt rest (Always φ)

satisfiesAt [] (Eventually _) = false
satisfiesAt trace@(x ∷ rest) (Eventually φ) = satisfiesAt trace φ ∨ satisfiesAt rest (Eventually φ)

satisfiesAt [] (Until _ _) = false
satisfiesAt trace@(x ∷ rest) (Until φ ψ) =
  satisfiesAt trace ψ ∨ (satisfiesAt trace φ ∧ satisfiesAt rest (Until φ ψ))

satisfiesAt [] (EventuallyWithin _ _) = false
satisfiesAt _ (EventuallyWithin zero _) = false
satisfiesAt trace@(x ∷ rest) (EventuallyWithin (suc n) φ) =
  satisfiesAt trace φ ∨ satisfiesAt rest (EventuallyWithin n φ)

satisfiesAt [] (AlwaysWithin _ _) = true
satisfiesAt _ (AlwaysWithin zero _) = true
satisfiesAt trace@(x ∷ rest) (AlwaysWithin (suc n) φ) =
  satisfiesAt trace φ ∧ satisfiesAt rest (AlwaysWithin n φ)

-- Coinductive trace wrapper (for compatibility with existing Trace type)
-- Takes first 1000 elements from infinite trace for bounded checking
_⊨_ : ∀ {A : Set} → Trace A → LTL (A → Bool) → Bool
trace ⊨ formula = satisfiesAt (take 1000 trace) formula
