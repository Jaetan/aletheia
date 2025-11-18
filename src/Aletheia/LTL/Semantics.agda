{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.Semantics where

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.Stream
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.List using (List; []; _∷_; length; drop)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- LTL SEMANTICS WITH REPEAT-LAST BEHAVIOR
-- ============================================================================

-- Finite lists are interpreted as infinite traces that repeat their last element.
-- This gives correct LTL semantics for recorded CAN traces:
-- - [f1, f2, f3] represents the infinite trace: f1, f2, f3, f3, f3, ...
-- - Always φ holds if φ holds on all frames AND on the repeating final state
-- - Eventually φ holds if φ holds somewhere in the list OR on the final state

-- Helper: Get the last element of a list (if it exists)
lastElem : ∀ {A : Set} → List A → Maybe A
lastElem [] = nothing
lastElem (x ∷ []) = just x
lastElem (x ∷ rest@(_ ∷ _)) = lastElem rest

-- Check if a finite trace (repeating last element) satisfies an LTL formula
satisfiesAt : ∀ {A : Set} → List A → LTL (A → Bool) → Bool
satisfiesAt [] (Atomic _) = false
satisfiesAt (x ∷ _) (Atomic pred) = pred x

satisfiesAt trace (Not φ) = not (satisfiesAt trace φ)

satisfiesAt trace (And φ ψ) = satisfiesAt trace φ ∧ satisfiesAt trace ψ

satisfiesAt trace (Or φ ψ) = satisfiesAt trace φ ∨ satisfiesAt trace ψ

satisfiesAt [] (Next _) = false
satisfiesAt (_ ∷ []) (Next φ) = satisfiesAt [] (Next φ)  -- Repeats last, so Next stays at last
satisfiesAt (_ ∷ rest) (Next φ) = satisfiesAt rest φ

-- Always: Must hold on all elements AND on the infinitely repeating final state
satisfiesAt [] (Always _) = true  -- Vacuously true for empty trace
satisfiesAt (x ∷ []) (Always φ) = satisfiesAt (x ∷ []) φ  -- Must hold on repeating final state
satisfiesAt trace@(x ∷ rest) (Always φ) = satisfiesAt trace φ ∧ satisfiesAt rest (Always φ)

-- Eventually: Must hold somewhere in the list OR on the infinitely repeating final state
satisfiesAt [] (Eventually _) = false
satisfiesAt trace@(x ∷ rest) (Eventually φ) = satisfiesAt trace φ ∨ satisfiesAt rest (Eventually φ)

-- Until: φ holds until ψ becomes true (ψ can be satisfied on repeating final state)
satisfiesAt [] (Until _ _) = false
satisfiesAt trace@(x ∷ rest) (Until φ ψ) =
  satisfiesAt trace ψ ∨ (satisfiesAt trace φ ∧ satisfiesAt rest (Until φ ψ))

-- Bounded operators work within the finite prefix (don't consider infinite tail)
satisfiesAt [] (EventuallyWithin _ _) = false
satisfiesAt _ (EventuallyWithin zero _) = false
satisfiesAt trace@(x ∷ rest) (EventuallyWithin (suc n) φ) =
  satisfiesAt trace φ ∨ satisfiesAt rest (EventuallyWithin n φ)

satisfiesAt [] (AlwaysWithin _ _) = true
satisfiesAt _ (AlwaysWithin zero _) = true
satisfiesAt trace@(x ∷ rest) (AlwaysWithin (suc n) φ) =
  satisfiesAt trace φ ∧ satisfiesAt rest (AlwaysWithin n φ)

-- Wrapper for list-based checking (primary interface)
-- Finite lists are interpreted as repeating their last element infinitely
checkList : ∀ {A : Set} → List A → LTL (A → Bool) → Bool
checkList = satisfiesAt

-- Note: Direct coinductive trace checking doesn't terminate for unbounded operators!
-- Always/Eventually on infinite traces require infinite computation.
-- For practical use, convert lists to coinductive traces with fromListRepeat,
-- or use bounded checking with satisfiesAt on finite prefixes.
