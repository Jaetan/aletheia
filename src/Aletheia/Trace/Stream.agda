{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.Trace.Stream where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; reverse; last; [_])
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- COINDUCTIVE TRACE
-- ============================================================================

record Trace (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Trace A

open Trace public

-- ============================================================================
-- TRACE OPERATIONS
-- ============================================================================

take : ∀ {A : Set} → ℕ → Trace A → List A
take zero t = []
take (suc n) t = head t ∷ take n (tail t)

drop : ∀ {A : Set} → ℕ → Trace A → Trace A
drop zero t = t
drop (suc n) t = drop n (tail t)

-- Repeat a single value infinitely (productive corecursion)
repeat : ∀ {A : Set} → A → Trace A
head (repeat x) = x
tail (repeat x) = repeat x

-- Helper for fromListRepeat (productive corecursion)
fromListRepeat-go : ∀ {A : Set} → A → List A → Trace A
head (fromListRepeat-go current []) = current
tail (fromListRepeat-go current []) = repeat current
head (fromListRepeat-go current (next ∷ rest)) = current
tail (fromListRepeat-go current (next ∷ rest)) = fromListRepeat-go next rest

-- Convert finite list to infinite trace by repeating the last element
-- Returns Nothing if the list is empty (no last element to repeat)
fromListRepeat : ∀ {A : Set} → List A → Maybe (Trace A)
fromListRepeat [] = nothing
fromListRepeat (x ∷ xs) = just (fromListRepeat-go x xs)
