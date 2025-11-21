{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.Trace.Stream where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; reverse; last; [_])
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- COINDUCTIVE TRACE (INFINITE)
-- ============================================================================

record Trace (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Trace A

open Trace public

-- ============================================================================
-- FINITE STREAM (FOR BOUNDED TRACES)
-- ============================================================================

-- A finite stream that can terminate
-- This is the key type for memory-bounded streaming
record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Maybe (Stream A)

open Stream public

-- Convert list to finite stream (lazy construction)
listToStream : ∀ {A : Set} → List A → Maybe (Stream A)
listToStream [] = nothing
listToStream (x ∷ xs) = just (mkStream x xs)
  where
    mkStream : ∀ {A : Set} → A → List A → Stream A
    hd (mkStream x _) = x
    tl (mkStream _ []) = nothing
    tl (mkStream _ (y ∷ ys)) = just (mkStream y ys)

-- Take first n elements from stream (bounded, so terminating)
takeStream : ∀ {A : Set} → ℕ → Stream A → List A
takeStream zero _ = []
takeStream (suc n) s with tl s
... | nothing = [ hd s ]
... | just s' = hd s ∷ takeStream n s'

-- Map over a finite stream
mapStream : ∀ {A B : Set} → (A → B) → Stream A → Stream B
hd (mapStream f s) = f (hd s)
tl (mapStream f s) with tl s
... | nothing = nothing
... | just s' = just (mapStream f s')

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
