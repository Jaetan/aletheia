{-# OPTIONS --safe --without-K #-}

module Aletheia.Trace.Stream where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

record Trace (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Trace A

open Trace public

take : ∀ {A : Set} → ℕ → Trace A → List A
take zero t = []
take (suc n) t = head t ∷ take n (tail t)

drop : ∀ {A : Set} → ℕ → Trace A → Trace A
drop zero t = t
drop (suc n) t = drop n (tail t)
