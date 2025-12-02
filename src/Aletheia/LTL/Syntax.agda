{-# OPTIONS --safe --without-K #-}

-- Linear Temporal Logic (LTL) abstract syntax tree.
--
-- Purpose: Define LTL formula types parameterized by atomic predicate type.
-- Operators: Atomic, Not, And, Or, Next, Always, Eventually, Until.
-- Role: Core LTL syntax used by Coinductive/Incremental semantics and JSON parser.
--
-- Design: Parametric in predicate type A allows reuse (signal predicates, generic predicates).
module Aletheia.LTL.Syntax where

open import Data.Nat using (ℕ)

data LTL (Atom : Set) : Set where
  Atomic : Atom → LTL Atom
  Not : LTL Atom → LTL Atom
  And Or : LTL Atom → LTL Atom → LTL Atom
  Next : LTL Atom → LTL Atom
  Always Eventually : LTL Atom → LTL Atom
  Until : LTL Atom → LTL Atom → LTL Atom
  EventuallyWithin : ℕ → LTL Atom → LTL Atom
  AlwaysWithin : ℕ → LTL Atom → LTL Atom

-- Functor map for LTL: transform the atomic type
mapLTL : ∀ {A B : Set} → (A → B) → LTL A → LTL B
mapLTL f (Atomic a) = Atomic (f a)
mapLTL f (Not φ) = Not (mapLTL f φ)
mapLTL f (And φ ψ) = And (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Or φ ψ) = Or (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Next φ) = Next (mapLTL f φ)
mapLTL f (Always φ) = Always (mapLTL f φ)
mapLTL f (Eventually φ) = Eventually (mapLTL f φ)
mapLTL f (Until φ ψ) = Until (mapLTL f φ) (mapLTL f ψ)
mapLTL f (EventuallyWithin n φ) = EventuallyWithin n (mapLTL f φ)
mapLTL f (AlwaysWithin n φ) = AlwaysWithin n (mapLTL f φ)
