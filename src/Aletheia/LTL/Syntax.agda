{-# OPTIONS --safe --without-K #-}

-- Linear Temporal Logic (LTL) and Metric Temporal Logic (MTL) abstract syntax tree.
--
-- Purpose: Define LTL/MTL formula types parameterized by atomic predicate type.
-- Operators:
--   Propositional: Atomic, Not, And, Or
--   Unbounded temporal: Next, Always, Eventually, Until, Release
--   Bounded temporal (MTL): MetricEventually, MetricAlways, MetricUntil, MetricRelease
-- Role: Core LTL/MTL syntax used by Coinductive/Incremental semantics and JSON parser.
--
-- Design: Parametric in predicate type A allows reuse (signal predicates, generic predicates).
module Aletheia.LTL.Syntax where

open import Data.Nat using (ℕ)

data LTL (Atom : Set) : Set where
  -- Propositional operators
  Atomic : Atom → LTL Atom
  Not : LTL Atom → LTL Atom
  And Or : LTL Atom → LTL Atom → LTL Atom

  -- Unbounded temporal operators
  Next : LTL Atom → LTL Atom
  Always Eventually : LTL Atom → LTL Atom
  Until : LTL Atom → LTL Atom → LTL Atom
  Release : LTL Atom → LTL Atom → LTL Atom  -- Dual of Until: ψ holds until φ releases it

  -- Bounded temporal operators (MTL)
  MetricEventually : ℕ → LTL Atom → LTL Atom  -- Formerly EventuallyWithin
  MetricAlways : ℕ → LTL Atom → LTL Atom      -- Formerly AlwaysWithin
  MetricUntil : ℕ → LTL Atom → LTL Atom → LTL Atom      -- Formerly UntilWithin
  MetricRelease : ℕ → LTL Atom → LTL Atom → LTL Atom    -- Formerly ReleaseWithin

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
mapLTL f (Release φ ψ) = Release (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricEventually n φ) = MetricEventually n (mapLTL f φ)
mapLTL f (MetricAlways n φ) = MetricAlways n (mapLTL f φ)
mapLTL f (MetricUntil n φ ψ) = MetricUntil n (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricRelease n φ ψ) = MetricRelease n (mapLTL f φ) (mapLTL f ψ)
