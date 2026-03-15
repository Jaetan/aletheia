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

open import Data.Nat using (ℕ; zero; suc)

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

  -- Bounded temporal operators (MTL) — window + startTime (suc-encoded)
  -- Encoding: 0 = uninitialized, suc t = initialized with start time t.
  MetricEventually : ℕ → ℕ → LTL Atom → LTL Atom
  MetricAlways : ℕ → ℕ → LTL Atom → LTL Atom
  MetricUntil : ℕ → ℕ → LTL Atom → LTL Atom → LTL Atom
  MetricRelease : ℕ → ℕ → LTL Atom → LTL Atom → LTL Atom

-- Decode start time for metric operators.
-- 0 = uninitialized (use current frame's timestamp),
-- suc t = initialized with actual start time t.
-- Avoids sentinel collision when the first frame has timestamp 0.
decodeStart : ℕ → ℕ → ℕ
decodeStart zero    currTime = currTime
decodeStart (suc s) _        = s

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
mapLTL f (MetricEventually w s φ) = MetricEventually w s (mapLTL f φ)
mapLTL f (MetricAlways w s φ) = MetricAlways w s (mapLTL f φ)
mapLTL f (MetricUntil w s φ ψ) = MetricUntil w s (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricRelease w s φ ψ) = MetricRelease w s (mapLTL f φ) (mapLTL f ψ)
