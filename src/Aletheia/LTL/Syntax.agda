{-# OPTIONS --safe --without-K #-}

-- Linear Temporal Logic (LTL) and Metric Temporal Logic (MTL) abstract syntax tree.
--
-- Purpose: Define LTL/MTL formula types parameterized by atomic predicate type.
-- Operators:
--   Propositional: Atomic, Not, And, Or
--   Unbounded temporal: Next, Always, Eventually, Until, Release
--   Bounded temporal (MTL): MetricEventually, MetricAlways, MetricUntil, MetricRelease
-- Role: Core LTL/MTL syntax used by Coalgebra, Semantics, and JSON parser.
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

