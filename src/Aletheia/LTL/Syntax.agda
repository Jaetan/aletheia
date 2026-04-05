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

  -- Bounded temporal operators (MTL) — window (microseconds) + startTime
  --
  -- Parameters: window startTime subformula(s)
  --   window    : deadline in microseconds (from first observation)
  --   startTime : suc-encoded timestamp of first frame that evaluated this operator
  --               0 = uninitialized, suc t = initialized with start time t
  --
  -- Suc encoding rationale: A plain ℕ sentinel (e.g., 0 = uninitialized) would
  -- collide with a legitimate start time of 0 (first frame at timestamp 0).
  -- The suc encoding avoids this: 0 is always "uninitialized", suc 0 means
  -- "initialized at time 0", suc 42 means "initialized at time 42".
  --
  -- timebound=0 semantics: A window of 0 microseconds means "must hold now".
  -- MetricEventually with window=0 is immediately violated if the subformula
  -- doesn't hold on the first frame. This is mathematically correct (the deadline
  -- expires before any time passes) and not rejected by the parser.
  MetricEventually : ℕ → ℕ → LTL Atom → LTL Atom
  MetricAlways : ℕ → ℕ → LTL Atom → LTL Atom
  MetricUntil : ℕ → ℕ → LTL Atom → LTL Atom → LTL Atom
  MetricRelease : ℕ → ℕ → LTL Atom → LTL Atom → LTL Atom

-- Decode start time for metric operators.
-- 0 = uninitialized (use current frame's timestamp),
-- suc t = initialized with actual start time t.
-- See encoding rationale on MetricEventually above.
decodeStart : ℕ → ℕ → ℕ
decodeStart zero    currTime = currTime
decodeStart (suc s) _        = s

