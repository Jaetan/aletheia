-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Linear Temporal Logic (LTL) and Metric Temporal Logic (MTL) abstract syntax tree.
--
-- Purpose: Define LTL/MTL formula types parameterized by atomic predicate type.
-- Operators:
--   Propositional: Atomic, Not, And, Or
--   Unbounded temporal: Next, WNext, Always, Eventually, Until, Release
--   Bounded temporal (MTL): MetricEventually, MetricAlways, MetricUntil, MetricRelease
-- Role: Core LTL/MTL syntax used by Coalgebra, Semantics, and JSON parser.
--
-- Design: Parametric in predicate type A allows reuse (signal predicates, generic predicates).
module Aletheia.LTL.Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Aletheia.Trace.Time using (Timestamp; μs)

data LTL (Atom : Set) : Set where
  -- Propositional operators
  Atomic : Atom → LTL Atom
  Not : LTL Atom → LTL Atom
  And Or : LTL Atom → LTL Atom → LTL Atom

  -- Unbounded temporal operators
  Next : LTL Atom → LTL Atom
  WNext : LTL Atom → LTL Atom  -- Weak Next: like Next, but holds vacuously at end of trace
  Always Eventually : LTL Atom → LTL Atom
  Until : LTL Atom → LTL Atom → LTL Atom
  Release : LTL Atom → LTL Atom → LTL Atom  -- Dual of Until: ψ holds until φ releases it

  -- Bounded temporal operators (MTL) — window (Timestamp μs) + startTime (ℕ, suc-encoded)
  --
  -- Parameters: window startTime subformula(s)
  --   window    : deadline expressed as a Timestamp μs (interpreted as a
  --               duration from first observation; same underlying ℕ but
  --               wrapped to make the dimensional invariant explicit).
  --   startTime : suc-encoded ℕ timestamp of first frame to evaluate this op.
  --               0 = uninitialized, suc t = initialized with start time t.
  --
  -- The window is `Timestamp μs`: it is microseconds
  -- per the Coalgebra step rules and JSON wire shape, not a frame count.
  -- startTime retains its
  -- suc-encoded ℕ form because the encoding is the load-bearing
  -- "uninitialized sentinel vs legitimate timestamp 0" distinction; refining
  -- it to `Maybe (Timestamp μs)` is a follow-up.
  --
  -- Suc encoding rationale (startTime): A plain ℕ sentinel (e.g., 0 = uninitialized)
  -- would collide with a legitimate start time of 0 (first frame at timestamp 0).
  -- The suc encoding avoids this: 0 is always "uninitialized", suc 0 means
  -- "initialized at time 0", suc 42 means "initialized at time 42".
  --
  -- timebound=0 semantics: A window of 0 microseconds means "must hold now".
  -- MetricEventually with window=0 is immediately violated if the subformula
  -- doesn't hold on the first frame. This is mathematically correct (the deadline
  -- expires before any time passes) and not rejected by the parser.
  --
  -- Signature note:
  --
  -- `MetricEventually : Timestamp μs → ℕ → ...`.  The first argument is
  -- the window bound (type-tagged `Timestamp μs`); the second argument is
  -- NOT a window bound — it's the suc-encoded `startTime` sentinel
  -- (`0 = uninitialised, suc t = start at time t`), per the parameter
  -- description in lines 31-50 above.
  --
  -- There is exactly ONE window bound per metric operator (the first
  -- `Timestamp μs` argument), and it is already type-tagged.
  --
  -- The actionable type-level refinement opportunity is the planned
  -- `startTime → Maybe (Timestamp μs)` follow-up noted at line 45 above,
  -- which replaces the suc-encoded sentinel with `nothing | just t`.  That
  -- refactor was investigated and is deliberately NOT taken here:
  --   * Cost: cascades to `Coalgebra.stepL` per-metric-clause, JSON
  --     parsing in `Protocol/Handlers`, `decodeStart` helper, and
  --     ~374 sites in src/.
  --   * MAlonzo runtime: `Maybe (Timestamp μs)` compiles to a `Maybe`
  --     wrapper at the per-frame hot path of metric LTL evaluation —
  --     slight allocation overhead vs the current single-`Integer`
  --     shape.  Sub-1% on first-principles analysis but unverified.
  --   * Type-safety gain: prevents accidental ℕ ⇄ Timestamp confusion
  --     at construction sites, but those construction sites are exactly
  --     `decodeStart` (kernel-internal) + 4 callers in Coalgebra — small
  --     attack surface.
  -- The net benefit of the refactor is real but small, and lifting a
  -- representation through every site is a multi-session effort.  Keep
  -- the suc-encoded ℕ form unless the Maybe-Timestamp cascade is
  -- explicitly approved.  Surface a wrong premise rather than silently
  -- reframing the proof around it.
  MetricEventually : Timestamp μs → ℕ → LTL Atom → LTL Atom
  MetricAlways : Timestamp μs → ℕ → LTL Atom → LTL Atom
  MetricUntil : Timestamp μs → ℕ → LTL Atom → LTL Atom → LTL Atom
  MetricRelease : Timestamp μs → ℕ → LTL Atom → LTL Atom → LTL Atom

-- Functor map: transform atomic predicates while preserving formula structure.
mapLTL : ∀ {A B : Set} → (A → B) → LTL A → LTL B
mapLTL f (Atomic a)              = Atomic (f a)
mapLTL f (Not φ)                 = Not (mapLTL f φ)
mapLTL f (And φ ψ)              = And (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Or φ ψ)               = Or (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Next φ)                = Next (mapLTL f φ)
mapLTL f (WNext φ)               = WNext (mapLTL f φ)
mapLTL f (Always φ)              = Always (mapLTL f φ)
mapLTL f (Eventually φ)          = Eventually (mapLTL f φ)
mapLTL f (Until φ ψ)            = Until (mapLTL f φ) (mapLTL f ψ)
mapLTL f (Release φ ψ)          = Release (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricEventually w s φ)     = MetricEventually w s (mapLTL f φ)
mapLTL f (MetricAlways w s φ)         = MetricAlways w s (mapLTL f φ)
mapLTL f (MetricUntil w s φ ψ)      = MetricUntil w s (mapLTL f φ) (mapLTL f ψ)
mapLTL f (MetricRelease w s φ ψ)    = MetricRelease w s (mapLTL f φ) (mapLTL f ψ)

-- Decode start time for metric operators.
-- 0 = uninitialized (use current frame's timestamp),
-- suc t = initialized with actual start time t.
-- See encoding rationale on MetricEventually above.
decodeStart : ℕ → ℕ → ℕ
decodeStart zero    currTime = currTime
decodeStart (suc s) _        = s

-- Count atomic predicates in a formula.  Used to
-- bound adversarial-input property formulas at the parser surface (the
-- canonical limit is `max-atom-count-per-property` in `Aletheia.Limits`,
-- currently 1024).  Mirrors `Protocol.StreamState.Internals.collectAtoms`
-- in structure (one ctor per AST shape) but returns a count directly so
-- callers can bound-check without allocating the atom list.
atomCount : ∀ {A : Set} → LTL A → ℕ
atomCount (Atomic _)                = 1
atomCount (Not φ)                   = atomCount φ
atomCount (And φ ψ)                 = atomCount φ + atomCount ψ
atomCount (Or φ ψ)                  = atomCount φ + atomCount ψ
atomCount (Next φ)                  = atomCount φ
atomCount (WNext φ)                 = atomCount φ
atomCount (Always φ)                = atomCount φ
atomCount (Eventually φ)            = atomCount φ
atomCount (Until φ ψ)               = atomCount φ + atomCount ψ
atomCount (Release φ ψ)             = atomCount φ + atomCount ψ
atomCount (MetricEventually _ _ φ)  = atomCount φ
atomCount (MetricAlways _ _ φ)      = atomCount φ
atomCount (MetricUntil _ _ φ ψ)     = atomCount φ + atomCount ψ
atomCount (MetricRelease _ _ φ ψ)   = atomCount φ + atomCount ψ

