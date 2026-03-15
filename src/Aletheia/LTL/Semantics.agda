{-# OPTIONS --safe --without-K #-}

-- Denotational LTLf semantics (De Giacomo & Vardi 2013).
--
-- Purpose: Define the mathematical meaning of LTL formulas on finite traces.
-- This is the reference specification against which stepL (formula progression)
-- is proven correct.
--
-- Key design decisions:
--   - Suffix-based: ⟦ φ ⟧ σ evaluates φ at position 0 of trace suffix σ
--   - Returns SignalVal (four-valued Kleene logic)
--   - Strong next: X φ is False at end of trace (standard LTLf)
--   - Vacuous truth: G φ on empty suffix = True (standard LTLf)
--   - Metric operators: window check uses elapsed time (timestamp difference)
--     Each carries startTime s (suc-encoded: 0 = uninitialized, suc t = start time t)
--
-- Termination: Lexicographic on (formula structure, list length).
--   Unbounded temporal: formula stays same, list strictly decreases (tail)
--   Metric temporal: met-*-go helpers recurse on list; calls to ⟦ φ ⟧
--     have strictly smaller formula (φ < MetricAlways w s φ).
--
-- Design: Metric go helpers are top-level (mutual with ⟦_⟧) so the adequacy
-- proof can reference them. The key property enabling this:
--   met-ev-go w φ start σ ≡ ⟦ MetricEventually w (suc start) φ ⟧ σ
-- (and similarly for the other metric operators).
module Aletheia.LTL.Semantics where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_)

open import Aletheia.LTL.Syntax
open import Aletheia.LTL.SignalPredicate using (SignalVal; notTV; _∧TV_; _∨TV_)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)

open SignalVal

-- ============================================================================
-- DENOTATIONAL LTLf SEMANTICS
-- ============================================================================

-- Evaluate an LTL formula on a finite trace suffix.
--
-- ⟦ φ ⟧ σ  gives the truth value of φ at position 0 of σ.
--
-- Standard LTLf semantics (De Giacomo & Vardi 2013):
--   ⟦ p ⟧ (x ∷ _)         = p x
--   ⟦ ¬φ ⟧ σ               = ¬ ⟦ φ ⟧ σ
--   ⟦ φ ∧ ψ ⟧ σ            = ⟦ φ ⟧ σ ∧ ⟦ ψ ⟧ σ
--   ⟦ Xφ ⟧ (x ∷ σ)        = ⟦ φ ⟧ σ       (strong next: False at last position)
--   ⟦ Gφ ⟧ σ               = ∀i∈[0,|σ|). ⟦ φ ⟧ σᵢ
--   ⟦ Fφ ⟧ σ               = ∃i∈[0,|σ|). ⟦ φ ⟧ σᵢ
--   ⟦ φ U ψ ⟧ σ            = ∃i. (⟦ ψ ⟧ σᵢ ∧ ∀j<i. ⟦ φ ⟧ σⱼ)
--   ⟦ φ R ψ ⟧ σ            = ∀i. (⟦ ψ ⟧ σᵢ ∨ ∃j<i. ⟦ φ ⟧ σⱼ)
--
-- Extended to four-valued Kleene logic (SignalVal):
--   True, False, Unknown, Pending — using ∧TV, ∨TV, notTV.

-- Forward declarations for mutual recursion between ⟦_⟧ and metric go helpers.
⟦_⟧ : LTL (TimedFrame → SignalVal) → List TimedFrame → SignalVal
met-ev-go : ℕ → LTL (TimedFrame → SignalVal) → ℕ → List TimedFrame → SignalVal
met-al-go : ℕ → LTL (TimedFrame → SignalVal) → ℕ → List TimedFrame → SignalVal
met-un-go : ℕ → LTL (TimedFrame → SignalVal) → LTL (TimedFrame → SignalVal) → ℕ → List TimedFrame → SignalVal
met-re-go : ℕ → LTL (TimedFrame → SignalVal) → LTL (TimedFrame → SignalVal) → ℕ → List TimedFrame → SignalVal

-- Propositional operators
-- Atomic on empty suffix: False (predicate has no frame to evaluate on).
⟦ Atomic p ⟧ []          = False
⟦ Atomic p ⟧ (x ∷ _)    = p x

⟦ Not φ ⟧ σ              = notTV (⟦ φ ⟧ σ)
⟦ And φ ψ ⟧ σ            = ⟦ φ ⟧ σ ∧TV ⟦ ψ ⟧ σ
⟦ Or φ ψ ⟧ σ             = ⟦ φ ⟧ σ ∨TV ⟦ ψ ⟧ σ

-- Strong next: requires at least one more frame after current
⟦ Next φ ⟧ []            = False
⟦ Next φ ⟧ (_ ∷ rest)    = ⟦ φ ⟧ rest

-- Always (G): vacuously true on empty suffix
⟦ Always φ ⟧ []          = True
⟦ Always φ ⟧ (x ∷ rest)  = ⟦ φ ⟧ (x ∷ rest) ∧TV ⟦ Always φ ⟧ rest

-- Eventually (F): false on empty suffix
⟦ Eventually φ ⟧ []          = False
⟦ Eventually φ ⟧ (x ∷ rest)  = ⟦ φ ⟧ (x ∷ rest) ∨TV ⟦ Eventually φ ⟧ rest

-- Until (φ U ψ): ψ must eventually hold, with φ holding until then
⟦ Until φ ψ ⟧ []          = False
⟦ Until φ ψ ⟧ (x ∷ rest)  = ⟦ ψ ⟧ (x ∷ rest) ∨TV (⟦ φ ⟧ (x ∷ rest) ∧TV ⟦ Until φ ψ ⟧ rest)

-- Release (φ R ψ): dual of Until — ψ must hold everywhere, or until φ releases it
⟦ Release φ ψ ⟧ []          = True
⟦ Release φ ψ ⟧ (x ∷ rest)  = ⟦ ψ ⟧ (x ∷ rest) ∧TV (⟦ φ ⟧ (x ∷ rest) ∨TV ⟦ Release φ ψ ⟧ rest)

-- ============================================================================
-- METRIC TEMPORAL OPERATORS
-- ============================================================================
-- Each carries window w and startTime s (suc-encoded).
-- Encoding: 0 = uninitialized (use timestamp of first frame),
--           suc t = initialized with actual start time t.
-- This avoids sentinel collision when the first frame has timestamp 0.
-- User-facing formulas always have s=0; denot preserves the monitor's startTime.
--
-- The go helpers are top-level (not where-blocks) so the adequacy proof
-- can reference and reason about them. Key property:
--   met-ev-go w φ start σ ≡ ⟦ MetricEventually w (suc start) φ ⟧ σ  (by refl)

-- Metric Eventually (F[0,w] φ): φ must hold at some point within window
⟦ MetricEventually w s φ ⟧ [] = False
⟦ MetricEventually w s φ ⟧ σ@(y ∷ _) = met-ev-go w φ (decodeStart s (timestamp y)) σ

-- Metric Always (G[0,w] φ): φ must hold at every point within window
⟦ MetricAlways w s φ ⟧ [] = True
⟦ MetricAlways w s φ ⟧ σ@(y ∷ _) = met-al-go w φ (decodeStart s (timestamp y)) σ

-- Metric Until (φ U[0,w] ψ): ψ must hold within window, with φ holding until then
⟦ MetricUntil w s φ ψ ⟧ [] = False
⟦ MetricUntil w s φ ψ ⟧ σ@(y ∷ _) = met-un-go w φ ψ (decodeStart s (timestamp y)) σ

-- Metric Release (φ R[0,w] ψ): dual of Metric Until
⟦ MetricRelease w s φ ψ ⟧ [] = True
⟦ MetricRelease w s φ ψ ⟧ σ@(y ∷ _) = met-re-go w φ ψ (decodeStart s (timestamp y)) σ

-- ============================================================================
-- METRIC GO HELPERS (top-level for adequacy proof access)
-- ============================================================================
-- Key property: met-ev-go w φ start σ ≡ ⟦ MetricEventually w (suc start) φ ⟧ σ  (by refl)
-- (and similarly for the other metric operators).

met-ev-go w φ start [] = False
met-ev-go w φ start (y ∷ rest) with (timestamp y ∸ start) ≤ᵇ w
... | false = False    -- past the window
... | true  = ⟦ φ ⟧ (y ∷ rest) ∨TV met-ev-go w φ start rest

met-al-go w φ start [] = True
met-al-go w φ start (y ∷ rest) with (timestamp y ∸ start) ≤ᵇ w
... | false = True     -- past the window, vacuously holds
... | true  = ⟦ φ ⟧ (y ∷ rest) ∧TV met-al-go w φ start rest

met-un-go w φ ψ start [] = False
met-un-go w φ ψ start (y ∷ rest) with (timestamp y ∸ start) ≤ᵇ w
... | false = False    -- past the window, ψ never held in time
... | true  = ⟦ ψ ⟧ (y ∷ rest) ∨TV (⟦ φ ⟧ (y ∷ rest) ∧TV met-un-go w φ ψ start rest)

met-re-go w φ ψ start [] = True
met-re-go w φ ψ start (y ∷ rest) with (timestamp y ∸ start) ≤ᵇ w
... | false = True     -- past the window, vacuously holds
... | true  = ⟦ ψ ⟧ (y ∷ rest) ∧TV (⟦ φ ⟧ (y ∷ rest) ∨TV met-re-go w φ ψ start rest)
