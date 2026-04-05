{-# OPTIONS --safe --without-K #-}

-- Rosu-style simplification for LTL formula progression.
--
-- Purpose: Compact formula trees produced by combineAnd/combineOr to prevent
-- O(n²) blowup from Always/Eventually progression on Unknown/Pending signals.
--
-- Two-phase approach:
--   Phase 1 (simplify): recurse into right subterms of And/Or
--   Phase 2 (absorb): apply absorption rules at the top level
--
-- Moved from Coalgebra.agda to separate concerns (types+evaluator vs. optimization).
-- Soundness proofs: LTL/SimplifySound.agda
module Aletheia.LTL.Simplify where

open import Aletheia.LTL.Coalgebra using
  ( LTLProc; finalizeL
  ; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release
  ; MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails)
open import Data.Nat using (_≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_)

-- ============================================================================
-- FINALIZATION PREDICATE
-- ============================================================================

-- Boolean check: does finalizeL give Holds?
-- Used by absorb to guard Always/Eventually rules against finalization mismatch.
finalizesHolds : LTLProc → Bool
finalizesHolds proc with finalizeL proc
... | Holds   = true
... | Fails _ = false

-- ============================================================================
-- STRUCTURAL EQUALITY
-- ============================================================================

-- Boolean structural equality on LTLProc.
-- Used by simplify to detect Rosu tree growth patterns.
_≡ᵇ-proc_ : LTLProc → LTLProc → Bool
Atomic n              ≡ᵇ-proc Atomic m              = n ≡ᵇ m
Not φ                 ≡ᵇ-proc Not ψ                 = φ ≡ᵇ-proc ψ
And φ₁ ψ₁             ≡ᵇ-proc And φ₂ ψ₂             = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Or φ₁ ψ₁              ≡ᵇ-proc Or φ₂ ψ₂              = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Next φ                ≡ᵇ-proc Next ψ                = φ ≡ᵇ-proc ψ
Always φ              ≡ᵇ-proc Always ψ              = φ ≡ᵇ-proc ψ
Eventually φ          ≡ᵇ-proc Eventually ψ          = φ ≡ᵇ-proc ψ
Until φ₁ ψ₁           ≡ᵇ-proc Until φ₂ ψ₂           = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Release φ₁ ψ₁         ≡ᵇ-proc Release φ₂ ψ₂         = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
MetricEventuallyProc w₁ s₁ φ₁ ≡ᵇ-proc MetricEventuallyProc w₂ s₂ φ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂)
MetricAlwaysProc w₁ s₁ φ₁ ≡ᵇ-proc MetricAlwaysProc w₂ s₂ φ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂)
MetricUntilProc w₁ s₁ φ₁ ψ₁ ≡ᵇ-proc MetricUntilProc w₂ s₂ φ₂ ψ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
MetricReleaseProc w₁ s₁ φ₁ ψ₁ ≡ᵇ-proc MetricReleaseProc w₂ s₂ φ₂ ψ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
_ ≡ᵇ-proc _ = false

-- ============================================================================
-- ABSORPTION AND SIMPLIFICATION
-- ============================================================================

-- Phase 2: apply absorption rules (non-recursive)
absorb : LTLProc → LTLProc
-- And absorption: φ ∧ G(φ) → G(φ) (guarded by finalizesHolds)
absorb (And φ (Always ψ)) with φ ≡ᵇ-proc ψ | finalizesHolds φ
... | true  | true  = Always ψ
... | _     | _     = And φ (Always ψ)
-- Or absorption: φ ∨ F(φ) → F(φ) (guarded by ¬ finalizesHolds)
absorb (Or φ (Eventually ψ)) with φ ≡ᵇ-proc ψ | finalizesHolds φ
... | true  | false = Eventually ψ
... | _     | _     = Or φ (Eventually ψ)
-- Structural idempotency: φ ∧ (φ ∧ ψ) → φ ∧ ψ, φ ∨ (φ ∨ ψ) → φ ∨ ψ
absorb (And a (And b c)) with a ≡ᵇ-proc b
... | true  = And a c
... | false = And a (And b c)
absorb (Or a (Or b c)) with a ≡ᵇ-proc b
... | true  = Or a c
... | false = Or a (Or b c)
absorb x = x

-- Phase 1: recurse right to handle nested patterns, then absorb
simplify : LTLProc → LTLProc
simplify (And a b) = absorb (And a (simplify b))
simplify (Or a b)  = absorb (Or a (simplify b))
simplify x = x
