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

open import Aletheia.LTL.Coalgebra using (LTLProc; finalizeL)
open import Aletheia.LTL.Syntax using
  (Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
   MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure)
open import Data.Nat using (_≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_)

-- ============================================================================
-- FINALIZATION PREDICATE
-- ============================================================================

-- Boolean check: does finalizeL give Holds definitely?
-- Used by And absorption to guard Always rules against finalization mismatch.
-- Unsure (Kleene Unknown) is treated as "not definitely Holds" so the
-- absorption guard stays conservative — keeps the absorption rule
-- denotationally sound on empty traces under three-valued finalization.
finalizesHolds : LTLProc → Bool
finalizesHolds proc with finalizeL proc
... | Holds    = true
... | Fails _  = false
... | Unsure _ = false

-- Boolean check: does finalizeL give Fails definitely?
-- Used by Or absorption to guard Eventually rules. Under three-valued
-- finalization, `¬ finalizesHolds` is too weak: it treats Unsure as
-- permissive, but `φ ∨ F(φ)` with `finalizeL φ = Unsure r` finalizes to
-- `Unsure r` (⊤-absorb identity on empty trace), not `Fails`, so replacing
-- it with `F(φ)` (which finalizes to Fails) would break adequacy. The
-- tighter predicate fires only when both sides definitely finalize to
-- `Fails`, making absorption denotationally sound.
finalizesFails : LTLProc → Bool
finalizesFails proc with finalizeL proc
... | Holds    = false
... | Fails _  = true
... | Unsure _ = false

-- ============================================================================
-- STRUCTURAL EQUALITY
-- ============================================================================

-- Boolean structural equality on LTLProc.
-- Used by simplify to detect Rosu tree growth patterns.
-- NOTE: The catch-all `_ ≡ᵇ-proc _ = false` at the end covers cross-constructor
-- pairs. If new constructors are added to LTLProc, add same-constructor clauses
-- ABOVE the catch-all — otherwise same-constructor pairs silently return false.
_≡ᵇ-proc_ : LTLProc → LTLProc → Bool
Atomic n              ≡ᵇ-proc Atomic m              = n ≡ᵇ m
Not φ                 ≡ᵇ-proc Not ψ                 = φ ≡ᵇ-proc ψ
And φ₁ ψ₁             ≡ᵇ-proc And φ₂ ψ₂             = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Or φ₁ ψ₁              ≡ᵇ-proc Or φ₂ ψ₂              = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Next φ                ≡ᵇ-proc Next ψ                = φ ≡ᵇ-proc ψ
WNext φ               ≡ᵇ-proc WNext ψ               = φ ≡ᵇ-proc ψ
Always φ              ≡ᵇ-proc Always ψ              = φ ≡ᵇ-proc ψ
Eventually φ          ≡ᵇ-proc Eventually ψ          = φ ≡ᵇ-proc ψ
Until φ₁ ψ₁           ≡ᵇ-proc Until φ₂ ψ₂           = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Release φ₁ ψ₁         ≡ᵇ-proc Release φ₂ ψ₂         = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
MetricEventually w₁ s₁ φ₁ ≡ᵇ-proc MetricEventually w₂ s₂ φ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂)
MetricAlways w₁ s₁ φ₁ ≡ᵇ-proc MetricAlways w₂ s₂ φ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂)
MetricUntil w₁ s₁ φ₁ ψ₁ ≡ᵇ-proc MetricUntil w₂ s₂ φ₂ ψ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
MetricRelease w₁ s₁ φ₁ ψ₁ ≡ᵇ-proc MetricRelease w₂ s₂ φ₂ ψ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
{-# CATCHALL #-}
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
-- Or absorption: φ ∨ F(φ) → F(φ) (guarded by finalizesFails)
absorb (Or φ (Eventually ψ)) with φ ≡ᵇ-proc ψ | finalizesFails φ
... | true  | true  = Eventually ψ
... | _     | _     = Or φ (Eventually ψ)
-- Structural idempotency: φ ∧ (φ ∧ ψ) → φ ∧ ψ, φ ∨ (φ ∨ ψ) → φ ∨ ψ
absorb (And a (And b c)) with a ≡ᵇ-proc b
... | true  = And a c
... | false = And a (And b c)
absorb (Or a (Or b c)) with a ≡ᵇ-proc b
... | true  = Or a c
... | false = Or a (Or b c)
-- CATCHALL is the identity default: all LTLProc constructors not matched above
-- (Atomic, Not, Next, WNext, Until, Release, Metric*, and And/Or with
-- non-matching subterms) absorb to themselves. Adding a new LTLProc
-- constructor is safe — it will flow through the identity — but any new
-- absorption rule MUST be added above this line.
{-# CATCHALL #-}
absorb x = x

-- Phase 1: recurse right to handle nested patterns, then absorb
simplify : LTLProc → LTLProc
simplify (And a b) = absorb (And a (simplify b))
simplify (Or a b)  = absorb (Or a (simplify b))
-- CATCHALL is the identity default: all non-And/Or LTLProc constructors
-- simplify to themselves. Adding a new LTLProc constructor is safe — it
-- flows through the identity — but any new recursive simplification rule
-- MUST be added above this line.
{-# CATCHALL #-}
simplify x = x
