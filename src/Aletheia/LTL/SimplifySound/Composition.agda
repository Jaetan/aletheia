{-# OPTIONS --safe --without-K #-}

-- Main soundness theorem for Rosu simplification — sections 6-8.
--
-- Purpose: Prove that `absorb`/`simplify` from LTL/Simplify.agda preserve
--   `runL`, then derive the empty-trace corollary used by Adequacy/Pipeline.
-- Public API:
--   * absorb-runL          — absorb preserves runL (all rules, all traces)
--   * simplify-runL        — simplify preserves runL (structural induction)
--   * simplify-finalize-sv — empty-trace corollary used by Pipeline
--
-- Role: Top-layer of SimplifySound. Consumes the public API of
--   SimplifySound.Decomposition (≡ᵇ-proc-correct, nested idempotency,
--   Always/Eventually absorption, runL congruence) and assembles the
--   Adequacy.Pipeline-facing soundness theorem.
module Aletheia.LTL.SimplifySound.Composition where

open import Aletheia.Prelude
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst)

open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; finalizeL)
open import Aletheia.LTL.Syntax using
  (Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
   MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Simplify using (finalizesHolds; finalizesFails; absorb; simplify; _≡ᵇ-proc_)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending)
open import Aletheia.LTL.Adequacy using (runL; verdictToSV)
open import Aletheia.LTL.SimplifySound.Decomposition using
  ( ≡ᵇ-proc-correct
  ; and-nested-idem-runL
  ; or-nested-idem-runL
  ; and-always-nonempty
  ; or-eventually-nonempty
  ; runL-and-cong-r
  ; runL-or-cong-r
  )

-- ============================================================================
-- SECTION 6: absorb preserves runL
-- ============================================================================

private
  -- Always absorption is sound when φ ≡ ψ and finalizesHolds φ.
  -- finalizesHolds returns false for both Fails and Unsure, so those cases
  -- are refuted by the fh hypothesis.
  always-absorb-sound : ∀ table φ σ →
    finalizesHolds φ ≡ true →
    runL table (Always φ) σ ≡ runL table (And φ (Always φ)) σ
  always-absorb-sound table φ (x ∷ rest) _ =
    sym (and-always-nonempty table φ x rest)
  always-absorb-sound table φ [] fh with finalizeL φ
  ... | Holds    = refl
  ... | Fails _  with () ← fh
  ... | Unsure _ with () ← fh

  -- Eventually absorption is sound when φ ≡ ψ and finalizesFails φ.
  -- The Unsure case would break adequacy (Or ⊥-identity preserves Unsure),
  -- so we require the strictly stronger Fails-definite guard.
  eventually-absorb-sound : ∀ table φ σ →
    finalizesFails φ ≡ true →
    runL table (Eventually φ) σ ≡ runL table (Or φ (Eventually φ)) σ
  eventually-absorb-sound table φ (x ∷ rest) _ =
    sym (or-eventually-nonempty table φ x rest)
  eventually-absorb-sound table φ [] fh with finalizeL φ
  ... | Holds    with () ← fh
  ... | Fails _  = refl
  ... | Unsure _ with () ← fh

absorb-runL : ∀ table φ σ → runL table (absorb φ) σ ≡ runL table φ σ
-- Always absorption: φ ∧ G(ψ) → G(ψ) when φ ≡ᵇ ψ and finalizesHolds φ
absorb-runL table (And φ (Always ψ)) σ
  with φ ≡ᵇ-proc ψ in beq | finalizesHolds φ in fheq
... | false | _     = refl
... | true  | false = refl
... | true  | true
  with refl ← ≡ᵇ-proc-correct φ ψ (subst T (sym beq) tt)
  = always-absorb-sound table φ σ fheq
-- Eventually absorption: φ ∨ F(ψ) → F(ψ) when φ ≡ᵇ ψ and finalizesFails φ
absorb-runL table (Or φ (Eventually ψ)) σ
  with φ ≡ᵇ-proc ψ in beq | finalizesFails φ in fheq
... | false | _     = refl
... | true  | false = refl
... | true  | true
  with refl ← ≡ᵇ-proc-correct φ ψ (subst T (sym beq) tt)
  = eventually-absorb-sound table φ σ fheq
-- And-And idempotency: a ∧ (b ∧ c) → a ∧ c when a ≡ᵇ b
absorb-runL table (And a (And b c)) σ
  with a ≡ᵇ-proc b in beq
... | false = refl
... | true
  with refl ← ≡ᵇ-proc-correct a b (subst T (sym beq) tt)
  = sym (and-nested-idem-runL table a c σ)
-- Or-Or idempotency: a ∨ (b ∨ c) → a ∨ c when a ≡ᵇ b
absorb-runL table (Or a (Or b c)) σ
  with a ≡ᵇ-proc b in beq
... | false = refl
... | true
  with refl ← ≡ᵇ-proc-correct a b (subst T (sym beq) tt)
  = sym (or-nested-idem-runL table a c σ)
-- Catch-all: And with second arg ∉ {Always, And} — absorb returns input
absorb-runL table (And _ (Atomic _)) σ = refl
absorb-runL table (And _ (Not _)) σ = refl
absorb-runL table (And _ (Or _ _)) σ = refl
absorb-runL table (And _ (Next _)) σ = refl
absorb-runL table (And _ (WNext _)) σ = refl
absorb-runL table (And _ (Eventually _)) σ = refl
absorb-runL table (And _ (Until _ _)) σ = refl
absorb-runL table (And _ (Release _ _)) σ = refl
absorb-runL table (And _ (MetricEventually _ _ _)) σ = refl
absorb-runL table (And _ (MetricAlways _ _ _)) σ = refl
absorb-runL table (And _ (MetricUntil _ _ _ _)) σ = refl
absorb-runL table (And _ (MetricRelease _ _ _ _)) σ = refl
-- Catch-all: Or with second arg ∉ {Eventually, Or} — absorb returns input
absorb-runL table (Or _ (Atomic _)) σ = refl
absorb-runL table (Or _ (Not _)) σ = refl
absorb-runL table (Or _ (And _ _)) σ = refl
absorb-runL table (Or _ (Next _)) σ = refl
absorb-runL table (Or _ (WNext _)) σ = refl
absorb-runL table (Or _ (Always _)) σ = refl
absorb-runL table (Or _ (Until _ _)) σ = refl
absorb-runL table (Or _ (Release _ _)) σ = refl
absorb-runL table (Or _ (MetricEventually _ _ _)) σ = refl
absorb-runL table (Or _ (MetricAlways _ _ _)) σ = refl
absorb-runL table (Or _ (MetricUntil _ _ _ _)) σ = refl
absorb-runL table (Or _ (MetricRelease _ _ _ _)) σ = refl
-- All other constructors — absorb returns input
absorb-runL table (Atomic _) σ = refl
absorb-runL table (Not _) σ = refl
absorb-runL table (Next _) σ = refl
absorb-runL table (WNext _) σ = refl
absorb-runL table (Always _) σ = refl
absorb-runL table (Eventually _) σ = refl
absorb-runL table (Until _ _) σ = refl
absorb-runL table (Release _ _) σ = refl
absorb-runL table (MetricEventually _ _ _) σ = refl
absorb-runL table (MetricAlways _ _ _) σ = refl
absorb-runL table (MetricUntil _ _ _ _) σ = refl
absorb-runL table (MetricRelease _ _ _ _) σ = refl

-- ============================================================================
-- SECTION 7: simplify preserves runL
-- ============================================================================

simplify-runL : ∀ table φ σ → runL table (simplify φ) σ ≡ runL table φ σ
simplify-runL table (And a b) σ =
  trans (absorb-runL table (And a (simplify b)) σ)
        (runL-and-cong-r table a (simplify b) b σ (simplify-runL table b σ))
simplify-runL table (Or a b) σ =
  trans (absorb-runL table (Or a (simplify b)) σ)
        (runL-or-cong-r table a (simplify b) b σ (simplify-runL table b σ))
simplify-runL table (Atomic _) σ = refl
simplify-runL table (Not _) σ = refl
simplify-runL table (Next _) σ = refl
simplify-runL table (WNext _) σ = refl
simplify-runL table (Always _) σ = refl
simplify-runL table (Eventually _) σ = refl
simplify-runL table (Until _ _) σ = refl
simplify-runL table (Release _ _) σ = refl
simplify-runL table (MetricEventually _ _ _) σ = refl
simplify-runL table (MetricAlways _ _ _) σ = refl
simplify-runL table (MetricUntil _ _ _ _) σ = refl
simplify-runL table (MetricRelease _ _ _ _) σ = refl

-- ============================================================================
-- SECTION 8: simplify-then-finalize composition (closes AD-12.1)
-- ============================================================================

-- Corollary of `simplify-runL` at the empty trace.
--
-- Statement: simplifying a formula does not change its final verdict under
-- `verdictToSV`. This is the LTL-level composition property for Rosu
-- simplification: pre-composing with `simplify` is sound for any terminal
-- observation that goes through `verdictToSV` (⟦ · ⟧ [] on the denotational
-- side).
--
-- Proof: `runL table proc []` reduces definitionally to
-- `verdictToSV (finalizeL proc)` (Adequacy.agda runL equation for `[]`), so
-- `simplify-runL table proc []` has exactly the target equality under
-- reduction. The PredTable is irrelevant because runL does not consult it on
-- the empty list — we thread a dummy `λ _ _ → Unknown` to satisfy the
-- explicit parameter.
simplify-finalize-sv : ∀ proc
  → verdictToSV (finalizeL (simplify proc)) ≡ verdictToSV (finalizeL proc)
simplify-finalize-sv proc = simplify-runL (λ _ _ → Unknown) proc []
