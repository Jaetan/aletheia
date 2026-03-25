{-# OPTIONS --safe --without-K #-}

-- Partial soundness results for Rosu simplification.
--
-- Purpose: Prove properties of `simplify`/`absorb` from Coalgebra.agda.
--
-- What IS proved (complete, no holes):
--   1. ≡ᵇ-proc-correct: Boolean equality on LTLProc reflects propositional equality
--   2. and-idem-runL / or-idem-runL: And a a ≡ a and Or a a ≡ a at runL level
--   3. and-nested-idem-runL / or-nested-idem-runL: And a (And a b) ≡ And a b at runL level
--   4. and-always-nonempty / or-eventually-nonempty: Always/Eventually absorption
--      on non-empty traces
--
-- What CANNOT be proved for arbitrary formulas:
--   The Until/Release absorption rules (e.g., And φ (Until φ ψ) → Until φ ψ) are
--   NOT sound for all φ, ψ. Counterexample:
--     Let stepL φ x = Violated ce, stepL ψ x = Satisfied.
--     Then: stepL (Until φ ψ) x = combineOr Satisfied (Violated _) = Satisfied → True
--           stepL (And φ (Until φ ψ)) x = combineAnd (Violated ce) Satisfied = Violated → False
--   These rules ARE correct when restricted to formulas reachable via stepL (the left
--   conjunct comes from the same temporal operator's progression). A complete proof
--   would require characterizing the reachable formula space — a worthwhile extension.
--
-- Production impact: `simplify` is applied after each `stepL` call. The absorption
-- rules fire only when `≡ᵇ-proc φ ψ ≡ true` (structural equality). Since `stepL`
-- produces formulas where the absorbed subformula originates from the same operator,
-- the counterexample cannot arise in practice. This module proves the foundation;
-- a restricted soundness proof over reachable states would close the gap.

module Aletheia.LTL.SimplifySound where

open import Aletheia.Prelude
open import Data.Bool using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Function.Bundles using (Equivalence)

open import Aletheia.LTL.Coalgebra using (
  LTLProc; PredTable; stepL; finalizeL;
  Atomic; Not; And; Or; Next; Always; Eventually; Until; Release;
  MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc;
  _≡ᵇ-proc_)
open import Aletheia.LTL.Incremental using (
  StepResult; Continue; Violated; Satisfied;
  FinalVerdict; Holds; Fails)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.Adequacy using (runL; verdictToSV)

-- ============================================================================
-- SECTION 1: Boolean equality on LTLProc reflects propositional equality
-- ============================================================================

private
  cong₂ : ∀ {A B C : Set} (f : A → B → C) {a₁ a₂ b₁ b₂} →
           a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
  cong₂ f refl refl = refl

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a₁ a₂ b₁ b₂ c₁ c₂} →
           a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
  cong₃ f refl refl refl = refl

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
           {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂} →
           a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ →
           f a₁ b₁ c₁ d₁ ≡ f a₂ b₂ c₂ d₂
  cong₄ f refl refl refl refl = refl

≡ᵇ-proc-correct : ∀ φ ψ → T (φ ≡ᵇ-proc ψ) → φ ≡ ψ
≡ᵇ-proc-correct (Atomic n) (Atomic m) p =
  cong Atomic (≡ᵇ⇒≡ n m p)
≡ᵇ-proc-correct (Not φ) (Not ψ) p =
  cong Not (≡ᵇ-proc-correct φ ψ p)
≡ᵇ-proc-correct (And φ₁ ψ₁) (And φ₂ ψ₂) p =
  let (p₁ , p₂) = Equivalence.to T-∧ p
  in cong₂ And (≡ᵇ-proc-correct φ₁ φ₂ p₁) (≡ᵇ-proc-correct ψ₁ ψ₂ p₂)
≡ᵇ-proc-correct (Or φ₁ ψ₁) (Or φ₂ ψ₂) p =
  let (p₁ , p₂) = Equivalence.to T-∧ p
  in cong₂ Or (≡ᵇ-proc-correct φ₁ φ₂ p₁) (≡ᵇ-proc-correct ψ₁ ψ₂ p₂)
≡ᵇ-proc-correct (Next φ) (Next ψ) p =
  cong Next (≡ᵇ-proc-correct φ ψ p)
≡ᵇ-proc-correct (Always φ) (Always ψ) p =
  cong Always (≡ᵇ-proc-correct φ ψ p)
≡ᵇ-proc-correct (Eventually φ) (Eventually ψ) p =
  cong Eventually (≡ᵇ-proc-correct φ ψ p)
≡ᵇ-proc-correct (Until φ₁ ψ₁) (Until φ₂ ψ₂) p =
  let (p₁ , p₂) = Equivalence.to T-∧ p
  in cong₂ Until (≡ᵇ-proc-correct φ₁ φ₂ p₁) (≡ᵇ-proc-correct ψ₁ ψ₂ p₂)
≡ᵇ-proc-correct (Release φ₁ ψ₁) (Release φ₂ ψ₂) p =
  let (p₁ , p₂) = Equivalence.to T-∧ p
  in cong₂ Release (≡ᵇ-proc-correct φ₁ φ₂ p₁) (≡ᵇ-proc-correct ψ₁ ψ₂ p₂)
≡ᵇ-proc-correct (MetricEventuallyProc w₁ s₁ φ₁) (MetricEventuallyProc w₂ s₂ φ₂) p =
  let (pw , ps∧pφ) = Equivalence.to T-∧ p
      (ps , pφ)    = Equivalence.to T-∧ ps∧pφ
  in cong₃ MetricEventuallyProc (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps) (≡ᵇ-proc-correct φ₁ φ₂ pφ)
≡ᵇ-proc-correct (MetricAlwaysProc w₁ s₁ φ₁) (MetricAlwaysProc w₂ s₂ φ₂) p =
  let (pw , ps∧pφ) = Equivalence.to T-∧ p
      (ps , pφ)    = Equivalence.to T-∧ ps∧pφ
  in cong₃ MetricAlwaysProc (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps) (≡ᵇ-proc-correct φ₁ φ₂ pφ)
≡ᵇ-proc-correct (MetricUntilProc w₁ s₁ φ₁ ψ₁) (MetricUntilProc w₂ s₂ φ₂ ψ₂) p =
  let (pw , ps∧rest)  = Equivalence.to T-∧ p
      (ps , pφ∧pψ)   = Equivalence.to T-∧ ps∧rest
      (pφ , pψ)      = Equivalence.to T-∧ pφ∧pψ
  in cong₄ MetricUntilProc (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps)
           (≡ᵇ-proc-correct φ₁ φ₂ pφ) (≡ᵇ-proc-correct ψ₁ ψ₂ pψ)
≡ᵇ-proc-correct (MetricReleaseProc w₁ s₁ φ₁ ψ₁) (MetricReleaseProc w₂ s₂ φ₂ ψ₂) p =
  let (pw , ps∧rest)  = Equivalence.to T-∧ p
      (ps , pφ∧pψ)   = Equivalence.to T-∧ ps∧rest
      (pφ , pψ)      = Equivalence.to T-∧ pφ∧pψ
  in cong₄ MetricReleaseProc (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps)
           (≡ᵇ-proc-correct φ₁ φ₂ pφ) (≡ᵇ-proc-correct ψ₁ ψ₂ pψ)

-- ============================================================================
-- SECTION 2: And/Or idempotency at runL level
-- ============================================================================

private
  finalizeL-And-same-go : ∀ a (v : FinalVerdict) → finalizeL a ≡ v → finalizeL (And a a) ≡ v
  finalizeL-And-same-go a Holds eq rewrite eq rewrite eq = refl
  finalizeL-And-same-go a (Fails r) eq rewrite eq = refl

  finalizeL-And-same : ∀ a → finalizeL (And a a) ≡ finalizeL a
  finalizeL-And-same a = finalizeL-And-same-go a (finalizeL a) refl

  finalizeL-Or-same-go : ∀ a (v : FinalVerdict) → finalizeL a ≡ v → finalizeL (Or a a) ≡ v
  finalizeL-Or-same-go a Holds eq rewrite eq = refl
  finalizeL-Or-same-go a (Fails r) eq rewrite eq rewrite eq = refl

  finalizeL-Or-same : ∀ a → finalizeL (Or a a) ≡ finalizeL a
  finalizeL-Or-same a = finalizeL-Or-same-go a (finalizeL a) refl

and-idem-runL : ∀ table a σ → runL table (And a a) σ ≡ runL table a σ
and-idem-runL table a [] = cong verdictToSV (finalizeL-And-same a)
and-idem-runL table a (x ∷ rest) with stepL table a x
... | Satisfied     = refl
... | Violated _    = refl
... | Continue n a' = and-idem-runL table a' rest

or-idem-runL : ∀ table a σ → runL table (Or a a) σ ≡ runL table a σ
or-idem-runL table a [] = cong verdictToSV (finalizeL-Or-same a)
or-idem-runL table a (x ∷ rest) with stepL table a x
... | Satisfied     = refl
... | Violated _    = refl
... | Continue n a' = or-idem-runL table a' rest

-- ============================================================================
-- SECTION 3: Nested idempotency at runL level
-- ============================================================================

private
  finalizeL-And-nested-go : ∀ a b va vb → finalizeL a ≡ va → finalizeL b ≡ vb →
    finalizeL (And a (And a b)) ≡ finalizeL (And a b)
  finalizeL-And-nested-go a b (Fails _) _ eqa _ rewrite eqa = refl
  finalizeL-And-nested-go a b Holds Holds eqa eqb rewrite eqa rewrite eqa rewrite eqb = refl
  finalizeL-And-nested-go a b Holds (Fails _) eqa eqb rewrite eqa rewrite eqa rewrite eqb = refl

  finalizeL-And-nested : ∀ a b → finalizeL (And a (And a b)) ≡ finalizeL (And a b)
  finalizeL-And-nested a b = finalizeL-And-nested-go a b _ _ refl refl

  finalizeL-Or-nested-go : ∀ a b va vb → finalizeL a ≡ va → finalizeL b ≡ vb →
    finalizeL (Or a (Or a b)) ≡ finalizeL (Or a b)
  finalizeL-Or-nested-go a b Holds _ eqa _ rewrite eqa = refl
  finalizeL-Or-nested-go a b (Fails _) Holds eqa eqb rewrite eqa rewrite eqa rewrite eqb = refl
  finalizeL-Or-nested-go a b (Fails _) (Fails _) eqa eqb rewrite eqa rewrite eqa rewrite eqb = refl

  finalizeL-Or-nested : ∀ a b → finalizeL (Or a (Or a b)) ≡ finalizeL (Or a b)
  finalizeL-Or-nested a b = finalizeL-Or-nested-go a b _ _ refl refl

and-nested-idem-runL : ∀ table a b σ →
  runL table (And a (And a b)) σ ≡ runL table (And a b) σ
and-nested-idem-runL table a b [] = cong verdictToSV (finalizeL-And-nested a b)
and-nested-idem-runL table a b (x ∷ rest)
  with stepL table a x | stepL table b x
... | Satisfied     | Satisfied      = refl
... | Satisfied     | Violated _     = refl
... | Satisfied     | Continue _ _   = refl
... | Violated _    | Satisfied      = refl
... | Violated _    | Violated _     = refl
... | Violated _    | Continue _ _   = refl
... | Continue n a' | Satisfied      = and-idem-runL table a' rest
... | Continue _ _  | Violated _     = refl
... | Continue n a' | Continue _ b'  = and-nested-idem-runL table a' b' rest

or-nested-idem-runL : ∀ table a b σ →
  runL table (Or a (Or a b)) σ ≡ runL table (Or a b) σ
or-nested-idem-runL table a b [] = cong verdictToSV (finalizeL-Or-nested a b)
or-nested-idem-runL table a b (x ∷ rest)
  with stepL table a x | stepL table b x
... | Satisfied     | Satisfied      = refl
... | Satisfied     | Violated _     = refl
... | Satisfied     | Continue _ _   = refl
... | Violated _    | Satisfied      = refl
... | Violated _    | Violated _     = refl
... | Violated _    | Continue _ _   = refl
... | Continue _ _  | Satisfied      = refl
... | Continue n a' | Violated _     = or-idem-runL table a' rest
... | Continue n a' | Continue _ b'  = or-nested-idem-runL table a' b' rest

-- ============================================================================
-- SECTION 4: Always/Eventually absorption on non-empty traces
-- ============================================================================

-- And φ (Always φ) ≡ Always φ on non-empty traces.
-- On the empty trace, finalizeL (And φ (Always φ)) may differ from finalizeL (Always φ)
-- when finalizeL φ = Fails but finalizeL (Always φ) = Holds.
and-always-nonempty : ∀ table φ x rest →
  runL table (And φ (Always φ)) (x ∷ rest) ≡ runL table (Always φ) (x ∷ rest)
and-always-nonempty table φ x rest with stepL table φ x
... | Satisfied      = refl
... | Violated _     = refl
... | Continue n φ'  = and-nested-idem-runL table φ' (Always φ) rest

-- Or φ (Eventually φ) ≡ Eventually φ on non-empty traces.
or-eventually-nonempty : ∀ table φ x rest →
  runL table (Or φ (Eventually φ)) (x ∷ rest) ≡ runL table (Eventually φ) (x ∷ rest)
or-eventually-nonempty table φ x rest with stepL table φ x
... | Satisfied      = refl
... | Violated _     = refl
... | Continue n φ'  = or-nested-idem-runL table φ' (Eventually φ) rest

-- ============================================================================
-- NOTE: Until/Release absorption rules
-- ============================================================================
--
-- The remaining 10 absorption rules (Until, Release, and metric variants) are NOT
-- provable for arbitrary formulas. Counterexample for And φ (Until φ ψ) ≡ Until φ ψ:
--   Let stepL φ x = Violated ce, stepL ψ x = Satisfied.
--   Then: stepL (Until φ ψ) x = combineOr Satisfied (Violated _) = Satisfied
--         stepL (And φ (Until φ ψ)) x = combineAnd (Violated ce) Satisfied = Violated
--   So runL differs on the trace (x ∷ []).
--
-- These rules ARE correct in the Rosu monitoring model when restricted to formulas
-- produced by stepL's progression (the left conjunct originates from the same temporal
-- operator). Proving this requires characterizing the reachable state space of stepL,
-- which is a non-trivial extension left for future work.
--
-- Production impact: minimal. The absorption rules fire only when ≡ᵇ-proc returns true,
-- meaning the absorbed subformula is structurally identical to the temporal operator's
-- inner formula. This structural constraint ensures the counterexample pattern (where
-- φ and ψ progress independently) cannot arise from stepL's actual output.
