{-# OPTIONS --safe --without-K #-}

-- Proof infrastructure for SimplifySound — sections 1-5.
--
-- Purpose: Decomposition lemmas + runL congruence used by the main
--   simplification soundness theorem in SimplifySound.Composition.
-- Public API:
--   * ≡ᵇ-proc-correct                — boolean LTLProc equality reflects ≡
--   * and-idem-runL / or-idem-runL    — runL idempotency
--   * and-nested-idem-runL /
--     or-nested-idem-runL             — runL nested idempotency
--   * and-always-nonempty /
--     or-eventually-nonempty          — Always/Eventually absorption (non-empty)
--   * runL-and-right-True/False,
--     runL-and-cong-r,
--     runL-or-right-True/False,
--     runL-or-cong-r                  — pointwise runL congruence helpers
--
-- Role: First-layer proof engine for SimplifySound — establishes how
--   `finalizeL` decomposes through And/Or and how `runL` respects congruence
--   under right-side equivalences. The Composition layer (absorb-runL,
--   simplify-runL) consumes only the public API and never touches the
--   private decomposition helpers.
module Aletheia.LTL.SimplifySound.Decomposition where

open import Aletheia.Prelude
open import Data.Bool using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; cong₂)
open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Function.Bundles using (Equivalence)

open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL)
open import Aletheia.LTL.Syntax using
  (Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
   MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Simplify using (_≡ᵇ-proc_)
open import Aletheia.LTL.Incremental using (
  StepResult; Continue; Violated; Satisfied;
  FinalVerdict; Holds; Fails; Unsure)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.Adequacy using (runL; verdictToSV)

-- ============================================================================
-- SECTION 1: Boolean equality on LTLProc reflects propositional equality
-- ============================================================================

private
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
≡ᵇ-proc-correct (WNext φ) (WNext ψ) p =
  cong WNext (≡ᵇ-proc-correct φ ψ p)
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
≡ᵇ-proc-correct (MetricEventually w₁ s₁ φ₁) (MetricEventually w₂ s₂ φ₂) p =
  let (pw , ps∧pφ) = Equivalence.to T-∧ p
      (ps , pφ)    = Equivalence.to T-∧ ps∧pφ
  in cong₃ MetricEventually (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps) (≡ᵇ-proc-correct φ₁ φ₂ pφ)
≡ᵇ-proc-correct (MetricAlways w₁ s₁ φ₁) (MetricAlways w₂ s₂ φ₂) p =
  let (pw , ps∧pφ) = Equivalence.to T-∧ p
      (ps , pφ)    = Equivalence.to T-∧ ps∧pφ
  in cong₃ MetricAlways (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps) (≡ᵇ-proc-correct φ₁ φ₂ pφ)
≡ᵇ-proc-correct (MetricUntil w₁ s₁ φ₁ ψ₁) (MetricUntil w₂ s₂ φ₂ ψ₂) p =
  let (pw , ps∧rest)  = Equivalence.to T-∧ p
      (ps , pφ∧pψ)   = Equivalence.to T-∧ ps∧rest
      (pφ , pψ)      = Equivalence.to T-∧ pφ∧pψ
  in cong₄ MetricUntil (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps)
           (≡ᵇ-proc-correct φ₁ φ₂ pφ) (≡ᵇ-proc-correct ψ₁ ψ₂ pψ)
≡ᵇ-proc-correct (MetricRelease w₁ s₁ φ₁ ψ₁) (MetricRelease w₂ s₂ φ₂ ψ₂) p =
  let (pw , ps∧rest)  = Equivalence.to T-∧ p
      (ps , pφ∧pψ)   = Equivalence.to T-∧ ps∧rest
      (pφ , pψ)      = Equivalence.to T-∧ pφ∧pψ
  in cong₄ MetricRelease (≡ᵇ⇒≡ w₁ w₂ pw) (≡ᵇ⇒≡ s₁ s₂ ps)
           (≡ᵇ-proc-correct φ₁ φ₂ pφ) (≡ᵇ-proc-correct ψ₁ ψ₂ pψ)

-- ============================================================================
-- SECTION 2: And/Or idempotency at runL level
-- ============================================================================

private
  -- Decomposition helpers: `finalizeL (And a b)` / `(Or a b)` are determined by
  -- `finalizeL a`. Each helper commits the outer `with` via `rewrite eq`, then
  -- commits the inner `with finalizeL b` by pattern-matching — avoiding the
  -- double-`rewrite` pattern of the earlier proof (both `finalizeL a` and
  -- `finalizeL b` are stuck under the compiled with-auxiliary until they're
  -- driven to a concrete constructor).
  finalizeL-And-Holds : ∀ a b → finalizeL a ≡ Holds → finalizeL (And a b) ≡ finalizeL b
  finalizeL-And-Holds a b eq rewrite eq with finalizeL b
  ... | Holds    = refl
  ... | Fails r  = refl
  ... | Unsure r = refl

  finalizeL-And-Fails : ∀ a b r → finalizeL a ≡ Fails r → finalizeL (And a b) ≡ Fails r
  finalizeL-And-Fails a b r eq rewrite eq = refl

  -- Three Unsure-on-left decomposition helpers: when `finalizeL a = Unsure r`,
  -- `finalizeL (And a b)` depends on `finalizeL b` (Fails drops, else Unsure r).
  finalizeL-And-Unsure-Holds : ∀ a b r → finalizeL a ≡ Unsure r → finalizeL b ≡ Holds →
    finalizeL (And a b) ≡ Unsure r
  finalizeL-And-Unsure-Holds a b r eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  finalizeL-And-Unsure-Fails : ∀ a b r r′ → finalizeL a ≡ Unsure r → finalizeL b ≡ Fails r′ →
    finalizeL (And a b) ≡ Fails r′
  finalizeL-And-Unsure-Fails a b r r′ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  finalizeL-And-Unsure-Unsure : ∀ a b r r′ → finalizeL a ≡ Unsure r → finalizeL b ≡ Unsure r′ →
    finalizeL (And a b) ≡ Unsure r
  finalizeL-And-Unsure-Unsure a b r r′ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  finalizeL-Or-Holds : ∀ a b → finalizeL a ≡ Holds → finalizeL (Or a b) ≡ Holds
  finalizeL-Or-Holds a b eq rewrite eq = refl

  finalizeL-Or-Fails : ∀ a b r → finalizeL a ≡ Fails r → finalizeL (Or a b) ≡ finalizeL b
  finalizeL-Or-Fails a b r eq rewrite eq with finalizeL b
  ... | Holds    = refl
  ... | Fails r′ = refl
  ... | Unsure r′ = refl

  -- Three Unsure-on-left decomposition helpers for Or: Holds absorbs, else Unsure r.
  finalizeL-Or-Unsure-Holds : ∀ a b r → finalizeL a ≡ Unsure r → finalizeL b ≡ Holds →
    finalizeL (Or a b) ≡ Holds
  finalizeL-Or-Unsure-Holds a b r eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  finalizeL-Or-Unsure-Fails : ∀ a b r r′ → finalizeL a ≡ Unsure r → finalizeL b ≡ Fails r′ →
    finalizeL (Or a b) ≡ Unsure r
  finalizeL-Or-Unsure-Fails a b r r′ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  finalizeL-Or-Unsure-Unsure : ∀ a b r r′ → finalizeL a ≡ Unsure r → finalizeL b ≡ Unsure r′ →
    finalizeL (Or a b) ≡ Unsure r
  finalizeL-Or-Unsure-Unsure a b r r′ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- `-go` wrappers pattern-match on the value of `finalizeL a` and compose the
  -- decomposition helpers. Avoids `with … in eq` because the outer goal
  -- `finalizeL (And a a)` does not syntactically mention `finalizeL a`, so the
  -- `with`-abstraction would leave an unreduced auxiliary on the LHS.
  finalizeL-And-same-go : ∀ a (v : FinalVerdict) → finalizeL a ≡ v →
    finalizeL (And a a) ≡ v
  finalizeL-And-same-go a Holds      eq = trans (finalizeL-And-Holds a a eq) eq
  finalizeL-And-same-go a (Fails r)  eq = finalizeL-And-Fails a a r eq
  finalizeL-And-same-go a (Unsure r) eq = finalizeL-And-Unsure-Unsure a a r r eq eq

  finalizeL-And-same : ∀ a → finalizeL (And a a) ≡ finalizeL a
  finalizeL-And-same a = finalizeL-And-same-go a (finalizeL a) refl

  finalizeL-Or-same-go : ∀ a (v : FinalVerdict) → finalizeL a ≡ v →
    finalizeL (Or a a) ≡ v
  finalizeL-Or-same-go a Holds      eq = finalizeL-Or-Holds a a eq
  finalizeL-Or-same-go a (Fails r)  eq = trans (finalizeL-Or-Fails a a r eq) eq
  finalizeL-Or-same-go a (Unsure r) eq = finalizeL-Or-Unsure-Unsure a a r r eq eq

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
  -- Nested idempotency: `finalizeL (And a (And a b)) ≡ finalizeL (And a b)`.
  -- Case-split on `finalizeL a` via a `-go` wrapper, then compose the
  -- decomposition helpers. The Fails case uses `sym` to bridge the two
  -- independent applications on `And a (And a b)` and `And a b`.
  finalizeL-And-nested-go : ∀ a b (va : FinalVerdict) → finalizeL a ≡ va →
    finalizeL (And a (And a b)) ≡ finalizeL (And a b)
  finalizeL-And-nested-go a b Holds     eqa = finalizeL-And-Holds a (And a b) eqa
  finalizeL-And-nested-go a b (Fails r) eqa =
    trans (finalizeL-And-Fails a (And a b) r eqa)
          (sym (finalizeL-And-Fails a b r eqa))
  -- Unsure-on-left: split on `finalizeL b` to determine `finalizeL (And a b)`,
  -- then compose with the outer And a (And a b) using the matching helper.
  finalizeL-And-nested-go a b (Unsure r) eqa = finalizeL-And-nested-Unsure a b r eqa (finalizeL b) refl
    where
      finalizeL-And-nested-Unsure : ∀ a b r → finalizeL a ≡ Unsure r →
        ∀ (vb : FinalVerdict) → finalizeL b ≡ vb →
        finalizeL (And a (And a b)) ≡ finalizeL (And a b)
      finalizeL-And-nested-Unsure a b r eqa Holds eqb =
        trans (finalizeL-And-Unsure-Unsure a (And a b) r r eqa
                 (finalizeL-And-Unsure-Holds a b r eqa eqb))
              (sym (finalizeL-And-Unsure-Holds a b r eqa eqb))
      finalizeL-And-nested-Unsure a b r eqa (Fails r′) eqb =
        trans (finalizeL-And-Unsure-Fails a (And a b) r r′ eqa
                 (finalizeL-And-Unsure-Fails a b r r′ eqa eqb))
              (sym (finalizeL-And-Unsure-Fails a b r r′ eqa eqb))
      finalizeL-And-nested-Unsure a b r eqa (Unsure r′) eqb =
        trans (finalizeL-And-Unsure-Unsure a (And a b) r r eqa
                 (finalizeL-And-Unsure-Unsure a b r r′ eqa eqb))
              (sym (finalizeL-And-Unsure-Unsure a b r r′ eqa eqb))

  finalizeL-And-nested : ∀ a b → finalizeL (And a (And a b)) ≡ finalizeL (And a b)
  finalizeL-And-nested a b = finalizeL-And-nested-go a b (finalizeL a) refl

  finalizeL-Or-nested-go : ∀ a b (va : FinalVerdict) → finalizeL a ≡ va →
    finalizeL (Or a (Or a b)) ≡ finalizeL (Or a b)
  finalizeL-Or-nested-go a b Holds     eqa =
    trans (finalizeL-Or-Holds a (Or a b) eqa)
          (sym (finalizeL-Or-Holds a b eqa))
  finalizeL-Or-nested-go a b (Fails r) eqa = finalizeL-Or-Fails a (Or a b) r eqa
  -- Unsure-on-left: split on `finalizeL b` just as for And.
  finalizeL-Or-nested-go a b (Unsure r) eqa = finalizeL-Or-nested-Unsure a b r eqa (finalizeL b) refl
    where
      finalizeL-Or-nested-Unsure : ∀ a b r → finalizeL a ≡ Unsure r →
        ∀ (vb : FinalVerdict) → finalizeL b ≡ vb →
        finalizeL (Or a (Or a b)) ≡ finalizeL (Or a b)
      finalizeL-Or-nested-Unsure a b r eqa Holds eqb =
        trans (finalizeL-Or-Unsure-Holds a (Or a b) r eqa
                 (finalizeL-Or-Unsure-Holds a b r eqa eqb))
              (sym (finalizeL-Or-Unsure-Holds a b r eqa eqb))
      finalizeL-Or-nested-Unsure a b r eqa (Fails r′) eqb =
        trans (finalizeL-Or-Unsure-Unsure a (Or a b) r r eqa
                 (finalizeL-Or-Unsure-Fails a b r r′ eqa eqb))
              (sym (finalizeL-Or-Unsure-Fails a b r r′ eqa eqb))
      finalizeL-Or-nested-Unsure a b r eqa (Unsure r′) eqb =
        trans (finalizeL-Or-Unsure-Unsure a (Or a b) r r eqa
                 (finalizeL-Or-Unsure-Unsure a b r r′ eqa eqb))
              (sym (finalizeL-Or-Unsure-Unsure a b r r′ eqa eqb))

  finalizeL-Or-nested : ∀ a b → finalizeL (Or a (Or a b)) ≡ finalizeL (Or a b)
  finalizeL-Or-nested a b = finalizeL-Or-nested-go a b (finalizeL a) refl

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
-- SECTION 5: runL congruence infrastructure
-- ============================================================================

-- When the right side of And evaluates to True, And a b ≡ a at runL level.
-- Empty-trace helpers: the partial evaluation form `finalizeL (And a b) | w`
-- that Agda produces under `with finalizeL a` doesn't auto-reduce past the
-- inner `with finalizeL ψ` in finalizeL's And clause. To force full reduction,
-- we case-split on the VALUES of finalizeL a and finalizeL b before exposing
-- `finalizeL (And a b)` to rewrite — the helpers (finalizeL-And-Holds /
-- -Fails / -Unsure-Holds / -Unsure-Fails / -Unsure-Unsure) then fire
-- cleanly. This pattern applies to all four -right-True/-False and two -cong-r
-- wrappers so that each fully-reduces its empty-trace case.
--
-- Design note (finding A25): the six empty-trace helpers below (3 for And,
-- 3 for Or) were considered for extraction into a generic dispatcher
-- parameterized by (And/Or, decomposition lemmas, target property). This
-- was rejected because:
--   (a) Each helper calls DIFFERENT decomposition lemmas (finalizeL-And-*
--       vs finalizeL-Or-*) with different arity/signatures.
--   (b) The right-True, right-False, and cong-r variants have different
--       return types and different case analysis shapes (Unsure cases
--       differ between And and Or because of different K3 absorbers).
--   (c) The purpose of these helpers is to force Agda's reduction through
--       the FinalVerdict case split — a generic dispatcher would still
--       need the same case analysis, just with more parameters.
-- The helpers are private to this module and not part of any public API.
private
  runL-and-right-True-[] :
    ∀ a b (fa fb : FinalVerdict) →
    finalizeL a ≡ fa → finalizeL b ≡ fb → verdictToSV fb ≡ True →
    verdictToSV (finalizeL (And a b)) ≡ verdictToSV fa
  runL-and-right-True-[] a b Holds      Holds      eqA eqB _
    rewrite finalizeL-And-Holds a b eqA | eqB = refl
  runL-and-right-True-[] a b Holds      (Fails _)  eqA eqB ()
  runL-and-right-True-[] a b Holds      (Unsure _) eqA eqB ()
  runL-and-right-True-[] a b (Fails r)  Holds      eqA _ _
    rewrite finalizeL-And-Fails a b r eqA = refl
  runL-and-right-True-[] a b (Fails _)  (Fails _)  eqA eqB ()
  runL-and-right-True-[] a b (Fails _)  (Unsure _) eqA eqB ()
  runL-and-right-True-[] a b (Unsure r) Holds      eqA eqB _
    rewrite finalizeL-And-Unsure-Holds a b r eqA eqB = refl
  runL-and-right-True-[] a b (Unsure _) (Fails _)  eqA eqB ()
  runL-and-right-True-[] a b (Unsure _) (Unsure _) eqA eqB ()

  runL-and-right-False-[] :
    ∀ a b (fa fb : FinalVerdict) →
    finalizeL a ≡ fa → finalizeL b ≡ fb → verdictToSV fb ≡ False →
    verdictToSV (finalizeL (And a b)) ≡ False
  runL-and-right-False-[] a b Holds      Holds      eqA eqB ()
  runL-and-right-False-[] a b Holds      (Fails r) eqA eqB _
    rewrite finalizeL-And-Holds a b eqA | eqB = refl
  runL-and-right-False-[] a b Holds      (Unsure _) eqA eqB ()
  runL-and-right-False-[] a b (Fails r)  _          eqA _ _
    rewrite finalizeL-And-Fails a b r eqA = refl
  runL-and-right-False-[] a b (Unsure _) Holds      eqA eqB ()
  runL-and-right-False-[] a b (Unsure r) (Fails r′) eqA eqB _
    rewrite finalizeL-And-Unsure-Fails a b r r′ eqA eqB = refl
  runL-and-right-False-[] a b (Unsure _) (Unsure _) eqA eqB ()

  runL-and-cong-r-[] :
    ∀ a b₁ b₂ (fa fb₁ fb₂ : FinalVerdict) →
    finalizeL a ≡ fa → finalizeL b₁ ≡ fb₁ → finalizeL b₂ ≡ fb₂ →
    verdictToSV fb₁ ≡ verdictToSV fb₂ →
    verdictToSV (finalizeL (And a b₁)) ≡ verdictToSV (finalizeL (And a b₂))
  runL-and-cong-r-[] a b₁ b₂ (Fails r) _ _ eqA _ _ _
    rewrite finalizeL-And-Fails a b₁ r eqA | finalizeL-And-Fails a b₂ r eqA = refl
  runL-and-cong-r-[] a b₁ b₂ Holds _ _ eqA eq₁ eq₂ hyp
    rewrite finalizeL-And-Holds a b₁ eqA | finalizeL-And-Holds a b₂ eqA | eq₁ | eq₂ = hyp
  runL-and-cong-r-[] a b₁ b₂ (Unsure r) Holds Holds eqA eq₁ eq₂ _
    rewrite finalizeL-And-Unsure-Holds a b₁ r eqA eq₁
          | finalizeL-And-Unsure-Holds a b₂ r eqA eq₂ = refl
  runL-and-cong-r-[] a b₁ b₂ (Unsure _) Holds (Fails _) eqA _ _ ()
  runL-and-cong-r-[] a b₁ b₂ (Unsure r) Holds (Unsure r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-And-Unsure-Holds a b₁ r eqA eq₁
          | finalizeL-And-Unsure-Unsure a b₂ r r₂ eqA eq₂ = refl
  runL-and-cong-r-[] a b₁ b₂ (Unsure _) (Fails _) Holds eqA _ _ ()
  runL-and-cong-r-[] a b₁ b₂ (Unsure r) (Fails r₁) (Fails r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-And-Unsure-Fails a b₁ r r₁ eqA eq₁
          | finalizeL-And-Unsure-Fails a b₂ r r₂ eqA eq₂ = refl
  runL-and-cong-r-[] a b₁ b₂ (Unsure _) (Fails _) (Unsure _) eqA _ _ ()
  runL-and-cong-r-[] a b₁ b₂ (Unsure r) (Unsure r₁) Holds eqA eq₁ eq₂ _
    rewrite finalizeL-And-Unsure-Unsure a b₁ r r₁ eqA eq₁
          | finalizeL-And-Unsure-Holds a b₂ r eqA eq₂ = refl
  runL-and-cong-r-[] a b₁ b₂ (Unsure _) (Unsure _) (Fails _) eqA _ _ ()
  runL-and-cong-r-[] a b₁ b₂ (Unsure r) (Unsure r₁) (Unsure r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-And-Unsure-Unsure a b₁ r r₁ eqA eq₁
          | finalizeL-And-Unsure-Unsure a b₂ r r₂ eqA eq₂ = refl

  runL-or-right-True-[] :
    ∀ a b (fa fb : FinalVerdict) →
    finalizeL a ≡ fa → finalizeL b ≡ fb → verdictToSV fb ≡ True →
    verdictToSV (finalizeL (Or a b)) ≡ True
  runL-or-right-True-[] a b Holds      _          eqA _ _
    rewrite finalizeL-Or-Holds a b eqA = refl
  runL-or-right-True-[] a b (Fails r)  Holds      eqA eqB _
    rewrite finalizeL-Or-Fails a b r eqA | eqB = refl
  runL-or-right-True-[] a b (Fails _)  (Fails _)  eqA eqB ()
  runL-or-right-True-[] a b (Fails _)  (Unsure _) eqA eqB ()
  runL-or-right-True-[] a b (Unsure _) Holds      eqA eqB _
    rewrite finalizeL-Or-Unsure-Holds a b _ eqA eqB = refl
  runL-or-right-True-[] a b (Unsure _) (Fails _)  eqA eqB ()
  runL-or-right-True-[] a b (Unsure _) (Unsure _) eqA eqB ()

  runL-or-right-False-[] :
    ∀ a b (fa fb : FinalVerdict) →
    finalizeL a ≡ fa → finalizeL b ≡ fb → verdictToSV fb ≡ False →
    verdictToSV (finalizeL (Or a b)) ≡ verdictToSV fa
  runL-or-right-False-[] a b Holds      _          eqA _ _
    rewrite finalizeL-Or-Holds a b eqA = refl
  runL-or-right-False-[] a b (Fails _)  Holds      eqA eqB ()
  runL-or-right-False-[] a b (Fails r)  (Fails r′) eqA eqB _
    rewrite finalizeL-Or-Fails a b r eqA | eqB = refl
  runL-or-right-False-[] a b (Fails _)  (Unsure _) eqA eqB ()
  runL-or-right-False-[] a b (Unsure _) Holds      eqA eqB ()
  runL-or-right-False-[] a b (Unsure r) (Fails r′) eqA eqB _
    rewrite finalizeL-Or-Unsure-Fails a b r r′ eqA eqB = refl
  runL-or-right-False-[] a b (Unsure _) (Unsure _) eqA eqB ()

  runL-or-cong-r-[] :
    ∀ a b₁ b₂ (fa fb₁ fb₂ : FinalVerdict) →
    finalizeL a ≡ fa → finalizeL b₁ ≡ fb₁ → finalizeL b₂ ≡ fb₂ →
    verdictToSV fb₁ ≡ verdictToSV fb₂ →
    verdictToSV (finalizeL (Or a b₁)) ≡ verdictToSV (finalizeL (Or a b₂))
  runL-or-cong-r-[] a b₁ b₂ Holds _ _ eqA _ _ _
    rewrite finalizeL-Or-Holds a b₁ eqA | finalizeL-Or-Holds a b₂ eqA = refl
  runL-or-cong-r-[] a b₁ b₂ (Fails r) _ _ eqA eq₁ eq₂ hyp
    rewrite finalizeL-Or-Fails a b₁ r eqA | finalizeL-Or-Fails a b₂ r eqA | eq₁ | eq₂ = hyp
  runL-or-cong-r-[] a b₁ b₂ (Unsure r) Holds Holds eqA eq₁ eq₂ _
    rewrite finalizeL-Or-Unsure-Holds a b₁ r eqA eq₁
          | finalizeL-Or-Unsure-Holds a b₂ r eqA eq₂ = refl
  runL-or-cong-r-[] a b₁ b₂ (Unsure _) Holds (Fails _) eqA _ _ ()
  runL-or-cong-r-[] a b₁ b₂ (Unsure _) Holds (Unsure _) eqA _ _ ()
  runL-or-cong-r-[] a b₁ b₂ (Unsure _) (Fails _) Holds eqA _ _ ()
  runL-or-cong-r-[] a b₁ b₂ (Unsure r) (Fails r₁) (Fails r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-Or-Unsure-Fails a b₁ r r₁ eqA eq₁
          | finalizeL-Or-Unsure-Fails a b₂ r r₂ eqA eq₂ = refl
  runL-or-cong-r-[] a b₁ b₂ (Unsure r) (Fails r₁) (Unsure r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-Or-Unsure-Fails a b₁ r r₁ eqA eq₁
          | finalizeL-Or-Unsure-Unsure a b₂ r r₂ eqA eq₂ = refl
  runL-or-cong-r-[] a b₁ b₂ (Unsure _) (Unsure _) Holds eqA _ _ ()
  runL-or-cong-r-[] a b₁ b₂ (Unsure r) (Unsure r₁) (Fails r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-Or-Unsure-Unsure a b₁ r r₁ eqA eq₁
          | finalizeL-Or-Unsure-Fails a b₂ r r₂ eqA eq₂ = refl
  runL-or-cong-r-[] a b₁ b₂ (Unsure r) (Unsure r₁) (Unsure r₂) eqA eq₁ eq₂ _
    rewrite finalizeL-Or-Unsure-Unsure a b₁ r r₁ eqA eq₁
          | finalizeL-Or-Unsure-Unsure a b₂ r r₂ eqA eq₂ = refl

runL-and-right-True : ∀ table a b σ → runL table b σ ≡ True →
  runL table (And a b) σ ≡ runL table a σ
runL-and-right-True table a b [] hyp =
  runL-and-right-True-[] a b (finalizeL a) (finalizeL b) refl refl hyp
runL-and-right-True table a b (x ∷ rest) hyp
  with stepL table a x | stepL table b x
... | Violated _    | _              = refl
... | Satisfied     | Satisfied      = refl
... | Satisfied     | Violated _     with () ← hyp
... | Satisfied     | Continue _ _   = hyp
... | Continue _ _  | Satisfied      = refl
... | Continue _ _  | Violated _     with () ← hyp
... | Continue _ a' | Continue _ b'  = runL-and-right-True table a' b' rest hyp

-- When the right side of And evaluates to False, And a b ≡ False.
runL-and-right-False : ∀ table a b σ → runL table b σ ≡ False →
  runL table (And a b) σ ≡ False
runL-and-right-False table a b [] hyp =
  runL-and-right-False-[] a b (finalizeL a) (finalizeL b) refl refl hyp
runL-and-right-False table a b (x ∷ rest) hyp
  with stepL table a x | stepL table b x
... | Violated _    | _              = refl
... | Satisfied     | Satisfied      with () ← hyp
... | Satisfied     | Violated _     = refl
... | Satisfied     | Continue _ _   = hyp
... | Continue _ _  | Satisfied      with () ← hyp
... | Continue _ _  | Violated _     = refl
... | Continue _ a' | Continue _ b'  = runL-and-right-False table a' b' rest hyp

-- Pointwise congruence: if b₁ ≡ b₂ at runL level, And a b₁ ≡ And a b₂.
runL-and-cong-r : ∀ table a b₁ b₂ σ →
  runL table b₁ σ ≡ runL table b₂ σ →
  runL table (And a b₁) σ ≡ runL table (And a b₂) σ
runL-and-cong-r table a b₁ b₂ [] hyp =
  runL-and-cong-r-[] a b₁ b₂ (finalizeL a) (finalizeL b₁) (finalizeL b₂)
    refl refl refl hyp
runL-and-cong-r table a b₁ b₂ (x ∷ rest) hyp
  with stepL table a x | stepL table b₁ x | stepL table b₂ x
... | Violated _    | _              | _              = refl
... | Satisfied     | Satisfied      | Satisfied      = refl
... | Satisfied     | Satisfied      | Violated _     with () ← hyp
... | Satisfied     | Satisfied      | Continue _ _   = hyp
... | Satisfied     | Violated _     | Satisfied      with () ← hyp
... | Satisfied     | Violated _     | Violated _     = refl
... | Satisfied     | Violated _     | Continue _ _   = hyp
... | Satisfied     | Continue _ _   | Satisfied      = hyp
... | Satisfied     | Continue _ _   | Violated _     = hyp
... | Satisfied     | Continue _ _   | Continue _ _   = hyp
... | Continue _ a' | Satisfied      | Satisfied      = refl
... | Continue _ _  | Satisfied      | Violated _     with () ← hyp
... | Continue _ a' | Satisfied      | Continue _ b₂' =
      sym (runL-and-right-True table a' b₂' rest (sym hyp))
... | Continue _ _  | Violated _     | Satisfied      with () ← hyp
... | Continue _ _  | Violated _     | Violated _     = refl
... | Continue _ a' | Violated _     | Continue _ b₂' =
      sym (runL-and-right-False table a' b₂' rest (sym hyp))
... | Continue _ a' | Continue _ b₁' | Satisfied      =
      runL-and-right-True table a' b₁' rest hyp
... | Continue _ a' | Continue _ b₁' | Violated _     =
      runL-and-right-False table a' b₁' rest hyp
... | Continue _ a' | Continue _ b₁' | Continue _ b₂' =
      runL-and-cong-r table a' b₁' b₂' rest hyp

-- When the right side of Or evaluates to True, Or a b ≡ True.
runL-or-right-True : ∀ table a b σ → runL table b σ ≡ True →
  runL table (Or a b) σ ≡ True
runL-or-right-True table a b [] hyp =
  runL-or-right-True-[] a b (finalizeL a) (finalizeL b) refl refl hyp
runL-or-right-True table a b (x ∷ rest) hyp
  with stepL table a x | stepL table b x
... | Satisfied     | _              = refl
... | Violated _    | Satisfied      = refl
... | Violated _    | Violated _     with () ← hyp
... | Violated _    | Continue _ _   = hyp
... | Continue _ _  | Satisfied      = refl
... | Continue _ _  | Violated _     with () ← hyp
... | Continue _ a' | Continue _ b'  = runL-or-right-True table a' b' rest hyp

-- When the right side of Or evaluates to False, Or a b ≡ a at runL level.
runL-or-right-False : ∀ table a b σ → runL table b σ ≡ False →
  runL table (Or a b) σ ≡ runL table a σ
runL-or-right-False table a b [] hyp =
  runL-or-right-False-[] a b (finalizeL a) (finalizeL b) refl refl hyp
runL-or-right-False table a b (x ∷ rest) hyp
  with stepL table a x | stepL table b x
... | Satisfied     | _              = refl
... | Violated _    | Satisfied      with () ← hyp
... | Violated _    | Violated _     = refl
... | Violated _    | Continue _ _   = hyp
... | Continue _ _  | Satisfied      with () ← hyp
... | Continue _ a' | Violated _     = refl
... | Continue _ a' | Continue _ b'  = runL-or-right-False table a' b' rest hyp

-- Pointwise congruence: if b₁ ≡ b₂ at runL level, Or a b₁ ≡ Or a b₂.
runL-or-cong-r : ∀ table a b₁ b₂ σ →
  runL table b₁ σ ≡ runL table b₂ σ →
  runL table (Or a b₁) σ ≡ runL table (Or a b₂) σ
runL-or-cong-r table a b₁ b₂ [] hyp =
  runL-or-cong-r-[] a b₁ b₂ (finalizeL a) (finalizeL b₁) (finalizeL b₂)
    refl refl refl hyp
runL-or-cong-r table a b₁ b₂ (x ∷ rest) hyp
  with stepL table a x | stepL table b₁ x | stepL table b₂ x
... | Satisfied     | _              | _              = refl
... | Violated _    | Satisfied      | Satisfied      = refl
... | Violated _    | Satisfied      | Violated _     with () ← hyp
... | Violated _    | Satisfied      | Continue _ _   = hyp
... | Violated _    | Violated _     | Satisfied      with () ← hyp
... | Violated _    | Violated _     | Violated _     = refl
... | Violated _    | Violated _     | Continue _ _   = hyp
... | Violated _    | Continue _ _   | Satisfied      = hyp
... | Violated _    | Continue _ _   | Violated _     = hyp
... | Violated _    | Continue _ _   | Continue _ _   = hyp
... | Continue _ a' | Satisfied      | Satisfied      = refl
... | Continue _ _  | Satisfied      | Violated _     with () ← hyp
... | Continue _ a' | Satisfied      | Continue _ b₂' =
      sym (runL-or-right-True table a' b₂' rest (sym hyp))
... | Continue _ _  | Violated _     | Satisfied      with () ← hyp
... | Continue _ _  | Violated _     | Violated _     = refl
... | Continue _ a' | Violated _     | Continue _ b₂' =
      sym (runL-or-right-False table a' b₂' rest (sym hyp))
... | Continue _ a' | Continue _ b₁' | Satisfied      =
      runL-or-right-True table a' b₁' rest hyp
... | Continue _ a' | Continue _ b₁' | Violated _     =
      runL-or-right-False table a' b₁' rest hyp
... | Continue _ a' | Continue _ b₁' | Continue _ b₂' =
      runL-or-cong-r table a' b₁' b₂' rest hyp
