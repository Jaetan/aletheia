{-# OPTIONS --safe --without-K #-}

-- Soundness of Rosu simplification.
--
-- Purpose: Prove that `simplify`/`absorb` from Coalgebra.agda preserve `runL`.
--
-- Main theorem: simplify-runL (simplify preserves runL for all formulas and traces).
-- This enables the pipeline adequacy proof in Adequacy/Pipeline.agda.
--
-- Proof structure:
--   1. ≡ᵇ-proc-correct: Boolean equality on LTLProc reflects propositional equality
--   2. and-idem-runL / or-idem-runL: And a a ≡ a and Or a a ≡ a at runL level
--   3. and-nested-idem-runL / or-nested-idem-runL: And a (And a b) ≡ And a b at runL level
--   4. and-always-nonempty / or-eventually-nonempty: Always/Eventually absorption
--      on non-empty traces
--   5. Finalization agreement + metric non-empty lemmas
--   6. absorb-runL: absorb preserves runL (all rules, all traces)
--   7. simplify-runL: simplify preserves runL (structural induction)

module Aletheia.LTL.SimplifySound where

open import Aletheia.Prelude
open import Data.Bool using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; cong₂)
open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Function.Bundles using (Equivalence)

open import Aletheia.LTL.Coalgebra using (
  LTLProc; PredTable; stepL; finalizeL;
  Atomic; Not; And; Or; Next; Always; Eventually; Until; Release;
  MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc)
open import Aletheia.LTL.Simplify using (finalizesHolds; absorb; simplify; _≡ᵇ-proc_)
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
-- SECTION 5: runL congruence infrastructure
-- ============================================================================

-- When the right side of And evaluates to True, And a b ≡ a at runL level.
runL-and-right-True : ∀ table a b σ → runL table b σ ≡ True →
  runL table (And a b) σ ≡ runL table a σ
runL-and-right-True table a b [] hyp with finalizeL a
... | Fails _ = refl
... | Holds with finalizeL b
...   | Holds   = refl
...   | Fails _ with () ← hyp
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
runL-and-right-False table a b [] hyp with finalizeL a
... | Fails _ = refl
... | Holds with finalizeL b
...   | Holds   with () ← hyp
...   | Fails _ = refl
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
runL-and-cong-r table a b₁ b₂ [] hyp with finalizeL a
... | Fails _ = refl
... | Holds with finalizeL b₁ | finalizeL b₂
...   | Holds   | Holds   = refl
...   | Holds   | Fails _ with () ← hyp
...   | Fails _ | Holds   with () ← hyp
...   | Fails _ | Fails _ = refl
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
runL-or-right-True table a b [] hyp with finalizeL a
... | Holds   = refl
... | Fails _ with finalizeL b
...   | Holds   = refl
...   | Fails _ with () ← hyp
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
runL-or-right-False table a b [] hyp with finalizeL a
... | Holds   = refl
... | Fails _ with finalizeL b
...   | Holds   with () ← hyp
...   | Fails _ = refl
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
runL-or-cong-r table a b₁ b₂ [] hyp with finalizeL a
... | Holds   = refl
... | Fails _ with finalizeL b₁ | finalizeL b₂
...   | Holds   | Holds   = refl
...   | Holds   | Fails _ with () ← hyp
...   | Fails _ | Holds   with () ← hyp
...   | Fails _ | Fails _ = refl
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

-- ============================================================================
-- SECTION 6: absorb preserves runL
-- ============================================================================

private
  -- Always absorption is sound when φ ≡ ψ and finalizesHolds φ.
  always-absorb-sound : ∀ table φ σ →
    finalizesHolds φ ≡ true →
    runL table (Always φ) σ ≡ runL table (And φ (Always φ)) σ
  always-absorb-sound table φ (x ∷ rest) _ =
    sym (and-always-nonempty table φ x rest)
  always-absorb-sound table φ [] fh with finalizeL φ
  ... | Holds   = refl
  ... | Fails _ with () ← fh

  -- Eventually absorption is sound when φ ≡ ψ and ¬ finalizesHolds φ.
  eventually-absorb-sound : ∀ table φ σ →
    finalizesHolds φ ≡ false →
    runL table (Eventually φ) σ ≡ runL table (Or φ (Eventually φ)) σ
  eventually-absorb-sound table φ (x ∷ rest) _ =
    sym (or-eventually-nonempty table φ x rest)
  eventually-absorb-sound table φ [] fh with finalizeL φ
  ... | Holds with () ← fh
  ... | Fails _ = refl

absorb-runL : ∀ table φ σ → runL table (absorb φ) σ ≡ runL table φ σ
-- Always absorption: φ ∧ G(ψ) → G(ψ) when φ ≡ᵇ ψ and finalizesHolds φ
absorb-runL table (And φ (Always ψ)) σ
  with φ ≡ᵇ-proc ψ in beq | finalizesHolds φ in fheq
... | false | _     = refl
... | true  | false = refl
... | true  | true
  with refl ← ≡ᵇ-proc-correct φ ψ (subst T (sym beq) tt)
  = always-absorb-sound table φ σ fheq
-- Eventually absorption: φ ∨ F(ψ) → F(ψ) when φ ≡ᵇ ψ and ¬ finalizesHolds φ
absorb-runL table (Or φ (Eventually ψ)) σ
  with φ ≡ᵇ-proc ψ in beq | finalizesHolds φ in fheq
... | false | _     = refl
... | true  | true  = refl
... | true  | false
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
absorb-runL table (And _ (Eventually _)) σ = refl
absorb-runL table (And _ (Until _ _)) σ = refl
absorb-runL table (And _ (Release _ _)) σ = refl
absorb-runL table (And _ (MetricEventuallyProc _ _ _)) σ = refl
absorb-runL table (And _ (MetricAlwaysProc _ _ _)) σ = refl
absorb-runL table (And _ (MetricUntilProc _ _ _ _)) σ = refl
absorb-runL table (And _ (MetricReleaseProc _ _ _ _)) σ = refl
-- Catch-all: Or with second arg ∉ {Eventually, Or} — absorb returns input
absorb-runL table (Or _ (Atomic _)) σ = refl
absorb-runL table (Or _ (Not _)) σ = refl
absorb-runL table (Or _ (And _ _)) σ = refl
absorb-runL table (Or _ (Next _)) σ = refl
absorb-runL table (Or _ (Always _)) σ = refl
absorb-runL table (Or _ (Until _ _)) σ = refl
absorb-runL table (Or _ (Release _ _)) σ = refl
absorb-runL table (Or _ (MetricEventuallyProc _ _ _)) σ = refl
absorb-runL table (Or _ (MetricAlwaysProc _ _ _)) σ = refl
absorb-runL table (Or _ (MetricUntilProc _ _ _ _)) σ = refl
absorb-runL table (Or _ (MetricReleaseProc _ _ _ _)) σ = refl
-- All other constructors — absorb returns input
absorb-runL table (Atomic _) σ = refl
absorb-runL table (Not _) σ = refl
absorb-runL table (Next _) σ = refl
absorb-runL table (Always _) σ = refl
absorb-runL table (Eventually _) σ = refl
absorb-runL table (Until _ _) σ = refl
absorb-runL table (Release _ _) σ = refl
absorb-runL table (MetricEventuallyProc _ _ _) σ = refl
absorb-runL table (MetricAlwaysProc _ _ _) σ = refl
absorb-runL table (MetricUntilProc _ _ _ _) σ = refl
absorb-runL table (MetricReleaseProc _ _ _ _) σ = refl

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
simplify-runL table (Always _) σ = refl
simplify-runL table (Eventually _) σ = refl
simplify-runL table (Until _ _) σ = refl
simplify-runL table (Release _ _) σ = refl
simplify-runL table (MetricEventuallyProc _ _ _) σ = refl
simplify-runL table (MetricAlwaysProc _ _ _) σ = refl
simplify-runL table (MetricUntilProc _ _ _ _) σ = refl
simplify-runL table (MetricReleaseProc _ _ _ _) σ = refl
