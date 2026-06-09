-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Reference MTL semantics and equivalence with ⟦_⟧ under monotonicity.
--
-- Purpose: Define a non-short-circuiting MTL semantics (⟦_⟧ₘ) and prove
-- that our production denotational semantics ⟦_⟧ agrees with it on
-- monotonic traces. Combined with the existing adequacy theorem
-- (stepL = ⟦_⟧), this gives: stepL = standard MTL on monotonic traces.
--
-- Key insight: ⟦_⟧ short-circuits metric operators past the time window
-- (returning False/True immediately). Under monotonicity, all future
-- frames are also past the window, so the short-circuit is sound.
-- ⟦_⟧ₘ does NOT short-circuit — it continues scanning, producing the
-- identity element (False for ∨, True for ∧) for past-window frames.
--
-- Structure:
--   1. Reference metric go helpers (non-short-circuiting)
--   2. Reference MTL semantics ⟦_⟧ₘ
--   3. Monotonicity helper lemmas
--   4. Equivalence: Monotonic σ → ⟦ φ ⟧ σ ≡ ⟦ φ ⟧ₘ σ
module Aletheia.LTL.Semantics.MTL where

open import Data.Nat using (ℕ; _∸_; _≤_; _≤ᵇ_; _<_)
open import Data.Nat.Properties using (≤-trans; ∸-monoˡ-≤; ≤⇒≤ᵇ; ≤ᵇ⇒≤; ≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Bool using (true; false; T)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)

open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; WNext; Always; Eventually;
  Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease; decodeStart)
open import Aletheia.LTL.SignalPredicate using (TruthVal; notTV; _∧TV_; _∨TV_)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestampℕ; tsValue; Monotonic)
open import Aletheia.LTL.Semantics using (⟦_⟧; met-ev-go; met-al-go; met-un-go; met-re-go)
open import Aletheia.Prelude using (T→true)

open TruthVal

-- ============================================================================
-- REFERENCE MTL SEMANTICS (non-short-circuiting)
-- ============================================================================

-- The reference semantics ⟦_⟧ₘ is identical to ⟦_⟧ for all non-metric
-- operators. For metric operators, the go helpers do NOT short-circuit
-- when past the window — they continue scanning, contributing the
-- identity element (False for ∨-based, True for ∧-based operators).

⟦_⟧ₘ : LTL (TimedFrame → TruthVal) → List TimedFrame → TruthVal
met-ev-ref : ℕ → LTL (TimedFrame → TruthVal) → ℕ → List TimedFrame → TruthVal
met-al-ref : ℕ → LTL (TimedFrame → TruthVal) → ℕ → List TimedFrame → TruthVal
met-un-ref : ℕ → LTL (TimedFrame → TruthVal) → LTL (TimedFrame → TruthVal) → ℕ → List TimedFrame → TruthVal
met-re-ref : ℕ → LTL (TimedFrame → TruthVal) → LTL (TimedFrame → TruthVal) → ℕ → List TimedFrame → TruthVal

-- Propositional operators — identical to ⟦_⟧
-- Atomic on empty suffix: Unknown (Kleene three-valued — matches ⟦_⟧).
-- Previously False; changed under Path G so the equivalence
-- mtl-equiv : ⟦ φ ⟧ σ ≡ ⟦ φ ⟧ₘ σ continues to hold on Atomic [].
⟦ Atomic p ⟧ₘ []          = Unknown
⟦ Atomic p ⟧ₘ (x ∷ _)    = p x
⟦ Not φ ⟧ₘ σ              = notTV (⟦ φ ⟧ₘ σ)
⟦ And φ ψ ⟧ₘ σ            = ⟦ φ ⟧ₘ σ ∧TV ⟦ ψ ⟧ₘ σ
⟦ Or φ ψ ⟧ₘ σ             = ⟦ φ ⟧ₘ σ ∨TV ⟦ ψ ⟧ₘ σ
⟦ Next φ ⟧ₘ []            = False
⟦ Next φ ⟧ₘ (_ ∷ rest)    = ⟦ φ ⟧ₘ rest
⟦ WNext φ ⟧ₘ []           = True
⟦ WNext φ ⟧ₘ (_ ∷ rest)   = ⟦ φ ⟧ₘ rest

-- Unbounded temporal — identical to ⟦_⟧
⟦ Always φ ⟧ₘ []          = True
⟦ Always φ ⟧ₘ (x ∷ rest)  = ⟦ φ ⟧ₘ (x ∷ rest) ∧TV ⟦ Always φ ⟧ₘ rest
⟦ Eventually φ ⟧ₘ []          = False
⟦ Eventually φ ⟧ₘ (x ∷ rest)  = ⟦ φ ⟧ₘ (x ∷ rest) ∨TV ⟦ Eventually φ ⟧ₘ rest
⟦ Until φ ψ ⟧ₘ []          = False
⟦ Until φ ψ ⟧ₘ (x ∷ rest)  = ⟦ ψ ⟧ₘ (x ∷ rest) ∨TV (⟦ φ ⟧ₘ (x ∷ rest) ∧TV ⟦ Until φ ψ ⟧ₘ rest)
⟦ Release φ ψ ⟧ₘ []          = True
⟦ Release φ ψ ⟧ₘ (x ∷ rest)  = ⟦ ψ ⟧ₘ (x ∷ rest) ∧TV (⟦ φ ⟧ₘ (x ∷ rest) ∨TV ⟦ Release φ ψ ⟧ₘ rest)

-- Metric operators — delegate to NON-short-circuiting go helpers
⟦ MetricEventually w s φ ⟧ₘ [] = False
⟦ MetricEventually w s φ ⟧ₘ σ@(y ∷ _) = met-ev-ref (tsValue w) φ (decodeStart s (timestampℕ y)) σ
⟦ MetricAlways w s φ ⟧ₘ [] = True
⟦ MetricAlways w s φ ⟧ₘ σ@(y ∷ _) = met-al-ref (tsValue w) φ (decodeStart s (timestampℕ y)) σ
⟦ MetricUntil w s φ ψ ⟧ₘ [] = False
⟦ MetricUntil w s φ ψ ⟧ₘ σ@(y ∷ _) = met-un-ref (tsValue w) φ ψ (decodeStart s (timestampℕ y)) σ
⟦ MetricRelease w s φ ψ ⟧ₘ [] = True
⟦ MetricRelease w s φ ψ ⟧ₘ σ@(y ∷ _) = met-re-ref (tsValue w) φ ψ (decodeStart s (timestampℕ y)) σ

-- Reference MetricEventually: no short-circuit, identity element False for ∨
met-ev-ref w φ start [] = False
met-ev-ref w φ start (y ∷ rest) with (timestampℕ y ∸ start) ≤ᵇ w
... | true  = ⟦ φ ⟧ₘ (y ∷ rest) ∨TV met-ev-ref w φ start rest
... | false = met-ev-ref w φ start rest  -- continue scanning (vs ⟦_⟧ which returns False)

-- Reference MetricAlways: no short-circuit, identity element True for ∧
met-al-ref w φ start [] = True
met-al-ref w φ start (y ∷ rest) with (timestampℕ y ∸ start) ≤ᵇ w
... | true  = ⟦ φ ⟧ₘ (y ∷ rest) ∧TV met-al-ref w φ start rest
... | false = met-al-ref w φ start rest  -- continue scanning (vs ⟦_⟧ which returns True)

-- Reference MetricUntil: no short-circuit
met-un-ref w φ ψ start [] = False
met-un-ref w φ ψ start (y ∷ rest) with (timestampℕ y ∸ start) ≤ᵇ w
... | true  = ⟦ ψ ⟧ₘ (y ∷ rest) ∨TV (⟦ φ ⟧ₘ (y ∷ rest) ∧TV met-un-ref w φ ψ start rest)
... | false = met-un-ref w φ ψ start rest

-- Reference MetricRelease: no short-circuit
met-re-ref w φ ψ start [] = True
met-re-ref w φ ψ start (y ∷ rest) with (timestampℕ y ∸ start) ≤ᵇ w
... | true  = ⟦ ψ ⟧ₘ (y ∷ rest) ∧TV (⟦ φ ⟧ₘ (y ∷ rest) ∨TV met-re-ref w φ ψ start rest)
... | false = met-re-ref w φ ψ start rest

-- ============================================================================
-- MONOTONICITY LEMMAS
-- ============================================================================

-- Core lemma: in a monotonic trace, once past the window, always past.
-- If (timestampℕ y ∸ start) > w and timestamps are non-decreasing,
-- then every z after y also has (timestampℕ z ∸ start) > w.

-- Key: if a ≤ b and ((a ∸ c) ≤ᵇ w) ≡ false, then ((b ∸ c) ≤ᵇ w) ≡ false.
-- (Larger timestamp ⇒ larger elapsed time ⇒ still past window)
past-window-mono : ∀ {a b c w} → a ≤ b
  → ((a ∸ c) ≤ᵇ w) ≡ false
  → ((b ∸ c) ≤ᵇ w) ≡ false
past-window-mono {a} {b} {c} {w} a≤b eq
  with (b ∸ c) ≤ᵇ w in h
... | false = refl
... | true  with () ← subst (λ x → x ≡ false) (T→true (≤⇒≤ᵇ (≤-trans (∸-monoˡ-≤ c a≤b) (≤ᵇ⇒≤ _ _ (subst T (sym h) tt))))) eq

-- ============================================================================
-- PAST-WINDOW STABILITY FOR REFERENCE GO HELPERS
-- ============================================================================

-- When all frames are past the window, reference go helpers return their
-- identity element (False for ∨-based, True for ∧-based).

-- When a frame y is past the window in a monotonic trace, met-ev-ref on
-- the remaining trace returns False (no future frame can be in-window).
met-ev-ref-past : ∀ w φ start y rest → Monotonic (y ∷ rest)
  → ((timestampℕ y ∸ start) ≤ᵇ w) ≡ false
  → met-ev-ref w φ start rest ≡ False
met-ev-ref-past w φ start y [] _ _ = refl
met-ev-ref-past w φ start y (z ∷ rest) (y≤z , mzr) pw
  with past-window-mono {timestampℕ y} {timestampℕ z} {start} {w} y≤z pw
... | zpw rewrite zpw = met-ev-ref-past w φ start z rest mzr zpw

met-al-ref-past : ∀ w φ start y rest → Monotonic (y ∷ rest)
  → ((timestampℕ y ∸ start) ≤ᵇ w) ≡ false
  → met-al-ref w φ start rest ≡ True
met-al-ref-past w φ start y [] _ _ = refl
met-al-ref-past w φ start y (z ∷ rest) (y≤z , mzr) pw
  with past-window-mono {timestampℕ y} {timestampℕ z} {start} {w} y≤z pw
... | zpw rewrite zpw = met-al-ref-past w φ start z rest mzr zpw

met-un-ref-past : ∀ w φ ψ start y rest → Monotonic (y ∷ rest)
  → ((timestampℕ y ∸ start) ≤ᵇ w) ≡ false
  → met-un-ref w φ ψ start rest ≡ False
met-un-ref-past w φ ψ start y [] _ _ = refl
met-un-ref-past w φ ψ start y (z ∷ rest) (y≤z , mzr) pw
  with past-window-mono {timestampℕ y} {timestampℕ z} {start} {w} y≤z pw
... | zpw rewrite zpw = met-un-ref-past w φ ψ start z rest mzr zpw

met-re-ref-past : ∀ w φ ψ start y rest → Monotonic (y ∷ rest)
  → ((timestampℕ y ∸ start) ≤ᵇ w) ≡ false
  → met-re-ref w φ ψ start rest ≡ True
met-re-ref-past w φ ψ start y [] _ _ = refl
met-re-ref-past w φ ψ start y (z ∷ rest) (y≤z , mzr) pw
  with past-window-mono {timestampℕ y} {timestampℕ z} {start} {w} y≤z pw
... | zpw rewrite zpw = met-re-ref-past w φ ψ start z rest mzr zpw

-- ============================================================================
-- EQUIVALENCE: ⟦_⟧ ≡ ⟦_⟧ₘ under monotonicity
-- ============================================================================

-- Main theorem: on monotonic traces, the short-circuiting semantics ⟦_⟧
-- agrees with the reference MTL semantics ⟦_⟧ₘ.
-- Proof structure:
--   1. met-*-equiv: list-recursive proofs for each metric go helper (non-mutual)
--   2. mtl-equiv: formula-recursive main theorem, delegates to met-*-equiv
-- Each met-*-equiv is defined completely (not forward-declared), so the
-- termination checker verifies each independently — avoiding the known
-- issue where `with ... in h` adds call-matrix columns that prevent
-- termination checking in mutual blocks.

-- FormulaIH: the equivalence holds for a given subformula on all monotonic traces.
-- Passed explicitly to the metric go proofs to break the dependency on mtl-equiv.
FormulaIH : LTL (TimedFrame → TruthVal) → Set
FormulaIH φ = ∀ σ → Monotonic σ → ⟦ φ ⟧ σ ≡ ⟦ φ ⟧ₘ σ

FormulaIH₂ : LTL (TimedFrame → TruthVal) → LTL (TimedFrame → TruthVal) → Set
FormulaIH₂ φ ψ = FormulaIH φ × FormulaIH ψ

-- Metric go helper equivalences (list-recursive only).
-- Well-founded recursion on list length is needed rather than direct structural
-- recursion on σ because the `with (timestampℕ y ∸ start) ≤ᵇ w in h` pattern
-- adds an extra column to the termination call matrix.  Agda's checker cannot
-- then verify that the recursive call `go (z ∷ rs) …` is structurally smaller
-- on σ, since the `in h` column varies.  Wrapping with Acc _<_ (length σ)
-- makes the decrease explicit: `acc rec → rec ≤-refl`.

met-ev-equiv : ∀ w φ start σ → Monotonic σ → FormulaIH φ
  → met-ev-go w φ start σ ≡ met-ev-ref w φ start σ
met-ev-equiv w φ start σ mono ih = go σ (<-wellFounded (length σ)) mono ih
  where
    go : ∀ σ → Acc _<_ (length σ) → Monotonic σ → FormulaIH φ
      → met-ev-go w φ start σ ≡ met-ev-ref w φ start σ
    go [] _ _ _ = refl
    go (y ∷ []) _ mono ih
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    ... | true  = cong (_∨TV False) (ih (y ∷ []) tt)
    ... | false = sym (met-ev-ref-past w φ start y [] mono h)
    go (y ∷ z ∷ rs) wf mono ih
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    go (y ∷ z ∷ rs) (acc rec) mono ih | true =
      cong₂ _∨TV_ (ih (y ∷ z ∷ rs) mono)
        (go (z ∷ rs) (rec ≤-refl) (proj₂ mono) ih)
    go (y ∷ z ∷ rs) wf mono ih | false =
      sym (met-ev-ref-past w φ start y (z ∷ rs) mono h)

met-al-equiv : ∀ w φ start σ → Monotonic σ → FormulaIH φ
  → met-al-go w φ start σ ≡ met-al-ref w φ start σ
met-al-equiv w φ start σ mono ih = go σ (<-wellFounded (length σ)) mono ih
  where
    go : ∀ σ → Acc _<_ (length σ) → Monotonic σ → FormulaIH φ
      → met-al-go w φ start σ ≡ met-al-ref w φ start σ
    go [] _ _ _ = refl
    go (y ∷ []) _ mono ih
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    ... | true  = cong (_∧TV True) (ih (y ∷ []) tt)
    ... | false = sym (met-al-ref-past w φ start y [] mono h)
    go (y ∷ z ∷ rs) wf mono ih
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    go (y ∷ z ∷ rs) (acc rec) mono ih | true =
      cong₂ _∧TV_ (ih (y ∷ z ∷ rs) mono)
        (go (z ∷ rs) (rec ≤-refl) (proj₂ mono) ih)
    go (y ∷ z ∷ rs) wf mono ih | false =
      sym (met-al-ref-past w φ start y (z ∷ rs) mono h)

met-un-equiv : ∀ w φ ψ start σ → Monotonic σ → FormulaIH₂ φ ψ
  → met-un-go w φ ψ start σ ≡ met-un-ref w φ ψ start σ
met-un-equiv w φ ψ start σ mono ih = go σ (<-wellFounded (length σ)) mono ih
  where
    go : ∀ σ → Acc _<_ (length σ) → Monotonic σ → FormulaIH₂ φ ψ
      → met-un-go w φ ψ start σ ≡ met-un-ref w φ ψ start σ
    go [] _ _ _ = refl
    go (y ∷ []) _ mono (ihφ , ihψ)
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    ... | true  = cong₂ _∨TV_ (ihψ (y ∷ []) tt)
                    (cong (_∧TV False) (ihφ (y ∷ []) tt))
    ... | false = sym (met-un-ref-past w φ ψ start y [] mono h)
    go (y ∷ z ∷ rs) wf mono ih@(ihφ , ihψ)
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    go (y ∷ z ∷ rs) (acc rec) mono ih@(ihφ , ihψ) | true =
      cong₂ _∨TV_ (ihψ (y ∷ z ∷ rs) mono)
        (cong₂ _∧TV_ (ihφ (y ∷ z ∷ rs) mono)
          (go (z ∷ rs) (rec ≤-refl) (proj₂ mono) ih))
    go (y ∷ z ∷ rs) wf mono ih@(ihφ , ihψ) | false =
      sym (met-un-ref-past w φ ψ start y (z ∷ rs) mono h)

met-re-equiv : ∀ w φ ψ start σ → Monotonic σ → FormulaIH₂ φ ψ
  → met-re-go w φ ψ start σ ≡ met-re-ref w φ ψ start σ
met-re-equiv w φ ψ start σ mono ih = go σ (<-wellFounded (length σ)) mono ih
  where
    go : ∀ σ → Acc _<_ (length σ) → Monotonic σ → FormulaIH₂ φ ψ
      → met-re-go w φ ψ start σ ≡ met-re-ref w φ ψ start σ
    go [] _ _ _ = refl
    go (y ∷ []) _ mono (ihφ , ihψ)
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    ... | true  = cong₂ _∧TV_ (ihψ (y ∷ []) tt)
                    (cong (_∨TV True) (ihφ (y ∷ []) tt))
    ... | false = sym (met-re-ref-past w φ ψ start y [] mono h)
    go (y ∷ z ∷ rs) wf mono ih@(ihφ , ihψ)
      with (timestampℕ y ∸ start) ≤ᵇ w in h
    go (y ∷ z ∷ rs) (acc rec) mono ih@(ihφ , ihψ) | true =
      cong₂ _∧TV_ (ihψ (y ∷ z ∷ rs) mono)
        (cong₂ _∨TV_ (ihφ (y ∷ z ∷ rs) mono)
          (go (z ∷ rs) (rec ≤-refl) (proj₂ mono) ih))
    go (y ∷ z ∷ rs) wf mono ih@(ihφ , ihψ) | false =
      sym (met-re-ref-past w φ ψ start y (z ∷ rs) mono h)

-- Main theorem (formula-recursive, no `with ... in h` needed)
mtl-equiv : ∀ φ σ → Monotonic σ → ⟦ φ ⟧ σ ≡ ⟦ φ ⟧ₘ σ

-- Propositional: identical
mtl-equiv (Atomic p) [] mono = refl
mtl-equiv (Atomic p) (x ∷ _) mono = refl

mtl-equiv (Not φ) σ mono = cong notTV (mtl-equiv φ σ mono)
mtl-equiv (And φ ψ) σ mono = cong₂ _∧TV_ (mtl-equiv φ σ mono) (mtl-equiv ψ σ mono)
mtl-equiv (Or φ ψ) σ mono = cong₂ _∨TV_ (mtl-equiv φ σ mono) (mtl-equiv ψ σ mono)

-- Next
mtl-equiv (Next φ) [] _ = refl
mtl-equiv (Next φ) (x ∷ []) _ = mtl-equiv φ [] tt
mtl-equiv (Next φ) (x ∷ x₂ ∷ rs) (_ , mr) = mtl-equiv φ (x₂ ∷ rs) mr

-- WNext
mtl-equiv (WNext φ) [] _ = refl
mtl-equiv (WNext φ) (x ∷ []) _ = mtl-equiv φ [] tt
mtl-equiv (WNext φ) (x ∷ x₂ ∷ rs) (_ , mr) = mtl-equiv φ (x₂ ∷ rs) mr

-- Unbounded temporal
mtl-equiv (Always φ) [] _ = refl
mtl-equiv (Always φ) (x ∷ []) _ =
  cong₂ _∧TV_ (mtl-equiv φ (x ∷ []) tt) (mtl-equiv (Always φ) [] tt)
mtl-equiv (Always φ) (x ∷ x₂ ∷ rs) mono =
  cong₂ _∧TV_ (mtl-equiv φ (x ∷ x₂ ∷ rs) mono) (mtl-equiv (Always φ) (x₂ ∷ rs) (proj₂ mono))

mtl-equiv (Eventually φ) [] _ = refl
mtl-equiv (Eventually φ) (x ∷ []) _ =
  cong₂ _∨TV_ (mtl-equiv φ (x ∷ []) tt) (mtl-equiv (Eventually φ) [] tt)
mtl-equiv (Eventually φ) (x ∷ x₂ ∷ rs) mono =
  cong₂ _∨TV_ (mtl-equiv φ (x ∷ x₂ ∷ rs) mono) (mtl-equiv (Eventually φ) (x₂ ∷ rs) (proj₂ mono))

mtl-equiv (Until φ ψ) [] _ = refl
mtl-equiv (Until φ ψ) (x ∷ []) _ =
  cong₂ _∨TV_ (mtl-equiv ψ (x ∷ []) tt)
    (cong₂ _∧TV_ (mtl-equiv φ (x ∷ []) tt) (mtl-equiv (Until φ ψ) [] tt))
mtl-equiv (Until φ ψ) (x ∷ x₂ ∷ rs) mono =
  cong₂ _∨TV_ (mtl-equiv ψ (x ∷ x₂ ∷ rs) mono)
    (cong₂ _∧TV_ (mtl-equiv φ (x ∷ x₂ ∷ rs) mono) (mtl-equiv (Until φ ψ) (x₂ ∷ rs) (proj₂ mono)))

mtl-equiv (Release φ ψ) [] _ = refl
mtl-equiv (Release φ ψ) (x ∷ []) _ =
  cong₂ _∧TV_ (mtl-equiv ψ (x ∷ []) tt)
    (cong₂ _∨TV_ (mtl-equiv φ (x ∷ []) tt) (mtl-equiv (Release φ ψ) [] tt))
mtl-equiv (Release φ ψ) (x ∷ x₂ ∷ rs) mono =
  cong₂ _∧TV_ (mtl-equiv ψ (x ∷ x₂ ∷ rs) mono)
    (cong₂ _∨TV_ (mtl-equiv φ (x ∷ x₂ ∷ rs) mono) (mtl-equiv (Release φ ψ) (x₂ ∷ rs) (proj₂ mono)))

-- Metric operators: delegate to go-helper equivalences, passing formula IH
mtl-equiv (MetricEventually w s φ) [] _ = refl
mtl-equiv (MetricEventually w s φ) (y ∷ rest) mono =
  met-ev-equiv (tsValue w) φ (decodeStart s (timestampℕ y)) (y ∷ rest) mono (mtl-equiv φ)
mtl-equiv (MetricAlways w s φ) [] _ = refl
mtl-equiv (MetricAlways w s φ) (y ∷ rest) mono =
  met-al-equiv (tsValue w) φ (decodeStart s (timestampℕ y)) (y ∷ rest) mono (mtl-equiv φ)
mtl-equiv (MetricUntil w s φ ψ) [] _ = refl
mtl-equiv (MetricUntil w s φ ψ) (y ∷ rest) mono =
  met-un-equiv (tsValue w) φ ψ (decodeStart s (timestampℕ y)) (y ∷ rest) mono (mtl-equiv φ , mtl-equiv ψ)
mtl-equiv (MetricRelease w s φ ψ) [] _ = refl
mtl-equiv (MetricRelease w s φ ψ) (y ∷ rest) mono =
  met-re-equiv (tsValue w) φ ψ (decodeStart s (timestampℕ y)) (y ∷ rest) mono (mtl-equiv φ , mtl-equiv ψ)
