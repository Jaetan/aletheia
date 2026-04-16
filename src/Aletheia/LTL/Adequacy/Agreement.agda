{-# OPTIONS --safe --without-K #-}

-- Two-valued agreement: full LTLf completeness for definite predicates.
--
-- Main theorem:
--   agreement : TwoValued table → runL table proc σ ≡ ⟦ denot table proc ⟧ σ
--
-- When all atomic predicates return True or False (never Unknown/Pending),
-- the operational coalgebra (runL) and denotational semantics (⟦_⟧) give
-- the same TruthVal — propositional equality, not just Sound.
--
-- Status / role in the production pipeline
-- -----------------------------------------
-- This theorem is **conditional**: it requires `TwoValued table`, i.e. every
-- `table n frame` returns `True` or `False` for every `n` and every `frame`.
-- On the table produced by `mkPredTable dbc cache atoms`, that precondition
-- does **not** hold universally — indices ≥ `length atoms` fall through to
-- the `Unknown` branch (see Property 27 in `FrameProcessor/Properties.agda`
-- showing that path is dead code for reachable indices, but the table is
-- still not two-valued as a mathematical function).
--
-- The production monitor therefore relies on two related but distinct
-- guarantees depending on phase:
--
--   * Cold start (first frame before any signal has been cached):
--     `adequacy : Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)`
--     (four-valued, from `Aletheia.LTL.Adequacy`). No precondition. The
--     monitor may legitimately return `Unknown`/`Pending`; soundness just
--     guarantees it never *lies* — a definite verdict matches the textbook
--     semantics.
--
--   * Steady state (all atom signals warmed in the cache):
--     `warm-cache-agreement` (from `Aletheia.Protocol.Adequacy.WarmCache`) —
--     composes `evalPredicate-cache-definite` (cache-warmness bridge) with
--     `agreement-bounded` (the AllBelow variant of this theorem). Warm
--     cache + `AllBelow b proc` is what `mkPredTable`'s table actually
--     satisfies; use that, not this module's unbounded `agreement`.
--
-- So the raw `agreement : TwoValued table → …` below is the abstract
-- mathematical fact; clients should normally call `warm-cache-agreement`
-- instead. `agreement` remains public for callers that independently
-- construct a two-valued table (e.g. test oracles, spec formalisations).
--
-- Proof strategy: mirrors adequacy's induction, using cong₂/trans/sym on the
-- existing decomposition lemmas instead of Sound compositionality.
-- Metric helpers extracted as non-recursive functions for termination.
-- Key technique: `rewrite sym ih-*` + Kleene identity lemmas (`∨TV-false-l`,
-- `∧TV-true-l`, …) bridge stuck `⟦_⟧ ∧TV ⟦_⟧` terms; `cong₂` applications use
-- real equalities on both arms (never `cong₂ f refl _`, which leaves
-- metavariables Agda cannot solve — see `feedback_overlapping_kleene_rewrite`).
module Aletheia.LTL.Adequacy.Agreement where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (subst; cong₂)

import Aletheia.LTL.Syntax as Syntax
open Syntax using (LTL; decodeStart)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending;
  notTV; _∧TV_; _∨TV_)
open import Aletheia.LTL.TruthVal.Properties using
  (∨TV-false-l; ∨TV-false-r; ∧TV-false-l; ∧TV-true-l; ∧TV-true-r)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; denot; metricElapsed)
open import Aletheia.LTL.Syntax using
  (Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
   MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Incremental using (Continue; Violated; Satisfied)
open import Aletheia.LTL.Semantics using (⟦_⟧; met-ev-go; met-al-go; met-un-go; met-re-go)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp; timestampℕ)
open import Aletheia.LTL.Adequacy using (runL;
  runL-and-decomp; runL-or-decomp; runL-not-decomp;
  runL-always-decomp; runL-eventually-decomp; runL-until-decomp; runL-release-decomp)

-- ============================================================================
-- TWO-VALUEDNESS PREDICATE
-- ============================================================================

TwoValued : PredTable → Set
TwoValued table = ∀ n f → (table n f ≡ True) ⊎ (table n f ≡ False)

-- ============================================================================
-- METRIC GO-DENOT BRIDGE LEMMAS
-- ============================================================================
--
-- Non-private so that the bounded-agreement variant in
-- `Aletheia.Protocol.Adequacy.WarmCache` can reuse them without duplication.

met-ev-go-denot : ∀ w (φ : LTL (TimedFrame → TruthVal)) start σ
  → met-ev-go w φ start σ ≡ ⟦ Syntax.MetricEventually w (suc start) φ ⟧ σ
met-ev-go-denot w φ start [] = refl
met-ev-go-denot w φ start (_ ∷ _) = refl

met-al-go-denot : ∀ w (φ : LTL (TimedFrame → TruthVal)) start σ
  → met-al-go w φ start σ ≡ ⟦ Syntax.MetricAlways w (suc start) φ ⟧ σ
met-al-go-denot w φ start [] = refl
met-al-go-denot w φ start (_ ∷ _) = refl

met-un-go-denot : ∀ w (φ ψ : LTL (TimedFrame → TruthVal)) start σ
  → met-un-go w φ ψ start σ ≡ ⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ σ
met-un-go-denot w φ ψ start [] = refl
met-un-go-denot w φ ψ start (_ ∷ _) = refl

met-re-go-denot : ∀ w (φ ψ : LTL (TimedFrame → TruthVal)) start σ
  → met-re-go w φ ψ start σ ≡ ⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ σ
met-re-go-denot w φ ψ start [] = refl
met-re-go-denot w φ ψ start (_ ∷ _) = refl

-- ============================================================================
-- METRIC AGREEMENT HELPERS (non-recursive, extracted for termination)
-- ============================================================================

-- Each helper handles the boolean window guard + stepL case split.
-- Composes equalities via `rewrite sym ih-*` + Kleene identity lemmas
-- (`∨TV-false-l`, `∧TV-true-l`, …); every `cong₂` takes real equalities on
-- both arms (never `cong₂ f refl _`, which leaves metavariables Agda cannot
-- solve — see `feedback_overlapping_kleene_rewrite`).
-- This avoids lambdas with captured variables that block ∧TV/∨TV reduction.
--
-- Non-private so that the bounded-agreement variant in
-- `Aletheia.Protocol.Adequacy.WarmCache` can reuse them without duplication — these
-- helpers are parameterized on IH equalities and do not mention `TwoValued`,
-- so they are generic in the shape of the top-level agreement induction.

-- MetricEventually: ∨-decomposition, False on window expiry.
agree-met-ev : ∀ (table : PredTable) w s (φ : LTLProc) y rest
  → runL table φ (y ∷ rest) ≡ ⟦ denot table φ ⟧ (y ∷ rest)
  → runL table (MetricEventually w (suc (decodeStart s (timestampℕ y))) φ) rest
    ≡ met-ev-go w (denot table φ) (decodeStart s (timestampℕ y)) rest
  → runL table (MetricEventually w s φ) (y ∷ rest)
    ≡ ⟦ denot table (MetricEventually w s φ) ⟧ (y ∷ rest)
agree-met-ev table w s φ y rest ih-φ ih-rest
  with metricElapsed s y ≤ᵇ w
... | false = refl
... | true with stepL table φ y
...   | Satisfied  rewrite sym ih-φ = refl                           -- True ∨TV _ = True (def'l)
...   | Violated _ rewrite sym ih-φ =                                -- False ∨TV m via ∨TV-false-l
        trans ih-rest (sym (∨TV-false-l _))
...   | Continue _ φ' =
        trans (runL-or-decomp table φ' (MetricEventually w (suc (decodeStart s (timestampℕ y))) φ) rest)
              (cong₂ _∨TV_ ih-φ ih-rest)

-- MetricAlways: ∧-decomposition, True on window expiry.
agree-met-al : ∀ (table : PredTable) w s (φ : LTLProc) y rest
  → runL table φ (y ∷ rest) ≡ ⟦ denot table φ ⟧ (y ∷ rest)
  → runL table (MetricAlways w (suc (decodeStart s (timestampℕ y))) φ) rest
    ≡ met-al-go w (denot table φ) (decodeStart s (timestampℕ y)) rest
  → runL table (MetricAlways w s φ) (y ∷ rest)
    ≡ ⟦ denot table (MetricAlways w s φ) ⟧ (y ∷ rest)
agree-met-al table w s φ y rest ih-φ ih-rest
  with metricElapsed s y ≤ᵇ w
... | false = refl
... | true with stepL table φ y
...   | Satisfied  rewrite sym ih-φ =                                -- True ∧TV m via ∧TV-true-l
        trans ih-rest (sym (∧TV-true-l _))
...   | Violated _ rewrite sym ih-φ = refl                           -- False ∧TV _ = False (def'l)
...   | Continue _ φ' =
        trans (runL-and-decomp table φ' (MetricAlways w (suc (decodeStart s (timestampℕ y))) φ) rest)
              (cong₂ _∧TV_ ih-φ ih-rest)

-- MetricUntil: ψ ∨ (φ ∧ MUP), False on window expiry.
agree-met-un : ∀ (table : PredTable) w s (φ ψ : LTLProc) y rest
  → runL table φ (y ∷ rest) ≡ ⟦ denot table φ ⟧ (y ∷ rest)
  → runL table ψ (y ∷ rest) ≡ ⟦ denot table ψ ⟧ (y ∷ rest)
  → runL table (MetricUntil w (suc (decodeStart s (timestampℕ y))) φ ψ) rest
    ≡ met-un-go w (denot table φ) (denot table ψ) (decodeStart s (timestampℕ y)) rest
  → runL table (MetricUntil w s φ ψ) (y ∷ rest)
    ≡ ⟦ denot table (MetricUntil w s φ ψ) ⟧ (y ∷ rest)
agree-met-un table w s φ ψ y rest ih-φ ih-ψ ih-rest
  with metricElapsed s y ≤ᵇ w
... | false = refl
... | true with stepL table ψ y | stepL table φ y
...   | Satisfied    | _                                             -- True ∨TV _ = True (def'l)
        rewrite sym ih-ψ = refl
...   | Violated _   | Satisfied                                     -- False∨(True∧m)
        rewrite sym ih-ψ | sym ih-φ =
        trans ih-rest (trans (sym (∧TV-true-l _)) (sym (∨TV-false-l _)))
...   | Violated _   | Violated _                                    -- False∨(False∧m)=False
        rewrite sym ih-ψ | sym ih-φ = refl
...   | Violated _   | Continue _ φ'                                 -- False∨(φ★∧m) via ∨TV-false-l
        rewrite sym ih-ψ =
        let mup = MetricUntil w (suc (decodeStart s (timestampℕ y))) φ ψ
        in trans (trans (runL-and-decomp table φ' mup rest) (cong₂ _∧TV_ ih-φ ih-rest))
                 (sym (∨TV-false-l _))
...   | Continue _ ψ' | Satisfied                                    -- ψ★∨(True∧m) via ∧TV-true-l
        rewrite sym ih-φ =
        let mup = MetricUntil w (suc (decodeStart s (timestampℕ y))) φ ψ
        in trans (runL-or-decomp table ψ' mup rest)
                 (cong₂ _∨TV_ ih-ψ (trans ih-rest (sym (∧TV-true-l _))))
...   | Continue _ ψ' | Violated _                                   -- ψ★∨(False∧m)=ψ★∨False
        rewrite sym ih-φ =
        trans ih-ψ (sym (∨TV-false-r _))
...   | Continue _ ψ' | Continue _ φ' =
        let mup = MetricUntil w (suc (decodeStart s (timestampℕ y))) φ ψ
        in trans (runL-or-decomp table ψ' (And φ' mup) rest)
                 (cong₂ _∨TV_ ih-ψ (trans (runL-and-decomp table φ' mup rest)
                                           (cong₂ _∧TV_ ih-φ ih-rest)))

-- MetricRelease: ψ ∧ (φ ∨ MRP), True on window expiry.
agree-met-re : ∀ (table : PredTable) w s (φ ψ : LTLProc) y rest
  → runL table φ (y ∷ rest) ≡ ⟦ denot table φ ⟧ (y ∷ rest)
  → runL table ψ (y ∷ rest) ≡ ⟦ denot table ψ ⟧ (y ∷ rest)
  → runL table (MetricRelease w (suc (decodeStart s (timestampℕ y))) φ ψ) rest
    ≡ met-re-go w (denot table φ) (denot table ψ) (decodeStart s (timestampℕ y)) rest
  → runL table (MetricRelease w s φ ψ) (y ∷ rest)
    ≡ ⟦ denot table (MetricRelease w s φ ψ) ⟧ (y ∷ rest)
agree-met-re table w s φ ψ y rest ih-φ ih-ψ ih-rest
  with metricElapsed s y ≤ᵇ w
... | false = refl
... | true with stepL table ψ y | stepL table φ y
...   | Violated _   | _                                             -- False ∧TV _ = False (def'l)
        rewrite sym ih-ψ = refl
...   | Satisfied    | Satisfied                                     -- True∧(True∨m)=True∧True=True
        rewrite sym ih-ψ | sym ih-φ = refl
...   | Satisfied    | Violated _                                    -- True∧(False∨m)
        rewrite sym ih-ψ | sym ih-φ =
        trans ih-rest (trans (sym (∨TV-false-l _)) (sym (∧TV-true-l _)))
...   | Satisfied    | Continue _ φ'                                 -- True∧(φ★∨m) via ∧TV-true-l
        rewrite sym ih-ψ =
        let mrp = MetricRelease w (suc (decodeStart s (timestampℕ y))) φ ψ
        in trans (trans (runL-or-decomp table φ' mrp rest) (cong₂ _∨TV_ ih-φ ih-rest))
                 (sym (∧TV-true-l _))
...   | Continue _ ψ' | Satisfied                                    -- ψ★∧(True∨m)=ψ★∧True
        rewrite sym ih-φ =
        trans ih-ψ (sym (∧TV-true-r _))
...   | Continue _ ψ' | Violated _                                   -- ψ★∧(False∨m) via ∨TV-false-l
        rewrite sym ih-φ =
        let mrp = MetricRelease w (suc (decodeStart s (timestampℕ y))) φ ψ
        in trans (runL-and-decomp table ψ' mrp rest)
                 (cong₂ _∧TV_ ih-ψ (trans ih-rest (sym (∨TV-false-l _))))
...   | Continue _ ψ' | Continue _ φ' =
        let mrp = MetricRelease w (suc (decodeStart s (timestampℕ y))) φ ψ
        in trans (runL-and-decomp table ψ' (Or φ' mrp) rest)
                 (cong₂ _∧TV_ ih-ψ (trans (runL-or-decomp table φ' mrp rest)
                                           (cong₂ _∨TV_ ih-φ ih-rest)))

-- ============================================================================
-- AGREEMENT THEOREM
-- ============================================================================

agreement : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → TwoValued table
  → runL table proc σ ≡ ⟦ denot table proc ⟧ σ

agreement table (Atomic n) [] tv = refl

agreement table (Atomic n) (x ∷ rest) tv with table n x | tv n x
... | .True  | inj₁ refl = refl
... | .False | inj₂ refl = refl

agreement table (And φ ψ) σ tv
  rewrite runL-and-decomp table φ ψ σ
  = cong₂ _∧TV_ (agreement table φ σ tv) (agreement table ψ σ tv)

agreement table (Or φ ψ) σ tv
  rewrite runL-or-decomp table φ ψ σ
  = cong₂ _∨TV_ (agreement table φ σ tv) (agreement table ψ σ tv)

agreement table (Not φ) σ tv
  rewrite runL-not-decomp table φ σ
  = cong notTV (agreement table φ σ tv)

agreement table (Next φ) [] tv = refl
agreement table (Next φ) (x ∷ rest) tv = agreement table φ rest tv

agreement table (WNext φ) [] tv = refl
agreement table (WNext φ) (x ∷ rest) tv = agreement table φ rest tv

agreement table (Always φ) [] tv = refl
agreement table (Always φ) (x ∷ rest) tv =
  subst (_≡ ⟦ denot table φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Always (denot table φ) ⟧ rest)
        (sym (runL-always-decomp table φ x rest))
        (cong₂ _∧TV_ (agreement table φ (x ∷ rest) tv) (agreement table (Always φ) rest tv))

agreement table (Eventually φ) [] tv = refl
agreement table (Eventually φ) (x ∷ rest) tv =
  subst (_≡ ⟦ denot table φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Eventually (denot table φ) ⟧ rest)
        (sym (runL-eventually-decomp table φ x rest))
        (cong₂ _∨TV_ (agreement table φ (x ∷ rest) tv) (agreement table (Eventually φ) rest tv))

agreement table (Until φ ψ) [] tv = refl
agreement table (Until φ ψ) (x ∷ rest) tv =
  subst (_≡ ⟦ denot table ψ ⟧ (x ∷ rest)
              ∨TV (⟦ denot table φ ⟧ (x ∷ rest)
                   ∧TV ⟦ Syntax.Until (denot table φ) (denot table ψ) ⟧ rest))
        (sym (runL-until-decomp table φ ψ x rest))
        (cong₂ _∨TV_ (agreement table ψ (x ∷ rest) tv)
                      (cong₂ _∧TV_ (agreement table φ (x ∷ rest) tv)
                                    (agreement table (Until φ ψ) rest tv)))

agreement table (Release φ ψ) [] tv = refl
agreement table (Release φ ψ) (x ∷ rest) tv =
  subst (_≡ ⟦ denot table ψ ⟧ (x ∷ rest)
              ∧TV (⟦ denot table φ ⟧ (x ∷ rest)
                   ∨TV ⟦ Syntax.Release (denot table φ) (denot table ψ) ⟧ rest))
        (sym (runL-release-decomp table φ ψ x rest))
        (cong₂ _∧TV_ (agreement table ψ (x ∷ rest) tv)
                      (cong₂ _∨TV_ (agreement table φ (x ∷ rest) tv)
                                    (agreement table (Release φ ψ) rest tv)))

agreement table (MetricEventually w s φ) [] tv = refl
agreement table (MetricEventually w s φ) (y ∷ rest) tv =
  agree-met-ev table w s φ y rest
    (agreement table φ (y ∷ rest) tv)
    (trans (agreement table (MetricEventually w (suc (decodeStart s (timestampℕ y))) φ) rest tv)
           (sym (met-ev-go-denot w (denot table φ) (decodeStart s (timestampℕ y)) rest)))

agreement table (MetricAlways w s φ) [] tv = refl
agreement table (MetricAlways w s φ) (y ∷ rest) tv =
  agree-met-al table w s φ y rest
    (agreement table φ (y ∷ rest) tv)
    (trans (agreement table (MetricAlways w (suc (decodeStart s (timestampℕ y))) φ) rest tv)
           (sym (met-al-go-denot w (denot table φ) (decodeStart s (timestampℕ y)) rest)))

agreement table (MetricUntil w s φ ψ) [] tv = refl
agreement table (MetricUntil w s φ ψ) (y ∷ rest) tv =
  agree-met-un table w s φ ψ y rest
    (agreement table φ (y ∷ rest) tv)
    (agreement table ψ (y ∷ rest) tv)
    (trans (agreement table (MetricUntil w (suc (decodeStart s (timestampℕ y))) φ ψ) rest tv)
           (sym (met-un-go-denot w (denot table φ) (denot table ψ) (decodeStart s (timestampℕ y)) rest)))

agreement table (MetricRelease w s φ ψ) [] tv = refl
agreement table (MetricRelease w s φ ψ) (y ∷ rest) tv =
  agree-met-re table w s φ ψ y rest
    (agreement table φ (y ∷ rest) tv)
    (agreement table ψ (y ∷ rest) tv)
    (trans (agreement table (MetricRelease w (suc (decodeStart s (timestampℕ y))) φ ψ) rest tv)
           (sym (met-re-go-denot w (denot table φ) (denot table ψ) (decodeStart s (timestampℕ y)) rest)))
