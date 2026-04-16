{-# OPTIONS --safe --without-K #-}

-- Warm-cache agreement: runtime cache ⇒ two-valued agreement theorem.
--
-- Purpose: Bridge a runtime SignalCache populated during streaming to the
-- TwoValued precondition of the `agreement` theorem in
-- `Aletheia.LTL.Adequacy.Agreement`. `agreement` quantifies definiteness
-- universally over atom indices, but `mkPredTable` returns `Unknown` for
-- indices beyond `length atoms` (dead code per Property 27). Warm cache
-- only produces a *bounded* two-valued table; composing with agreement
-- therefore requires a bounded variant that threads an AllBelow hypothesis
-- through every constructor of the LTL induction.
--
-- Exports:
--   AllCached          — warm-cache predicate on an atom list
--   BoundedTwoValued   — two-valuedness restricted to indices < b
--   lookupAtom-warm    — bounded lookup in warm list gives cached predicate
--   warm-cache-table-definite
--                      — mkPredTable definite on bounded indices
--   warm-cache-bounded-twovalued
--                      — bundled: AllCached ⇒ BoundedTwoValued on mkPredTable
--   agreement-bounded  — agreement variant: BoundedTwoValued + AllBelow ⇒ runL ≡ ⟦_⟧
--   warm-cache-agreement
--                      — final composition: warm cache + bounded formula ⇒ runL ≡ ⟦_⟧
--
-- Role: Closes the compositional chain
--   (1) evalPredicate-cache-definite (Evaluation/Properties.agda)
--   (2) lookupAtom-total + mkPredTable-lookup (FrameProcessor/Properties.agda Prop 27)
--   (3) agreement-bounded + warm-cache-agreement (this file)
-- A client that maintains a warm cache and uses a stepped LTL formula
-- (which is AllBelow by construction) plugs directly into the textbook
-- LTLf denotational semantics — no intermediate TwoValued obligation.
--
-- Proof style: The structural cases of `agreement-bounded` mirror `agreement`
-- exactly; the only differences are (a) the Atomic case consults `btv n bp x`
-- instead of `tv n x`, and (b) every recursive call decomposes `bp : AllBelow`
-- for the sub-formula(s). Metric cases delegate to the `agree-met-*` helpers
-- exposed by Agreement.agda, avoiding duplication of boolean-window-guard
-- case analysis.
module Aletheia.Protocol.Adequacy.WarmCache where

open import Aletheia.Prelude
open import Data.Unit using (⊤)
open import Data.Nat using (s≤s)
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst; cong₂)

open import Aletheia.DBC.Types using (DBC)

open import Aletheia.LTL.SignalPredicate using
  (TruthVal; True; False; notTV; _∧TV_; _∨TV_;
   SignalPredicate; SignalCache)
open import Aletheia.LTL.SignalPredicate.Cache using (lookupCache)
open import Aletheia.LTL.SignalPredicate.Evaluation.Properties
  using (signalOf; evalPredicate-cache-definite)

open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; denot)
open import Aletheia.LTL.Syntax using
  (Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
   MetricEventually; MetricAlways; MetricUntil; MetricRelease; decodeStart)
import Aletheia.LTL.Syntax as Syntax
open import Aletheia.LTL.Semantics using (⟦_⟧)
open import Aletheia.LTL.Adequacy using (runL;
  runL-and-decomp; runL-or-decomp; runL-not-decomp;
  runL-always-decomp; runL-eventually-decomp; runL-until-decomp; runL-release-decomp)
open import Aletheia.LTL.Adequacy.Agreement using
  (TwoValued;
   agree-met-ev; agree-met-al; agree-met-un; agree-met-re;
   met-ev-go-denot; met-al-go-denot; met-un-go-denot; met-re-go-denot)

open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp; timestampℕ)
open import Aletheia.Protocol.StreamState.Internals using (lookupAtom; mkPredTable)
open import Aletheia.Protocol.FrameProcessor.Properties using
  (AllBelow; mkPredTable-lookup)

-- ============================================================================
-- WARM CACHE PREDICATE
-- ============================================================================

-- Every predicate in the atom list has its target signal cached.
-- Structural on the atom list — matches the recursion pattern of
-- `lookupAtom` so the bounded-lookup lemma below is a direct zip.
AllCached : SignalCache → List SignalPredicate → Set
AllCached cache []       = ⊤
AllCached cache (p ∷ ps) =
  (∃[ cs ] lookupCache (signalOf p) cache ≡ just cs) × AllCached cache ps

-- Bounded lookup in a warm-cache list yields a cached predicate.
-- Induction on both the atom list and the index, consuming one
-- element of the AllCached pair at each cons.
lookupAtom-warm : ∀ cache atoms k → k < length atoms → AllCached cache atoms →
  ∃[ p ] ∃[ cs ]
    (lookupAtom atoms k ≡ just p × lookupCache (signalOf p) cache ≡ just cs)
lookupAtom-warm cache []       k       () _
lookupAtom-warm cache (p ∷ _)  zero    _        ((cs , hit) , _) = p , cs , refl , hit
lookupAtom-warm cache (_ ∷ ps) (suc k) (s≤s k<) (_ , warm')      =
  lookupAtom-warm cache ps k k< warm'

-- ============================================================================
-- BOUNDED TWO-VALUED PREDICATE
-- ============================================================================

-- Bounded form of TwoValued: definiteness only required for indices below b.
-- Needed because mkPredTable returns `Unknown` for out-of-range indices
-- (dead code per Property 27), so its table is not universally TwoValued —
-- only definite on reachable indices.
BoundedTwoValued : ℕ → PredTable → Set
BoundedTwoValued b table =
  ∀ n → n < b → ∀ f → (table n f ≡ True) ⊎ (table n f ≡ False)

-- Universal TwoValued trivially implies BoundedTwoValued for any bound.
-- Provided as a convenience so clients holding a universal table can still
-- call `agreement-bounded` (passing an AllBelow witness obtained elsewhere).
TwoValued→Bounded : ∀ b table → TwoValued table → BoundedTwoValued b table
TwoValued→Bounded b table tv n _ f = tv n f

-- mkPredTable is definite on bounded indices when the cache is warm for all
-- atoms. The core "warm cache → two-valued" bridge: composes
-- `lookupAtom-warm` with `evalPredicate-cache-definite`, threaded through
-- `mkPredTable-lookup` to unfold the table definition.
warm-cache-table-definite : ∀ dbc cache atoms k frame → k < length atoms →
  AllCached cache atoms →
  (mkPredTable dbc cache atoms k frame ≡ True)
  ⊎ (mkPredTable dbc cache atoms k frame ≡ False)
warm-cache-table-definite dbc cache atoms k frame k< warm
  with lookupAtom-warm cache atoms k k< warm
... | p , cs , look-eq , hit
  with evalPredicate-cache-definite dbc cache p (TimedFrame.frame frame) cs hit
...   | inj₁ t =
        inj₁ (trans (mkPredTable-lookup dbc cache atoms k p frame look-eq) t)
...   | inj₂ f =
        inj₂ (trans (mkPredTable-lookup dbc cache atoms k p frame look-eq) f)

-- Bundled form: warm cache directly gives BoundedTwoValued on mkPredTable
-- at bound = length atoms.
warm-cache-bounded-twovalued : ∀ dbc cache atoms →
  AllCached cache atoms →
  BoundedTwoValued (length atoms) (mkPredTable dbc cache atoms)
warm-cache-bounded-twovalued dbc cache atoms warm n n< f =
  warm-cache-table-definite dbc cache atoms n f n< warm

-- ============================================================================
-- BOUNDED AGREEMENT
-- ============================================================================
--
-- Parallels `agreement` (Aletheia.LTL.Adequacy.Agreement) with:
--   * BoundedTwoValued b instead of TwoValued (universal)
--   * AllBelow b proc as an additional precondition
--   * AllBelow decomposition threaded through every recursive call
-- Structural cases mirror `agreement`; metric cases delegate to the shared
-- `agree-met-*` helpers exported by Agreement.agda, avoiding duplication.

agreement-bounded : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame) (b : ℕ)
  → BoundedTwoValued b table
  → AllBelow b proc
  → runL table proc σ ≡ ⟦ denot table proc ⟧ σ

agreement-bounded table (Atomic n) [] b btv bp = refl
agreement-bounded table (Atomic n) (x ∷ rest) b btv bp with table n x | btv n bp x
... | .True  | inj₁ refl = refl
... | .False | inj₂ refl = refl

agreement-bounded table (And φ ψ) σ b btv (bpφ , bpψ)
  rewrite runL-and-decomp table φ ψ σ
  = cong₂ _∧TV_ (agreement-bounded table φ σ b btv bpφ)
                (agreement-bounded table ψ σ b btv bpψ)

agreement-bounded table (Or φ ψ) σ b btv (bpφ , bpψ)
  rewrite runL-or-decomp table φ ψ σ
  = cong₂ _∨TV_ (agreement-bounded table φ σ b btv bpφ)
                (agreement-bounded table ψ σ b btv bpψ)

agreement-bounded table (Not φ) σ b btv bp
  rewrite runL-not-decomp table φ σ
  = cong notTV (agreement-bounded table φ σ b btv bp)

agreement-bounded table (Next φ) [] b btv bp = refl
agreement-bounded table (Next φ) (x ∷ rest) b btv bp =
  agreement-bounded table φ rest b btv bp

agreement-bounded table (WNext φ) [] b btv bp = refl
agreement-bounded table (WNext φ) (x ∷ rest) b btv bp =
  agreement-bounded table φ rest b btv bp

agreement-bounded table (Always φ) [] b btv bp = refl
agreement-bounded table (Always φ) (x ∷ rest) b btv bp =
  subst (_≡ ⟦ denot table φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Always (denot table φ) ⟧ rest)
        (sym (runL-always-decomp table φ x rest))
        (cong₂ _∧TV_ (agreement-bounded table φ (x ∷ rest) b btv bp)
                     (agreement-bounded table (Always φ) rest b btv bp))

agreement-bounded table (Eventually φ) [] b btv bp = refl
agreement-bounded table (Eventually φ) (x ∷ rest) b btv bp =
  subst (_≡ ⟦ denot table φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Eventually (denot table φ) ⟧ rest)
        (sym (runL-eventually-decomp table φ x rest))
        (cong₂ _∨TV_ (agreement-bounded table φ (x ∷ rest) b btv bp)
                     (agreement-bounded table (Eventually φ) rest b btv bp))

agreement-bounded table (Until φ ψ) [] b btv _ = refl
agreement-bounded table (Until φ ψ) (x ∷ rest) b btv (bpφ , bpψ) =
  subst (_≡ ⟦ denot table ψ ⟧ (x ∷ rest)
              ∨TV (⟦ denot table φ ⟧ (x ∷ rest)
                   ∧TV ⟦ Syntax.Until (denot table φ) (denot table ψ) ⟧ rest))
        (sym (runL-until-decomp table φ ψ x rest))
        (cong₂ _∨TV_ (agreement-bounded table ψ (x ∷ rest) b btv bpψ)
                     (cong₂ _∧TV_ (agreement-bounded table φ (x ∷ rest) b btv bpφ)
                                  (agreement-bounded table (Until φ ψ) rest b btv (bpφ , bpψ))))

agreement-bounded table (Release φ ψ) [] b btv _ = refl
agreement-bounded table (Release φ ψ) (x ∷ rest) b btv (bpφ , bpψ) =
  subst (_≡ ⟦ denot table ψ ⟧ (x ∷ rest)
              ∧TV (⟦ denot table φ ⟧ (x ∷ rest)
                   ∨TV ⟦ Syntax.Release (denot table φ) (denot table ψ) ⟧ rest))
        (sym (runL-release-decomp table φ ψ x rest))
        (cong₂ _∧TV_ (agreement-bounded table ψ (x ∷ rest) b btv bpψ)
                     (cong₂ _∨TV_ (agreement-bounded table φ (x ∷ rest) b btv bpφ)
                                  (agreement-bounded table (Release φ ψ) rest b btv (bpφ , bpψ))))

agreement-bounded table (MetricEventually w s φ) [] b btv bp = refl
agreement-bounded table (MetricEventually w s φ) (y ∷ rest) b btv bp =
  agree-met-ev table w s φ y rest
    (agreement-bounded table φ (y ∷ rest) b btv bp)
    (trans (agreement-bounded table (MetricEventually w (suc (decodeStart s (timestampℕ y))) φ) rest b btv bp)
           (sym (met-ev-go-denot w (denot table φ) (decodeStart s (timestampℕ y)) rest)))

agreement-bounded table (MetricAlways w s φ) [] b btv bp = refl
agreement-bounded table (MetricAlways w s φ) (y ∷ rest) b btv bp =
  agree-met-al table w s φ y rest
    (agreement-bounded table φ (y ∷ rest) b btv bp)
    (trans (agreement-bounded table (MetricAlways w (suc (decodeStart s (timestampℕ y))) φ) rest b btv bp)
           (sym (met-al-go-denot w (denot table φ) (decodeStart s (timestampℕ y)) rest)))

agreement-bounded table (MetricUntil w s φ ψ) [] b btv _ = refl
agreement-bounded table (MetricUntil w s φ ψ) (y ∷ rest) b btv (bpφ , bpψ) =
  agree-met-un table w s φ ψ y rest
    (agreement-bounded table φ (y ∷ rest) b btv bpφ)
    (agreement-bounded table ψ (y ∷ rest) b btv bpψ)
    (trans (agreement-bounded table (MetricUntil w (suc (decodeStart s (timestampℕ y))) φ ψ) rest b btv (bpφ , bpψ))
           (sym (met-un-go-denot w (denot table φ) (denot table ψ) (decodeStart s (timestampℕ y)) rest)))

agreement-bounded table (MetricRelease w s φ ψ) [] b btv _ = refl
agreement-bounded table (MetricRelease w s φ ψ) (y ∷ rest) b btv (bpφ , bpψ) =
  agree-met-re table w s φ ψ y rest
    (agreement-bounded table φ (y ∷ rest) b btv bpφ)
    (agreement-bounded table ψ (y ∷ rest) b btv bpψ)
    (trans (agreement-bounded table (MetricRelease w (suc (decodeStart s (timestampℕ y))) φ ψ) rest b btv (bpφ , bpψ))
           (sym (met-re-go-denot w (denot table φ) (denot table ψ) (decodeStart s (timestampℕ y)) rest)))

-- ============================================================================
-- WARM-CACHE AGREEMENT (HEADLINE COMPOSITION)
-- ============================================================================

-- Warm cache + formula bounded by atom count ⇒ runL ≡ ⟦_⟧.
-- The canonical use case: `atoms` is the atom list from a stepped LTLProc,
-- and Property 27 (FrameProcessor/Properties.agda) discharges AllBelow
-- automatically. No hand-off to a universal TwoValued is required.
warm-cache-agreement : ∀ dbc cache atoms (proc : LTLProc) σ
  → AllCached cache atoms
  → AllBelow (length atoms) proc
  → runL (mkPredTable dbc cache atoms) proc σ
    ≡ ⟦ denot (mkPredTable dbc cache atoms) proc ⟧ σ
warm-cache-agreement dbc cache atoms proc σ warm bound =
  agreement-bounded (mkPredTable dbc cache atoms) proc σ (length atoms)
    (warm-cache-bounded-twovalued dbc cache atoms warm)
    bound
