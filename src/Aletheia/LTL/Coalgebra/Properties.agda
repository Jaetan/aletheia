{-# OPTIONS --safe --without-K #-}

-- Properties of the LTL coalgebra: initialization, metric window bounds,
-- and monotonic-trace agreement with textbook MTL semantics.
--
-- Key theorems:
--   initProc-correct          : initProc produces correct initial state for denot
--   stepL-met-*-expired       : past window -> Violated/Satisfied (terminal, not Continue)
--   runL-met-*-expired        : first frame past window -> runL resolves immediately
--   past-window-mono          : monotonic timestamps -> past-window is persistent
--   remaining-anti-mono       : monotonic timestamps -> remaining time non-increasing
--   runL-trichotomy           : runL returns True, False, or Unknown
--   runL-monotonic-mtl-sound  : runL is sound w.r.t. textbook ⟦_⟧ₘ on monotonic traces
--   runL-monotonic-{False,True} : definite ⟦_⟧ₘ verdicts → runL says same or Unknown
--
-- Together these prove metric operators respect their time window:
-- (1) at window expiry, stepL produces a terminal verdict,
-- (2) on monotonic traces, once expired always expired (past-window-mono),
-- (3) remaining time makes monotonic progress toward zero,
-- (4) runL agrees with the textbook (non-short-circuiting) MTL semantics on
--     monotonic traces — composing adequacy with mtl-equiv via Sound transport.
module Aletheia.LTL.Coalgebra.Properties where

open import Data.Nat using (ℕ; _∸_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (∸-monoˡ-≤; ∸-monoʳ-≤)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Aletheia.LTL.Syntax using (LTL; mapLTL; decodeStart;
  Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
  MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Coalgebra using (PredTable; LTLProc; initProc; denot; stepL; finalizeL; metricElapsed)
open import Aletheia.LTL.Incremental using (Counterexample; Continue; Violated; Satisfied;
  mkCounterexample; Holds; Fails; Unsure;
  MetricEventuallyExpired; MetricUntilExpired)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; notTV)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestampℕ; Monotonic)
open import Aletheia.LTL.Adequacy using (runL; adequacy; Sound; verdictToSV;
  sound-transport-monitor; sound-transport-denot; sound-transport)
open import Aletheia.LTL.Semantics using (⟦_⟧)
open import Aletheia.LTL.Semantics.MTL using (⟦_⟧ₘ; mtl-equiv)

-- Re-export: on monotonic traces, once past the window, always past.
-- Key: if a <= b and ((a - c) <=? w) = false, then ((b - c) <=? w) = false.
open import Aletheia.LTL.Semantics.MTL using (past-window-mono) public

-- ============================================================================
-- INITIALIZATION CORRECTNESS
-- ============================================================================

-- initProc correctly initializes the LTL process state:
-- denot recovers the intended formula (atoms mapped through PredTable).
initProc-correct : ∀ (table : PredTable) (φ : LTL ℕ)
  → denot table (initProc φ) ≡ mapLTL table φ
initProc-correct table φ = refl

-- ============================================================================
-- METRIC OPERATOR WINDOW EXPIRY (stepL)
-- ============================================================================

-- When the elapsed time exceeds the window, metric operators produce
-- terminal results (Violated or Satisfied), never Continue.
--
-- Liveness operators (MetricEventually, MetricUntil): Violated
-- Safety operators (MetricAlways, MetricRelease): Satisfied

stepL-met-ev-expired : ∀ (table : PredTable) w s (φ : LTLProc) (curr : TimedFrame)
  → (metricElapsed s curr ≤ᵇ w) ≡ false
  → stepL table (MetricEventually w s φ) curr
    ≡ Violated (mkCounterexample curr MetricEventuallyExpired)
stepL-met-ev-expired table w s φ curr eq
  with metricElapsed s curr ≤ᵇ w
stepL-met-ev-expired table w s φ curr refl | false = refl

stepL-met-al-expired : ∀ (table : PredTable) w s (φ : LTLProc) (curr : TimedFrame)
  → (metricElapsed s curr ≤ᵇ w) ≡ false
  → stepL table (MetricAlways w s φ) curr ≡ Satisfied
stepL-met-al-expired table w s φ curr eq
  with metricElapsed s curr ≤ᵇ w
stepL-met-al-expired table w s φ curr refl | false = refl

stepL-met-un-expired : ∀ (table : PredTable) w s (φ ψ : LTLProc) (curr : TimedFrame)
  → (metricElapsed s curr ≤ᵇ w) ≡ false
  → stepL table (MetricUntil w s φ ψ) curr
    ≡ Violated (mkCounterexample curr MetricUntilExpired)
stepL-met-un-expired table w s φ ψ curr eq
  with metricElapsed s curr ≤ᵇ w
stepL-met-un-expired table w s φ ψ curr refl | false = refl

stepL-met-re-expired : ∀ (table : PredTable) w s (φ ψ : LTLProc) (curr : TimedFrame)
  → (metricElapsed s curr ≤ᵇ w) ≡ false
  → stepL table (MetricRelease w s φ ψ) curr ≡ Satisfied
stepL-met-re-expired table w s φ ψ curr eq
  with metricElapsed s curr ≤ᵇ w
stepL-met-re-expired table w s φ ψ curr refl | false = refl

-- ============================================================================
-- GENERIC TERMINAL STEP → runL RESULT
-- ============================================================================

-- Generic: if stepL on the first frame returns Violated, runL returns False.
-- Proven by `with`-abstraction (required because runL is defined by `with stepL`).
runL-stepL-violated : ∀ (table : PredTable) (proc : LTLProc) ce
  (y : TimedFrame) (rest : List TimedFrame)
  → stepL table proc y ≡ Violated ce
  → runL table proc (y ∷ rest) ≡ False
runL-stepL-violated table proc ce y rest eq
  with stepL table proc y
runL-stepL-violated table proc ce y rest refl | .(Violated ce) = refl

-- Generic: if stepL on the first frame returns Satisfied, runL returns True.
runL-stepL-satisfied : ∀ (table : PredTable) (proc : LTLProc)
  (y : TimedFrame) (rest : List TimedFrame)
  → stepL table proc y ≡ Satisfied
  → runL table proc (y ∷ rest) ≡ True
runL-stepL-satisfied table proc y rest eq
  with stepL table proc y
runL-stepL-satisfied table proc y rest refl | .Satisfied = refl

-- ============================================================================
-- VERDICT STABILITY (finding A27)
-- ============================================================================

-- The "stepL-satisfied-stable" property: once stepL produces a terminal
-- verdict (Satisfied or Violated) at any frame, all subsequent frames are
-- irrelevant — runL's result is determined.
--
-- This is exactly `runL-stepL-satisfied` and `runL-stepL-violated` above:
-- they say that if stepL returns Satisfied/Violated at the first frame,
-- then runL over any (y :: rest) returns True/False regardless of rest.
-- The inductive extension (stability over a longer prefix σ₁ ++ σ₂) is
-- NOT a theorem in general because runL's empty-trace base case uses
-- `finalizeL` — a conservative end-of-stream approximation that can
-- disagree with subsequent frames. For example, Always(p) finalizes to
-- Holds on the empty trace but may Fail on σ₂ = [frame_where_p_is_false].
-- Stability is strictly a property of frames where stepL produces a
-- terminal result (Satisfied / Violated), NOT of Continue-to-finalizeL.
--
-- Summary:
--   runL-stepL-satisfied  :  stepL proc y ≡ Satisfied → runL proc (y ∷ rest) ≡ True
--   runL-stepL-violated   :  stepL proc y ≡ Violated ce → runL proc (y ∷ rest) ≡ False
--
-- These are the two halves of verdict stability. The type system enforces
-- that Satisfied/Violated carry no successor LTLProc, so there is literally
-- no state to feed additional frames to — stability is structural.

-- ============================================================================
-- METRIC OPERATOR WINDOW EXPIRY (runL)
-- ============================================================================

-- When the first frame is past the window, runL immediately resolves.
-- Combined with past-window-mono, this extends to any monotonic trace
-- whose first frame exceeds the window.
--
-- Note: these corollaries cannot simply compose stepL-met-*-expired with
-- runL-stepL-violated/satisfied because Agda can't infer the proc argument —
-- stepL for metric operators has an internal `with` on the ≤ᵇ expression that
-- blocks reduction until the boolean is known. So each corollary drives the
-- same `with`-abstraction directly.

runL-met-ev-expired : ∀ (table : PredTable) w s (φ : LTLProc)
  (y : TimedFrame) (rest : List TimedFrame)
  → (metricElapsed s y ≤ᵇ w) ≡ false
  → runL table (MetricEventually w s φ) (y ∷ rest) ≡ False
runL-met-ev-expired table w s φ y rest eq
  with metricElapsed s y ≤ᵇ w
runL-met-ev-expired table w s φ y rest refl | false = refl

runL-met-al-expired : ∀ (table : PredTable) w s (φ : LTLProc)
  (y : TimedFrame) (rest : List TimedFrame)
  → (metricElapsed s y ≤ᵇ w) ≡ false
  → runL table (MetricAlways w s φ) (y ∷ rest) ≡ True
runL-met-al-expired table w s φ y rest eq
  with metricElapsed s y ≤ᵇ w
runL-met-al-expired table w s φ y rest refl | false = refl

runL-met-un-expired : ∀ (table : PredTable) w s (φ ψ : LTLProc)
  (y : TimedFrame) (rest : List TimedFrame)
  → (metricElapsed s y ≤ᵇ w) ≡ false
  → runL table (MetricUntil w s φ ψ) (y ∷ rest) ≡ False
runL-met-un-expired table w s φ ψ y rest eq
  with metricElapsed s y ≤ᵇ w
runL-met-un-expired table w s φ ψ y rest refl | false = refl

runL-met-re-expired : ∀ (table : PredTable) w s (φ ψ : LTLProc)
  (y : TimedFrame) (rest : List TimedFrame)
  → (metricElapsed s y ≤ᵇ w) ≡ false
  → runL table (MetricRelease w s φ ψ) (y ∷ rest) ≡ True
runL-met-re-expired table w s φ ψ y rest eq
  with metricElapsed s y ≤ᵇ w
runL-met-re-expired table w s φ ψ y rest refl | false = refl

-- ============================================================================
-- REMAINING TIME MONOTONICITY
-- ============================================================================

-- On monotonic traces (t1 <= t2), the remaining time for a metric operator
-- with window w and start time s is non-increasing:
--   w - (t2 - s) <= w - (t1 - s)
--
-- Proof: t1 <= t2 implies t1 - s <= t2 - s (monoL), then
-- the outer subtraction reverses the order (monoR/anti-monotone).
-- This guarantees monotonic progress toward window expiry.
remaining-anti-mono : ∀ w s {t₁ t₂} → t₁ ≤ t₂ → w ∸ (t₂ ∸ s) ≤ w ∸ (t₁ ∸ s)
remaining-anti-mono w s t₁≤t₂ = ∸-monoʳ-≤ w (∸-monoˡ-≤ s t₁≤t₂)

-- ============================================================================
-- METRIC RESOLUTION GUARANTEE
-- ============================================================================

-- runL returns one of the three definite truth values: True, False, or Unknown.
-- Pending never appears because verdictToSV maps the three FinalVerdict
-- constructors (Holds → True, Fails → False, Unsure → Unknown) and stepL
-- produces Satisfied → True, Violated → False, Continue → recurse.
--
-- Prior to Path G (2026-04-09), runL was two-valued (True ⊎ False) because
-- finalizeL had no Unsure constructor. Path G introduced Kleene three-valued
-- finalization: finalizeL (Atomic _) = Unsure _ → verdictToSV = Unknown.
runL-trichotomy : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → (runL table proc σ ≡ True) ⊎ (runL table proc σ ≡ False) ⊎ (runL table proc σ ≡ Unknown)
runL-trichotomy table proc [] with finalizeL proc
... | Holds    = inj₁ refl
... | Fails _  = inj₂ (inj₁ refl)
... | Unsure _ = inj₂ (inj₂ refl)
runL-trichotomy table proc (x ∷ rest) with stepL table proc x
... | Satisfied        = inj₁ refl
... | Violated _       = inj₂ (inj₁ refl)
... | Continue _ proc' = runL-trichotomy table proc' rest

-- On monotonic traces, runL is sound w.r.t. the textbook (non-short-circuiting)
-- MTL semantics. Composes adequacy (runL ↔ ⟦_⟧) with mtl-equiv (⟦_⟧ ≡ ⟦_⟧ₘ on
-- monotonic traces) via Sound transport. This is the bridge: the operational
-- monitor agrees with the standard MTL reference semantics whenever timestamps
-- are well-formed.
runL-monotonic-mtl-sound : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → Monotonic σ
  → Sound (runL table proc σ) (⟦ denot table proc ⟧ₘ σ)
runL-monotonic-mtl-sound table proc σ mono =
  sound-transport-denot (mtl-equiv (denot table proc) σ mono) (adequacy table proc σ)

-- Metric resolution guarantee (False direction): if the textbook MTL semantics
-- definitely fails on a monotonic trace, runL returns False or Unknown.
--
-- This is the headline corollary for finite monotonic traces past the window.
-- Concretely: when MetricEventually's window is fully past with no witness,
-- ⟦_⟧ₘ evaluates to False, and runL returns False (or Unknown if the formula
-- contained an atomic predicate that was never resolved before end-of-stream).
--
-- Proof: case split on runL-trichotomy. If runL is True, the two-sided
-- `sound-transport` rewrites the sound-bridge to `Sound True False`, which
-- has no constructor (absurd: monitor would have lied).
runL-monotonic-False : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → Monotonic σ
  → ⟦ denot table proc ⟧ₘ σ ≡ False
  → (runL table proc σ ≡ False) ⊎ (runL table proc σ ≡ Unknown)
runL-monotonic-False table proc σ mono d≡F
  with runL-trichotomy table proc σ
... | inj₂ (inj₁ runL≡F) = inj₁ runL≡F
... | inj₂ (inj₂ runL≡U) = inj₂ runL≡U
... | inj₁ runL≡T
        with sound-transport runL≡T d≡F
               (runL-monotonic-mtl-sound table proc σ mono)
...   | ()

-- Metric resolution guarantee (True direction): dual of runL-monotonic-False.
-- If the textbook MTL semantics definitely holds on a monotonic trace, runL
-- returns True or Unknown (never False — that would contradict soundness).
runL-monotonic-True : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → Monotonic σ
  → ⟦ denot table proc ⟧ₘ σ ≡ True
  → (runL table proc σ ≡ True) ⊎ (runL table proc σ ≡ Unknown)
runL-monotonic-True table proc σ mono d≡T
  with runL-trichotomy table proc σ
... | inj₁ runL≡T        = inj₁ runL≡T
... | inj₂ (inj₂ runL≡U) = inj₂ runL≡U
... | inj₂ (inj₁ runL≡F)
        with sound-transport runL≡F d≡T
               (runL-monotonic-mtl-sound table proc σ mono)
...   | ()

-- ============================================================================
-- FINALIZATION SOUNDNESS
-- ============================================================================

-- At the end of a stream, the operational finalizer (verdictToSV ∘ finalizeL)
-- agrees propositionally with the denotational LTLf semantics on the empty
-- trace. Concretely, when the monitor reaches end-of-stream and reports a
-- final verdict, that verdict matches what ⟦_⟧ would say at the empty trace.
--
-- This closes the last LTLf liveness sub-item: it connects the operational
-- "didn't find a witness" intuition to the denotational "no witness exists"
-- statement, exactly when there are no more frames to consume.
--
-- Headline use case: if Eventually/Until/MetricEventually/MetricUntil are
-- still in Continue when the trace ends, finalizeL produces Fails → False,
-- and ⟦_⟧ on the empty suffix also produces False — agreement is exact.
--
-- Proof: structural induction on proc (13 LTL constructors). Each temporal
-- and atomic case reduces by refl since both sides reduce to the same
-- True/False at the empty trace. The propositional cases (Not/And/Or)
-- use the IH and the algebraic structure of notTV/∧TV/∨TV.
finalize-empty-equiv : ∀ (table : PredTable) (proc : LTLProc)
  → verdictToSV (finalizeL proc) ≡ ⟦ denot table proc ⟧ []
finalize-empty-equiv table (Atomic _) = refl
finalize-empty-equiv table (Not φ)
  with finalizeL φ | finalize-empty-equiv table φ
... | Holds    | ih = cong notTV ih
... | Fails _  | ih = cong notTV ih
... | Unsure _ | ih = cong notTV ih
finalize-empty-equiv table (And φ ψ)
  with finalizeL φ | finalize-empty-equiv table φ
... | Fails _  | ih₁ rewrite sym ih₁ = refl
... | Holds    | ih₁
        with finalizeL ψ | finalize-empty-equiv table ψ
...   | Fails _  | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Holds    | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Unsure _ | ih₂ rewrite sym ih₁ | sym ih₂ = refl
finalize-empty-equiv table (And φ ψ) | Unsure _ | ih₁
        with finalizeL ψ | finalize-empty-equiv table ψ
...   | Fails _  | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Holds    | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Unsure _ | ih₂ rewrite sym ih₁ | sym ih₂ = refl
finalize-empty-equiv table (Or φ ψ)
  with finalizeL φ | finalize-empty-equiv table φ
... | Holds    | ih₁ rewrite sym ih₁ = refl
... | Fails _  | ih₁
        with finalizeL ψ | finalize-empty-equiv table ψ
...   | Holds    | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Fails _  | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Unsure _ | ih₂ rewrite sym ih₁ | sym ih₂ = refl
finalize-empty-equiv table (Or φ ψ) | Unsure _ | ih₁
        with finalizeL ψ | finalize-empty-equiv table ψ
...   | Holds    | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Fails _  | ih₂ rewrite sym ih₁ | sym ih₂ = refl
...   | Unsure _ | ih₂ rewrite sym ih₁ | sym ih₂ = refl
finalize-empty-equiv table (Next _) = refl
finalize-empty-equiv table (WNext _) = refl
finalize-empty-equiv table (Always _) = refl
finalize-empty-equiv table (Eventually _) = refl
finalize-empty-equiv table (Until _ _) = refl
finalize-empty-equiv table (Release _ _) = refl
finalize-empty-equiv table (MetricEventually _ _ _) = refl
finalize-empty-equiv table (MetricAlways _ _ _) = refl
finalize-empty-equiv table (MetricUntil _ _ _ _) = refl
finalize-empty-equiv table (MetricRelease _ _ _ _) = refl
