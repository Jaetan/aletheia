{-# OPTIONS --safe --without-K #-}

-- Adequacy of stepL (formula progression) w.r.t. denotational LTLf semantics.
--
-- Main theorem:
--   adequacy : ∀ table proc σ → Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)
--
-- The coalgebra (stepL + finalizeL) never gives a wrong definite answer:
-- if runL says True, ⟦_⟧ says True; if runL says False, ⟦_⟧ says False.
-- When either side is uncertain (Unknown/Pending), any result is acceptable.
--
-- Proof architecture:
--   1. Sound compositionality (sound-and, sound-or, sound-not) — in Adequacy.SoundOps
--   2. Operational decomposition (runL-*-decomp lemmas)
--   3. Soundness transport (subst-based, avoids with-auxiliaries)
--   4. Non-recursive metric helpers (fix termination checker)
--
-- All proofs hold for four-valued Kleene logic (True/False/Unknown/Pending).
-- Zero postulates, zero holes, all 13 LTL operators covered.
module Aletheia.LTL.Adequacy where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (subst)

import Aletheia.LTL.Syntax as Syntax
open Syntax using (LTL; decodeStart)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending;
  notTV; _∧TV_; _∨TV_)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL; denot;
  Atomic; Not; And; Or; Next; Always; Eventually; Until; Release;
  MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc)
open import Aletheia.LTL.Incremental using (Continue; Violated; Satisfied;
  FinalVerdict; Holds; Fails)
open import Aletheia.LTL.Semantics using (⟦_⟧; met-ev-go; met-al-go; met-un-go; met-re-go)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)

-- ============================================================================
-- FINAL VERDICT → SIGNAL VALUE CONVERSION
-- ============================================================================

verdictToSV : FinalVerdict → TruthVal
verdictToSV Holds = True
verdictToSV (Fails _) = False

-- ============================================================================
-- COALGEBRA EXECUTION ON FULL TRACE
-- ============================================================================

-- Run the coalgebra on a full trace, producing a TruthVal.
-- Takes a PredTable for evaluating atomic predicates.
-- No prev parameter — delta predicates use SignalCache externally.
--
-- When stepL returns:
--   Satisfied       → True  (property definitely holds)
--   Violated _      → False (property definitely fails)
--   Continue _ proc' → recurse on remaining trace
--   (Unknown/Pending signals produce Continue 0 for uncertain verdicts)

runL : PredTable → LTLProc → List TimedFrame → TruthVal
runL table proc [] = verdictToSV (finalizeL proc)
runL table proc (x ∷ rest) with stepL table proc x
... | Satisfied        = True
... | Violated _       = False
... | Continue _ proc' = runL table proc' rest

-- Sound datatype and compositionality combinators (extracted to separate module).
-- Re-exported publicly so all downstream users see the same names.
open import Aletheia.LTL.Adequacy.SoundOps public

-- ============================================================================
-- FOUR-VALUED IDENTITY LEMMAS (local copies for decomposition proofs)
-- ============================================================================

-- These are also defined in SoundOps (private there, for the Sound combinators).
-- Needed here because the operational decomposition lemmas (runL-*-decomp) use
-- rewrite with these identities, and SoundOps does not export them.

private
  ∧TV-false-r : ∀ a → (a ∧TV False) ≡ False
  ∧TV-false-r True    = refl
  ∧TV-false-r False   = refl
  ∧TV-false-r Unknown = refl
  ∧TV-false-r Pending = refl

  ∨TV-true-r : ∀ a → (a ∨TV True) ≡ True
  ∨TV-true-r True    = refl
  ∨TV-true-r False   = refl
  ∨TV-true-r Unknown = refl
  ∨TV-true-r Pending = refl

  ∨TV-false-r : ∀ a → (a ∨TV False) ≡ a
  ∨TV-false-r True    = refl
  ∨TV-false-r False   = refl
  ∨TV-false-r Unknown = refl
  ∨TV-false-r Pending = refl

  ∧TV-true-l : ∀ b → (True ∧TV b) ≡ b
  ∧TV-true-l True    = refl
  ∧TV-true-l False   = refl
  ∧TV-true-l Unknown = refl
  ∧TV-true-l Pending = refl

  ∧TV-true-r : ∀ a → (a ∧TV True) ≡ a
  ∧TV-true-r True    = refl
  ∧TV-true-r False   = refl
  ∧TV-true-r Unknown = refl
  ∧TV-true-r Pending = refl

  ∨TV-false-l : ∀ b → (False ∨TV b) ≡ b
  ∨TV-false-l True    = refl
  ∨TV-false-l False   = refl
  ∨TV-false-l Unknown = refl
  ∨TV-false-l Pending = refl

-- ============================================================================
-- OPERATIONAL DECOMPOSITION LEMMAS
-- ============================================================================

-- runL distributes over And: the coalgebra run of And φ ψ equals
-- the ∧TV combination of the individual runs.
-- Proof: list induction on σ. Base case uses finalizeL decomposition.
-- Inductive case uses combineAnd decomposition + IH.

runL-and-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → runL table (And φ ψ) σ ≡ (runL table φ σ) ∧TV (runL table ψ σ)
runL-and-decomp table φ ψ [] with finalizeL φ
... | Fails _ = refl
... | Holds with finalizeL ψ
...   | Fails _ = refl
...   | Holds   = refl
runL-and-decomp table φ ψ (x ∷ σ) with stepL table φ x | stepL table ψ x
... | Violated _   | _             = refl
... | Satisfied    | Violated _    = refl
... | Continue _ a | Violated _    rewrite ∧TV-false-r (runL table a σ) = refl
... | Satisfied    | Satisfied     = refl
... | Satisfied    | Continue _ b  rewrite ∧TV-true-l (runL table b σ) = refl
... | Continue _ a | Satisfied     rewrite ∧TV-true-r (runL table a σ) = refl
... | Continue _ a | Continue _ b  = runL-and-decomp table a b σ

-- runL distributes over Not: coalgebra run of Not φ equals notTV of the inner run.
runL-not-decomp : ∀ (table : PredTable) (φ : LTLProc) (σ : List TimedFrame)
  → runL table (Not φ) σ ≡ notTV (runL table φ σ)
runL-not-decomp table φ [] with finalizeL φ
... | Holds   = refl
... | Fails _ = refl
runL-not-decomp table φ (x ∷ σ) with stepL table φ x
... | Satisfied    = refl
... | Violated _   = refl
... | Continue _ φ' = runL-not-decomp table φ' σ

-- runL distributes over Or: dual of runL-and-decomp.
runL-or-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → runL table (Or φ ψ) σ ≡ (runL table φ σ) ∨TV (runL table ψ σ)
runL-or-decomp table φ ψ [] with finalizeL φ
... | Holds = refl
... | Fails _ with finalizeL ψ
...   | Holds   = refl
...   | Fails _ = refl
runL-or-decomp table φ ψ (x ∷ σ) with stepL table φ x | stepL table ψ x
... | Satisfied    | _             = refl
... | Violated _   | Satisfied     = refl
... | Violated _   | Violated _    = refl
... | Violated _   | Continue _ b  rewrite ∨TV-false-l (runL table b σ) = refl
... | Continue _ a | Satisfied     rewrite ∨TV-true-r (runL table a σ) = refl
... | Continue _ a | Violated _    rewrite ∨TV-false-r (runL table a σ) = refl
... | Continue _ a | Continue _ b  = runL-or-decomp table a b σ

-- runL distributes over Always: coalgebra run decomposes like the denotational semantics.
-- Always φ steps as combineAnd (stepL φ) (Continue 0 (Always φ)), matching ⟦φ⟧∧TV⟦G φ⟧.
runL-always-decomp : ∀ (table : PredTable) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Always φ) (x ∷ rest) ≡ (runL table φ (x ∷ rest)) ∧TV (runL table (Always φ) rest)
runL-always-decomp table φ x rest with stepL table φ x
... | Satisfied     rewrite ∧TV-true-l (runL table (Always φ) rest) = refl
... | Violated _    = refl
... | Continue _ φ' = runL-and-decomp table φ' (Always φ) rest

-- runL distributes over Eventually: dual of Always decomposition.
-- Eventually φ steps as combineOr (stepL φ) (Continue 0 (Eventually φ)), matching ⟦φ⟧∨TV⟦F φ⟧.
runL-eventually-decomp : ∀ (table : PredTable) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Eventually φ) (x ∷ rest) ≡ (runL table φ (x ∷ rest)) ∨TV (runL table (Eventually φ) rest)
runL-eventually-decomp table φ x rest with stepL table φ x
... | Satisfied     = refl
... | Violated _    rewrite ∨TV-false-l (runL table (Eventually φ) rest) = refl
... | Continue _ φ' = runL-or-decomp table φ' (Eventually φ) rest

-- runL distributes over Until: φ U ψ ≡ ψ ∨ (φ ∧ X(φ U ψ)).
-- stepL(Until φ ψ) = combineOr (stepL ψ) (combineAnd (stepL φ) (Continue 0 (Until φ ψ)))
runL-until-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Until φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∨TV ((runL table φ (x ∷ rest)) ∧TV (runL table (Until φ ψ) rest))
runL-until-decomp table φ ψ x rest with stepL table ψ x | stepL table φ x
... | Satisfied     | _             = refl
... | Violated _    | Violated _    = refl
... | Violated _    | Satisfied
    rewrite ∧TV-true-l (runL table (Until φ ψ) rest)
          | ∨TV-false-l (runL table (Until φ ψ) rest) = refl
... | Violated _    | Continue _ φ'
    rewrite ∨TV-false-l ((runL table φ' rest) ∧TV (runL table (Until φ ψ) rest))
    = runL-and-decomp table φ' (Until φ ψ) rest
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-l (runL table (Until φ ψ) rest)
    = runL-or-decomp table ψ' (Until φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-and-decomp table φ' (Until φ ψ) rest)
    = runL-or-decomp table ψ' (And φ' (Until φ ψ)) rest

-- runL distributes over Release: φ R ψ ≡ ψ ∧ (φ ∨ X(φ R ψ)).
-- stepL(Release φ ψ) = combineAnd (stepL ψ) (combineOr (stepL φ) (Continue 0 (Release φ ψ)))
runL-release-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Release φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∧TV ((runL table φ (x ∷ rest)) ∨TV (runL table (Release φ ψ) rest))
runL-release-decomp table φ ψ x rest with stepL table ψ x | stepL table φ x
... | Violated _    | _             = refl
... | Satisfied     | Satisfied     = refl
... | Satisfied     | Violated _
    rewrite ∨TV-false-l (runL table (Release φ ψ) rest)
          | ∧TV-true-l (runL table (Release φ ψ) rest) = refl
... | Satisfied     | Continue _ φ'
    rewrite ∧TV-true-l ((runL table φ' rest) ∨TV (runL table (Release φ ψ) rest))
    = runL-or-decomp table φ' (Release φ ψ) rest
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-l (runL table (Release φ ψ) rest)
    = runL-and-decomp table ψ' (Release φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-or-decomp table φ' (Release φ ψ) rest)
    = runL-and-decomp table ψ' (Or φ' (Release φ ψ)) rest

-- ============================================================================
-- METRIC OPERATOR HELPERS
-- ============================================================================

-- Bridge between met-*-go helpers and ⟦ Metric* (suc start) ⟧.
-- The go helpers are top-level mutual functions in Semantics.agda.
-- Key property: met-ev-go w φ start σ ≡ ⟦ MetricEventually w (suc start) φ ⟧ σ
-- This is NOT definitional for abstract σ (both are stuck pattern matches),
-- but holds by case split on σ (both clauses are refl).

private
  met-ev-go-denot : ∀ (w : ℕ) (φ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-ev-go w φ start σ ≡ ⟦ Syntax.MetricEventually w (suc start) φ ⟧ σ
  met-ev-go-denot w φ start [] = refl
  met-ev-go-denot w φ start (_ ∷ _) = refl

  met-al-go-denot : ∀ (w : ℕ) (φ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-al-go w φ start σ ≡ ⟦ Syntax.MetricAlways w (suc start) φ ⟧ σ
  met-al-go-denot w φ start [] = refl
  met-al-go-denot w φ start (_ ∷ _) = refl

  met-un-go-denot : ∀ (w : ℕ) (φ ψ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-un-go w φ ψ start σ ≡ ⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ σ
  met-un-go-denot w φ ψ start [] = refl
  met-un-go-denot w φ ψ start (_ ∷ _) = refl

  met-re-go-denot : ∀ (w : ℕ) (φ ψ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-re-go w φ ψ start σ ≡ ⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ σ
  met-re-go-denot w φ ψ start [] = refl
  met-re-go-denot w φ ψ start (_ ∷ _) = refl

-- Generic monitor-side transport: rewrite the monitor argument of Sound
-- along an equality, without generating with-auxiliaries (unlike rewrite).
-- This is the single pattern that all operational transport lemmas use.

sound-transport-monitor : ∀ {m₁ m₂ d} → m₁ ≡ m₂ → Sound m₁ d → Sound m₂ d
sound-transport-monitor {d = d} eq = subst (λ m → Sound m d) eq

sound-transport-denot : ∀ {m d₁ d₂} → d₁ ≡ d₂ → Sound m d₁ → Sound m d₂
sound-transport-denot {m = m} eq = subst (Sound m) eq

-- Denotational transport: convert adequacy IH from ⟦ MetricOp (suc start) ⟧
-- to met-*-go. These avoid `rewrite met-*-go-denot` which generates
-- with-auxiliaries that hide recursive calls from the termination checker.

met-ev-go-sound : ∀ {m} w φ start rest →
  Sound m (⟦ Syntax.MetricEventually w (suc start) φ ⟧ rest) →
  Sound m (met-ev-go w φ start rest)
met-ev-go-sound w φ start rest =
  sound-transport-denot (sym (met-ev-go-denot w φ start rest))

met-al-go-sound : ∀ {m} w φ start rest →
  Sound m (⟦ Syntax.MetricAlways w (suc start) φ ⟧ rest) →
  Sound m (met-al-go w φ start rest)
met-al-go-sound w φ start rest =
  sound-transport-denot (sym (met-al-go-denot w φ start rest))

met-un-go-sound : ∀ {m} w φ ψ start rest →
  Sound m (⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ rest) →
  Sound m (met-un-go w φ ψ start rest)
met-un-go-sound w φ ψ start rest =
  sound-transport-denot (sym (met-un-go-denot w φ ψ start rest))

met-re-go-sound : ∀ {m} w φ ψ start rest →
  Sound m (⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ rest) →
  Sound m (met-re-go w φ ψ start rest)
met-re-go-sound w φ ψ start rest =
  sound-transport-denot (sym (met-re-go-denot w φ ψ start rest))

-- Monitor-side transport: convert between runL on composed formulas
-- and ∨TV/∧TV of decomposed runL results.

runL-or-sound : ∀ {d} (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → Sound (runL table φ σ ∨TV runL table ψ σ) d
  → Sound (runL table (Or φ ψ) σ) d
runL-or-sound table φ ψ σ =
  sound-transport-monitor (sym (runL-or-decomp table φ ψ σ))

runL-and-sound : ∀ {d} (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → Sound (runL table φ σ ∧TV runL table ψ σ) d
  → Sound (runL table (And φ ψ) σ) d
runL-and-sound table φ ψ σ =
  sound-transport-monitor (sym (runL-and-decomp table φ ψ σ))

-- ============================================================================
-- METRIC DECOMPOSITION LEMMAS
-- ============================================================================

-- Conditional decomposition: when inWindow ≡ true, the metric operators
-- decompose like their unbounded counterparts (Eventually/Always/Until/Release).
-- The false case is absurd (discharged via () on the equality proof).

-- MetricEventually: mirrors runL-eventually-decomp
runL-metric-eventually-decomp : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricEventuallyProc w s φ) (x ∷ rest)
    ≡ (runL table φ (x ∷ rest)) ∨TV (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest)
runL-metric-eventually-decomp table w s φ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-eventually-decomp table w s φ x rest () | false
runL-metric-eventually-decomp table w s φ x rest eq | true with stepL table φ x
... | Satisfied     = refl
... | Violated _    rewrite ∨TV-false-l (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest) = refl
... | Continue _ φ' = runL-or-decomp table φ' (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest

-- MetricAlways: mirrors runL-always-decomp
runL-metric-always-decomp : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricAlwaysProc w s φ) (x ∷ rest)
    ≡ (runL table φ (x ∷ rest)) ∧TV (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest)
runL-metric-always-decomp table w s φ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-always-decomp table w s φ x rest () | false
runL-metric-always-decomp table w s φ x rest eq | true with stepL table φ x
... | Satisfied     rewrite ∧TV-true-l (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest) = refl
... | Violated _    = refl
... | Continue _ φ' = runL-and-decomp table φ' (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest

-- MetricUntil: mirrors runL-until-decomp
runL-metric-until-decomp : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricUntilProc w s φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∨TV ((runL table φ (x ∷ rest)) ∧TV (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
runL-metric-until-decomp table w s φ ψ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-until-decomp table w s φ ψ x rest () | false
runL-metric-until-decomp table w s φ ψ x rest eq | true with stepL table ψ x | stepL table φ x
... | Satisfied     | _             = refl
... | Violated _    | Violated _    = refl
... | Violated _    | Satisfied
    rewrite ∧TV-true-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
          | ∨TV-false-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest) = refl
... | Violated _    | Continue _ φ'
    rewrite ∨TV-false-l ((runL table φ' rest) ∧TV (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
    = runL-and-decomp table φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-or-decomp table ψ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-and-decomp table φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-or-decomp table ψ' (And φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ)) rest

-- MetricRelease: mirrors runL-release-decomp
runL-metric-release-decomp : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricReleaseProc w s φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∧TV ((runL table φ (x ∷ rest)) ∨TV (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
runL-metric-release-decomp table w s φ ψ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-release-decomp table w s φ ψ x rest () | false
runL-metric-release-decomp table w s φ ψ x rest eq | true with stepL table ψ x | stepL table φ x
... | Violated _    | _             = refl
... | Satisfied     | Satisfied     = refl
... | Satisfied     | Violated _
    rewrite ∨TV-false-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
          | ∧TV-true-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest) = refl
... | Satisfied     | Continue _ φ'
    rewrite ∧TV-true-l ((runL table φ' rest) ∨TV (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
    = runL-or-decomp table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-and-decomp table ψ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-or-decomp table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-and-decomp table ψ' (Or φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ)) rest

-- ============================================================================
-- METRIC ADEQUACY HELPERS (non-recursive)
-- ============================================================================

-- These helpers extract the boolean + stepL case analysis from adequacy,
-- so that adequacy itself has zero `with`s for metric operators.
-- The termination checker can then see the direct recursive calls.

-- MetricEventually: boolean guard + stepL case split. Non-recursive.
adequacy-met-ev : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest)
          (met-ev-go w (denot table φ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricEventuallyProc w s φ) (y ∷ rest))
          (⟦ denot table (MetricEventuallyProc w s φ) ⟧ (y ∷ rest))
adequacy-met-ev table w s φ y rest ih-φ ih-MEP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-ff
... | true with stepL table φ y
...   | Satisfied   = sound-or ih-φ ih-MEP
...   | Violated _  = sound-or-false-l ih-φ ih-MEP
...   | Continue _ φ' = runL-or-sound table φ' (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest
                          (sound-or ih-φ ih-MEP)

-- MetricAlways: dual of MetricEventually (∧ instead of ∨, sound-tt on window expiry).
adequacy-met-al : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest)
          (met-al-go w (denot table φ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricAlwaysProc w s φ) (y ∷ rest))
          (⟦ denot table (MetricAlwaysProc w s φ) ⟧ (y ∷ rest))
adequacy-met-al table w s φ y rest ih-φ ih-MAP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-tt
... | true with stepL table φ y
...   | Satisfied   = sound-and-true-l ih-φ ih-MAP
...   | Violated _  = sound-and ih-φ ih-MAP
...   | Continue _ φ' = runL-and-sound table φ' (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest
                          (sound-and ih-φ ih-MAP)

-- MetricUntil: simultaneous (stepL ψ × stepL φ) after boolean guard. Non-recursive.
adequacy-met-un : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table ψ (y ∷ rest)) (⟦ denot table ψ ⟧ (y ∷ rest))
  → Sound (runL table (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest)
          (met-un-go w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricUntilProc w s φ ψ) (y ∷ rest))
          (⟦ denot table (MetricUntilProc w s φ ψ) ⟧ (y ∷ rest))
adequacy-met-un table w s φ ψ y rest ih-φ ih-ψ ih-MUP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-ff
... | true with stepL table ψ y | stepL table φ y
...   | Satisfied     | _             = sound-or ih-ψ (sound-and ih-φ ih-MUP)
...   | Violated _    | Satisfied     = sound-or-false-l ih-ψ (sound-and-true-l ih-φ ih-MUP)
...   | Violated _    | Violated _    = sound-or ih-ψ (sound-and ih-φ ih-MUP)
...   | Violated _    | Continue _ φ' = sound-or-false-l ih-ψ
                                          (runL-and-sound table φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                            (sound-and ih-φ ih-MUP))
...   | Continue _ ψ' | Satisfied     = runL-or-sound table ψ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                          (sound-or ih-ψ (sound-and-true-l ih-φ ih-MUP))
...   | Continue _ ψ' | Violated _    = sound-or-false-r ih-ψ (sound-and ih-φ ih-MUP)
...   | Continue _ ψ' | Continue _ φ' = runL-or-sound table ψ' (And φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ)) rest
                                          (sound-or ih-ψ
                                            (runL-and-sound table φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                              (sound-and ih-φ ih-MUP)))

-- MetricRelease: dual of MetricUntil (∧/∨ swapped). Non-recursive.
-- Decomposition: ψ ∧ (φ ∨ MRP). Simultaneous with on stepL ψ and stepL φ.
adequacy-met-re : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table ψ (y ∷ rest)) (⟦ denot table ψ ⟧ (y ∷ rest))
  → Sound (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest)
          (met-re-go w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricReleaseProc w s φ ψ) (y ∷ rest))
          (⟦ denot table (MetricReleaseProc w s φ ψ) ⟧ (y ∷ rest))
adequacy-met-re table w s φ ψ y rest ih-φ ih-ψ ih-MRP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-tt
... | true with stepL table ψ y | stepL table φ y
...   | Violated _    | _             = sound-and ih-ψ (sound-or ih-φ ih-MRP)
...   | Satisfied     | Satisfied     = sound-and ih-ψ (sound-or ih-φ ih-MRP)
...   | Satisfied     | Violated _    = sound-and-true-l ih-ψ (sound-or-false-l ih-φ ih-MRP)
...   | Satisfied     | Continue _ φ' = sound-and-true-l ih-ψ
                                          (runL-or-sound table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                            (sound-or ih-φ ih-MRP))
...   | Continue _ ψ' | Satisfied     = sound-and-true-r ih-ψ (sound-or ih-φ ih-MRP)
...   | Continue _ ψ' | Violated _    = runL-and-sound table ψ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                          (sound-and ih-ψ (sound-or-false-l ih-φ ih-MRP))
...   | Continue _ ψ' | Continue _ φ' = runL-and-sound table ψ' (Or φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ)) rest
                                          (sound-and ih-ψ
                                            (runL-or-sound table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                              (sound-or ih-φ ih-MRP)))

-- ============================================================================
-- ADEQUACY THEOREM
-- ============================================================================

-- The crown jewel: for any LTLProc and trace, the coalgebra execution (runL)
-- is sound with respect to the denotational semantics (⟦_⟧).
-- Structural induction on LTLProc (outer) + list induction on σ (inner).

adequacy : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)

-- Atomic: empty trace
adequacy table (Atomic n) [] = sound-ff

-- Atomic: non-empty trace — case split on table n x
adequacy table (Atomic n) (x ∷ rest) with table n x
... | True    = sound-tt
... | False   = sound-ff
... | Unknown = sound-unk
... | Pending = sound-pen

-- And: decompose runL to ∧TV, then compose with sound-and + IH
adequacy table (And φ ψ) σ rewrite runL-and-decomp table φ ψ σ = sound-and (adequacy table φ σ) (adequacy table ψ σ)

-- Or: decompose runL to ∨TV, then compose with sound-or + IH
adequacy table (Or φ ψ) σ rewrite runL-or-decomp table φ ψ σ = sound-or (adequacy table φ σ) (adequacy table ψ σ)

-- Next: empty → sound-ff; non-empty → IH on tail
adequacy table (Next φ) [] = sound-ff
adequacy table (Next φ) (x ∷ rest) = adequacy table φ rest

-- Always: empty → sound-tt (vacuous); non-empty → decompose + sound-and + IH
-- Uses subst (not rewrite) to avoid with-generated auxiliary that confuses termination checker.
adequacy table (Always φ) [] = sound-tt
adequacy table (Always φ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Always (denot table φ) ⟧ rest))
        (sym (runL-always-decomp table φ x rest))
        (sound-and (adequacy table φ (x ∷ rest)) (adequacy table (Always φ) rest))

-- Eventually: empty → sound-ff; non-empty → decompose + sound-or + IH
adequacy table (Eventually φ) [] = sound-ff
adequacy table (Eventually φ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Eventually (denot table φ) ⟧ rest))
        (sym (runL-eventually-decomp table φ x rest))
        (sound-or (adequacy table φ (x ∷ rest)) (adequacy table (Eventually φ) rest))

-- Until: empty → sound-ff; non-empty → ψ ∨ (φ ∧ Until), subst on monitor
adequacy table (Until φ ψ) [] = sound-ff
adequacy table (Until φ ψ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table ψ ⟧ (x ∷ rest)
                          ∨TV (⟦ denot table φ ⟧ (x ∷ rest)
                               ∧TV ⟦ Syntax.Until (denot table φ) (denot table ψ) ⟧ rest)))
        (sym (runL-until-decomp table φ ψ x rest))
        (sound-or (adequacy table ψ (x ∷ rest))
                  (sound-and (adequacy table φ (x ∷ rest))
                             (adequacy table (Until φ ψ) rest)))

-- Release: empty → sound-tt; non-empty → ψ ∧ (φ ∨ Release), subst on monitor
adequacy table (Release φ ψ) [] = sound-tt
adequacy table (Release φ ψ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table ψ ⟧ (x ∷ rest)
                          ∧TV (⟦ denot table φ ⟧ (x ∷ rest)
                               ∨TV ⟦ Syntax.Release (denot table φ) (denot table ψ) ⟧ rest)))
        (sym (runL-release-decomp table φ ψ x rest))
        (sound-and (adequacy table ψ (x ∷ rest))
                   (sound-or (adequacy table φ (x ∷ rest))
                             (adequacy table (Release φ ψ) rest)))

-- MetricEventually: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricEventuallyProc w s φ) [] = sound-ff
adequacy table (MetricEventuallyProc w s φ) (y ∷ rest) =
  adequacy-met-ev table w s φ y rest
    (adequacy table φ (y ∷ rest))
    (met-ev-go-sound w (denot table φ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest))

-- MetricAlways: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricAlwaysProc w s φ) [] = sound-tt
adequacy table (MetricAlwaysProc w s φ) (y ∷ rest) =
  adequacy-met-al table w s φ y rest
    (adequacy table φ (y ∷ rest))
    (met-al-go-sound w (denot table φ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest))

-- MetricUntil: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricUntilProc w s φ ψ) [] = sound-ff
adequacy table (MetricUntilProc w s φ ψ) (y ∷ rest) =
  adequacy-met-un table w s φ ψ y rest
    (adequacy table φ (y ∷ rest))
    (adequacy table ψ (y ∷ rest))
    (met-un-go-sound w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest))

-- MetricRelease: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricReleaseProc w s φ ψ) [] = sound-tt
adequacy table (MetricReleaseProc w s φ ψ) (y ∷ rest) =
  adequacy-met-re table w s φ ψ y rest
    (adequacy table φ (y ∷ rest))
    (adequacy table ψ (y ∷ rest))
    (met-re-go-sound w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest))

-- Not: decompose runL to notTV, then compose with sound-not + IH
adequacy table (Not φ) σ rewrite runL-not-decomp table φ σ = sound-not (adequacy table φ σ)
