{-# OPTIONS --safe --without-K #-}

-- Pipeline adequacy: the production pipeline (stepL → simplify → repeat)
-- preserves the adequacy guarantee of the coalgebra.
--
-- Key theorem: pipeline-adequate
--   The simplify step applied between each stepL call does not affect
--   the final verdict. This follows directly from simplify-runL
--   (SimplifySound.agda) and the existing adequacy theorem (Adequacy.agda).

module Aletheia.LTL.Adequacy.Pipeline where

open import Aletheia.Prelude
open import Relation.Binary.PropositionalEquality using (subst)

open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL;
  simplify; denot; initProc)
open import Aletheia.LTL.Incremental using (Continue; Violated; Satisfied;
  StepResult)
open import Aletheia.LTL.Adequacy using (runL; verdictToSV; adequacy)
open import Aletheia.LTL.Adequacy.SoundOps using (Sound)
open import Aletheia.LTL.SimplifySound using (simplify-runL)
open import Aletheia.LTL.Semantics using (⟦_⟧)
open import Aletheia.Trace.CANTrace using (TimedFrame)
import Aletheia.LTL.Syntax as Syntax

-- Pipeline runner: applies simplify after each Continue step,
-- matching the production code in StreamState.agda.
runL-s : PredTable → LTLProc → List TimedFrame → TruthVal
runL-s table proc [] = verdictToSV (finalizeL proc)
runL-s table proc (x ∷ rest) with stepL table proc x
... | Satisfied      = True
... | Violated _     = False
... | Continue _ proc' = runL-s table (simplify proc') rest

-- Bridge lemma: runL-s ≡ runL (simplify doesn't affect the result).
runL-s-eq : ∀ table proc σ → runL-s table proc σ ≡ runL table proc σ
runL-s-eq table proc [] = refl
runL-s-eq table proc (x ∷ rest) with stepL table proc x
... | Satisfied      = refl
... | Violated _     = refl
... | Continue _ proc' =
  trans (runL-s-eq table (simplify proc') rest)
        (simplify-runL table proc' rest)

-- Pipeline adequacy: the production pipeline is sound w.r.t. denotational semantics.
pipeline-adequate : ∀ table proc σ
  → Sound (runL-s table proc σ) (⟦ denot table proc ⟧ σ)
pipeline-adequate table proc σ =
  subst (λ m → Sound m (⟦ denot table proc ⟧ σ))
        (sym (runL-s-eq table proc σ))
        (adequacy table proc σ)

-- Production theorem: from user formula (LTL ℕ) through the full pipeline to verdict.
production-adequate : ∀ (φ : Syntax.LTL ℕ) table σ
  → Sound (runL-s table (initProc φ) σ) (⟦ denot table (initProc φ) ⟧ σ)
production-adequate φ table σ = pipeline-adequate table (initProc φ) σ
