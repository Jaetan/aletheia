{-# OPTIONS --safe --without-K #-}

-- Reachable-state predicate for LTLProc formulas.
--
-- Defines which LTLProc formulas can arise from stepL progression.
-- This characterizes the pipeline's state space.
--
-- Note: the absorption rules in Coalgebra.agda are unconditionally sound
-- (proven in SimplifySound.agda: absorb-runL, simplify-runL). The unsound
-- Until/Release rules were removed and Always/Eventually rules were guarded
-- by finalizesHolds. This predicate is therefore NOT required for the
-- pipeline adequacy proof (see Adequacy/Pipeline.agda), but documents the
-- pipeline's reachable states for future structural reasoning.
module Aletheia.LTL.Reachable where

open import Aletheia.Prelude
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; initProc; simplify)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- ============================================================================
-- REACHABLE PREDICATE
-- ============================================================================

-- A formula is reachable if it can be produced from initProc via stepL+simplify.
-- This captures exactly the formulas that arise in the streaming pipeline.
data Reachable : LTLProc → Set where
  -- Base: any formula produced by initProc is reachable
  base : ∀ (φ : LTL ℕ) → Reachable (initProc φ)

  -- Step: if proc is reachable and stepL produces a Continue with proc',
  -- then simplify proc' is reachable (simplify is applied after each step)
  step : ∀ {proc proc' : LTLProc} {n : ℕ}
       → (table : PredTable) → (frame : TimedFrame)
       → Reachable proc
       → stepL table proc frame ≡ Continue n proc'
       → Reachable (simplify proc')

-- ============================================================================
-- STRUCTURAL LEMMAS
-- ============================================================================

-- The Reachable predicate documents which formulas the pipeline can produce.
-- Since absorb is now unconditionally sound, this predicate is not needed
-- for correctness proofs, but may be useful for performance analysis
-- (e.g., bounding formula tree growth for reachable formulas).
