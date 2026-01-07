{-# OPTIONS --safe --without-K #-}

-- Coalgebraic bisimilarity for step-based systems
--
-- Purpose: Define bisimilarity between two coalgebras with StepResult observations.
--
-- Key insight: This is WHERE the coinduction happens! StepResultBisim is finite,
-- but the coalgebra bisimilarity is coinductive because we need to relate
-- continuation states through all future observations.
--
-- This is the right notion of equivalence for our state machine vs coinductive LTL proof.

module Aletheia.LTL.CoalgebraBisim where

open import Aletheia.Prelude
open import Aletheia.LTL.Incremental using (StepResult)
open import Aletheia.LTL.StepResultBisim using (StepResultBisim)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- ============================================================================
-- COALGEBRA BISIMILARITY (Generic over state types)
-- ============================================================================

-- Two coalgebras are bisimilar if there exists a relation between their states
-- such that related states produce bisimilar observations (StepResult) for all frames.
--
-- The coinduction is in the 'relate' field: when both step results are Continue,
-- we require the continuation states to be related, which is a coinductive proof.
--
-- Parameters:
--   S1, S2 : State types of the two coalgebras
--   step1  : Step function for first coalgebra (returns StepResult S1)
--   step2  : Step function for second coalgebra (returns StepResult S2)
record CoalgebraBisim (S1 S2 : Set)
                      (step1 : S1 → TimedFrame → StepResult S1)
                      (step2 : S2 → TimedFrame → StepResult S2) : Set₁ where
  coinductive
  field
    -- The bisimulation relation between states
    relate : S1 → S2 → Set

    -- If states are related, their step results are bisimilar
    -- (using the relate relation for Continue states)
    step-bisim : ∀ {s1 : S1} {s2 : S2}
      → relate s1 s2
      → ∀ (f : TimedFrame)
      → StepResultBisim relate (step1 s1 f) (step2 s2 f)

-- ============================================================================
-- NOTES
-- ============================================================================

-- Why coinductive?
-- Because when step results are both Continue, we need to prove the continuation
-- states are related, which requires coinductive reasoning through infinite
-- future observations.

-- Why parameterized over S1 S2?
-- Because the state machine uses LTLEvalState, but the coinductive LTL
-- uses a different type (LTLProc, to be determined). They have different
-- internal representations but the same observable behavior.

-- Why StepResultBisim is parameterized by relate?
-- Because in the Continue case, StepResultBisim needs to check that continuation
-- states are related by the same bisimulation relation - creating the coinductive tie.
