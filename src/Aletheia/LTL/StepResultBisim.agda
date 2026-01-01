{-# OPTIONS --safe --without-K #-}

-- Bisimilarity for StepResult observations
--
-- Purpose: Define behavioral equivalence for StepResult observations
-- from different coalgebras (monitor vs defunctionalized LTL).
--
-- Key insight: StepResult is a simple finite data type, not coinductive.
-- Bisimilarity here is structural matching of observations, parameterized
-- by a relation R that relates continuation states.
--
-- This avoids extended lambda equality - we only compare observable behavior!

module Aletheia.LTL.StepResultBisim where

open import Aletheia.Prelude
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.Trace.Context using (TimedFrame)

-- ============================================================================
-- COUNTEREXAMPLE EQUIVALENCE
-- ============================================================================

-- Two counterexamples are equivalent if they refer to the same frame
-- and have the same reason string
record CounterexampleEquiv (ce1 ce2 : Counterexample) : Set where
  constructor mkCEEquiv
  field
    frame-eq : Counterexample.violatingFrame ce1 ≡ Counterexample.violatingFrame ce2
    reason-eq : Counterexample.reason ce1 ≡ Counterexample.reason ce2

-- Reflexivity for counterexample equivalence
ceEquiv-refl : ∀ (ce : Counterexample) → CounterexampleEquiv ce ce
ceEquiv-refl ce = mkCEEquiv refl refl

-- ============================================================================
-- STEPRESULT BISIMILARITY (Generic over two state types)
-- ============================================================================

-- Two StepResults are bisimilar if they have the same observable structure
-- and their continuation states are related by a given relation.
--
-- Note: This is NOT coinductive! StepResult is a finite observation.
-- The coinduction happens at the coalgebra level (for Continue states).
--
-- Parameters:
--   S1, S2 : State types for the two coalgebras
--   R : Relation between S1 and S2 (the coalgebra bisimilarity relation)
data StepResultBisim {S1 S2 : Set} (R : S1 → S2 → Set)
                     : StepResult S1 → StepResult S2 → Set where

  -- Both violated with equivalent counterexamples
  violated-bisim : ∀ {ce1 ce2 : Counterexample}
    → CounterexampleEquiv ce1 ce2
    → StepResultBisim R (Violated ce1) (Violated ce2)

  -- Both satisfied (no additional data to compare)
  satisfied-bisim : StepResultBisim R Satisfied Satisfied

  -- Both continue with related states
  -- The states s1 : S1 and s2 : S2 must be related by R
  continue-bisim : ∀ {s1 : S1} {s2 : S2}
    → R s1 s2
    → StepResultBisim R (Continue s1) (Continue s2)

-- ============================================================================
-- BASIC PROPERTIES
-- ============================================================================

-- Reflexivity: Every StepResult is bisimilar to itself
-- (when using propositional equality as the relation)
stepResult-refl : ∀ {S : Set} (sr : StepResult S) → StepResultBisim _≡_ sr sr
stepResult-refl (Violated ce) = violated-bisim (ceEquiv-refl ce)
stepResult-refl Satisfied = satisfied-bisim
stepResult-refl (Continue s) = continue-bisim refl

-- Note: Symmetry and transitivity can be proven but are not needed for the main proof.
