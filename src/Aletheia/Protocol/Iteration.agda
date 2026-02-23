{-# OPTIONS --safe --without-K #-}

-- Verified iteration with early termination.
--
-- Purpose: Generic accumulator-based list traversal with halt semantics.
-- Property: Implementation with reverse-accumulator ≡ forward specification.
-- Used by: Protocol.StreamState for property-list iteration.
--
-- Key design: No dependency on LTL, CAN, or any domain types.
-- This is pure structural list algebra.
--
-- Public API:
--   StepOutcome      — result of stepping one element
--   specResult       — canonical forward specification (result list)
--   specHalt         — canonical forward specification (halt evidence)
--   iterate          — implementation (accumulator hidden)
--   iterate-correct  — iterate ≡ (specResult , specHalt)

module Aletheia.Protocol.Iteration where

open import Data.List using (List; []; _∷_; reverse; _∷ʳ_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

-- ============================================================================
-- STEP OUTCOME
-- ============================================================================

-- Result of stepping one element: either advance with updated state,
-- or halt with evidence. Parametric over state type S and evidence type E.
data StepOutcome (S E : Set) : Set where
  advance : S → StepOutcome S E
  halt    : E → StepOutcome S E

-- ============================================================================
-- SPECIFICATION (forward-building, canonical)
-- ============================================================================
--
-- This is the mathematical model of what the iteration SHOULD do.
-- No accumulator, no reverse — just structural recursion building forward.
--
-- Properties that fall out for free from the definition:
--   - Each element is visited exactly once (structural recursion on input)
--   - No reordering (output built in same order as input)
--   - Elements before halt are stepped; halt element and rest are unchanged
--   - No duplication or skipping

-- Spec result: what the output list should look like.
specResult : {S E : Set} → (S → StepOutcome S E) → List S → List S
specResult step [] = []
specResult step (x ∷ xs) with step x
... | halt _     = x ∷ xs
... | advance x' = x' ∷ specResult step xs

-- Spec halt: first halt evidence encountered (if any).
specHalt : {S E : Set} → (S → StepOutcome S E) → List S → Maybe E
specHalt step [] = nothing
specHalt step (x ∷ xs) with step x
... | halt e     = just e
... | advance _  = specHalt step xs

-- ============================================================================
-- IMPLEMENTATION (internal, reverse-accumulator)
-- ============================================================================

private
  -- Iteration with explicit accumulator (internal).
  -- Processed elements prepended to acc (in reverse).
  -- On halt: reconstructs full list as reverse acc ++ (halted ∷ remaining).
  -- On completion: reverses accumulator.
  iterateImpl : {S E : Set} → (S → StepOutcome S E) → List S → List S → List S × Maybe E
  iterateImpl step [] acc = (reverse acc , nothing)
  iterateImpl step (x ∷ xs) acc with step x
  ... | halt e     = (reverse acc ++ₗ (x ∷ xs) , just e)
  ... | advance x' = iterateImpl step xs (x' ∷ acc)

-- ============================================================================
-- PUBLIC API
-- ============================================================================

-- Iterate over a list with early termination on halt.
-- Returns (updated list, halt evidence if any).
iterate : {S E : Set} → (S → StepOutcome S E) → List S → List S × Maybe E
iterate step props = iterateImpl step props []

-- ============================================================================
-- EQUIVALENCE PROOF (internal machinery + public theorem)
-- ============================================================================
--
-- Strategy: Generalize over an arbitrary accumulator, then specialize to [].
--
-- The generalized invariant states that at any point in the iteration,
-- the accumulated prefix (reversed) followed by the spec result of the
-- remaining elements gives the correct output.
--
-- List algebra needed (all from stdlib):
--   unfold-reverse : reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
--   ++-assoc       : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
--   ++-identityʳ   : xs ++ [] ≡ xs

private
  -- Generalized lemma: with any accumulator prefix.
  iterate-equiv : ∀ {S E : Set} (step : S → StepOutcome S E)
    (props : List S) (acc : List S)
    → iterateImpl step props acc ≡ (reverse acc ++ₗ specResult step props , specHalt step props)
  iterate-equiv step [] acc =
    cong (λ ys → (ys , nothing)) (sym (++-identityʳ (reverse acc)))
  iterate-equiv step (x ∷ xs) acc with step x
  ... | halt e     = refl
  ... | advance x' =
    trans (iterate-equiv step xs (x' ∷ acc))
          (cong (λ ys → (ys , specHalt step xs))
                (trans (cong (_++ₗ specResult step xs) (unfold-reverse x' acc))
                       (++-assoc (reverse acc) (x' ∷ []) (specResult step xs))))

-- Main theorem: iterate ≡ (specResult , specHalt).
-- At acc = [], reverse [] ++ specResult reduces to specResult by computation.
iterate-correct : ∀ {S E : Set} (step : S → StepOutcome S E)
  (props : List S)
  → iterate step props ≡ (specResult step props , specHalt step props)
iterate-correct step props = iterate-equiv step props []
