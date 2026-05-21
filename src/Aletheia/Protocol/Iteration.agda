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
--   StepOutcome           — result of stepping one element
--   specResult            — canonical forward specification (result list)
--   specHalt              — canonical forward specification (halt evidence)
--   iterate               — implementation (accumulator hidden)
--   iterate-correct       — iterate ≡ (specResult , specHalt)
--   length-specResult-≤   — active set monotonically shrinks (used by
--                           the streaming runtime to close the
--                           classifyStepResult Satisfied → complete soundness gap)

module Aletheia.Protocol.Iteration where

open import Data.List using (List; []; _∷_; reverse; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

-- ============================================================================
-- STEP OUTCOME
-- ============================================================================

-- Result of stepping one element: either advance with updated state,
-- halt with evidence, or complete (drop the element from the active set).
-- Parametric over state type S and evidence type E.
--
-- `complete` is parameterless by design: when a property is decided in
-- favour of the user (its `stepL` returns Satisfied), the streaming
-- runtime drops it from the iteration list rather than re-evaluating it
-- on subsequent frames.  Re-evaluating a Satisfied proc is unsound for
-- top-level Until/Release/Atomic shapes (concrete witness in
-- `Coalgebra/Properties.agda`'s comment block) — `complete` is the
-- structural fix.  No `S` payload because the dropped state doesn't flow
-- anywhere downstream; "which property completed" is not surfaced on the
-- wire today (a future enhancement could add `Satisfaction` emission via
-- `dispatchIterResult`, mirroring `PropertyResult.Satisfaction` already
-- emitted at EndStream).
data StepOutcome (S E : Set) : Set where
  advance  : S → StepOutcome S E
  halt     : E → StepOutcome S E
  complete : StepOutcome S E

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
-- `complete` drops the element (recurses without prepending).
specResult : {S E : Set} → (S → StepOutcome S E) → List S → List S
specResult step [] = []
specResult step (x ∷ xs) with step x
... | halt _     = x ∷ xs
... | advance x' = x' ∷ specResult step xs
... | complete   = specResult step xs

-- Spec halt: first halt evidence encountered (if any).
-- `complete` does not halt; recurses past the dropped element.
specHalt : {S E : Set} → (S → StepOutcome S E) → List S → Maybe E
specHalt step [] = nothing
specHalt step (x ∷ xs) with step x
... | halt e     = just e
... | advance _  = specHalt step xs
... | complete   = specHalt step xs

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
  ... | complete   = iterateImpl step xs acc

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
  ... | complete   = iterate-equiv step xs acc

-- Main theorem: iterate ≡ (specResult , specHalt).
-- At acc = [], reverse [] ++ specResult reduces to specResult by computation.
iterate-correct : ∀ {S E : Set} (step : S → StepOutcome S E)
  (props : List S)
  → iterate step props ≡ (specResult step props , specHalt step props)
iterate-correct step props = iterate-equiv step props []

-- ============================================================================
-- ACTIVE-SET MONOTONICITY (AGDA-B-9.2 closure)
-- ============================================================================
--
-- The post-iteration list is no longer than the input.  `halt` keeps the
-- list (re-emits `x ∷ xs`); `advance` keeps the list one-for-one (replaces
-- `x` with `x'`); `complete` shrinks the list by one (drops `x`).  The
-- streaming runtime relies on this to argue that re-evaluating the active
-- set on subsequent frames cannot grow without explicit user input.
length-specResult-≤ : ∀ {S E : Set} (step : S → StepOutcome S E) (props : List S)
  → length (specResult step props) ≤ length props
length-specResult-≤ step [] = z≤n
length-specResult-≤ step (x ∷ xs) with step x
... | halt _     = ≤-refl
... | advance _  = s≤s (length-specResult-≤ step xs)
... | complete   = m≤n⇒m≤1+n (length-specResult-≤ step xs)
