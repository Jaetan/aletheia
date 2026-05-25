{-# OPTIONS --safe --without-K #-}

-- Verified iteration with early termination + completion tracking.
--
-- Purpose: Generic accumulator-based list traversal with halt + complete-with-
-- payload semantics.
-- Property: Implementation with reverse-accumulator ≡ forward specification.
-- Used by: Protocol.StreamState for property-list iteration.
--
-- Key design: No dependency on LTL, CAN, or any domain types.
-- This is pure structural list algebra.
--
-- Public API:
--   StepOutcome           — result of stepping one element
--   specResult            — canonical forward specification (survivor list)
--   specHalt              — canonical forward specification (halt evidence)
--   specCompletions       — canonical forward specification (completion payloads)
--   iterate               — implementation (accumulators hidden)
--   iterate-correct       — iterate ≡ (specResult , specHalt , specCompletions)
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

-- Result of stepping one element: advance with updated state, halt with
-- evidence, or complete with a per-completion payload that flows out of
-- the iterator alongside the survivor list.  Parametric over state type
-- S, halt-evidence E, and completion-payload C.
--
-- `complete` carries `C` (R23 — AGDA-D-12.1): when a property is decided
-- in favour of the user (its `stepL` returns Satisfied), the streaming
-- runtime drops it from the iteration list rather than re-evaluating it
-- on subsequent frames, and the caller-supplied payload (typically the
-- property's `Fin n` index) flows through `specCompletions` to the wire
-- so the binding can emit `PropertyResult.Satisfaction` at the frame
-- where the property completed.  Re-evaluating a Satisfied proc is
-- unsound for top-level Until/Release/Atomic shapes (concrete witness in
-- `Coalgebra/Properties.agda`'s comment block) — `complete` is the
-- structural fix; the payload is the diagnostic signal.
data StepOutcome (S E C : Set) : Set where
  advance  : S → StepOutcome S E C
  halt     : E → StepOutcome S E C
  complete : C → StepOutcome S E C

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
--   - Completion payloads are collected in source-order, halt-terminated

-- Spec result: what the survivor list should look like.
-- `complete _` drops the element (recurses without prepending).
specResult : {S E C : Set} → (S → StepOutcome S E C) → List S → List S
specResult step [] = []
specResult step (x ∷ xs) with step x
... | halt _     = x ∷ xs
... | advance x' = x' ∷ specResult step xs
... | complete _ = specResult step xs

-- Spec halt: first halt evidence encountered (if any).
-- `complete _` does not halt; recurses past the dropped element.
specHalt : {S E C : Set} → (S → StepOutcome S E C) → List S → Maybe E
specHalt step [] = nothing
specHalt step (x ∷ xs) with step x
... | halt e     = just e
... | advance _  = specHalt step xs
... | complete _ = specHalt step xs

-- Spec completions: completion payloads in source-order, terminated at
-- the first halt (the halt element itself contributes nothing, and
-- elements after halt are NOT stepped, so their payloads are excluded).
-- The dispatcher consumes this list to emit one `Satisfaction` wire
-- event per entry.
specCompletions : {S E C : Set} → (S → StepOutcome S E C) → List S → List C
specCompletions step [] = []
specCompletions step (x ∷ xs) with step x
... | halt _     = []
... | advance _  = specCompletions step xs
... | complete c = c ∷ specCompletions step xs

-- ============================================================================
-- IMPLEMENTATION (internal, reverse-accumulator)
-- ============================================================================

private
  -- Iteration with explicit accumulators (internal).  Processed survivors
  -- prepended to `acc` (in reverse); completion payloads prepended to
  -- `compAcc` (in reverse).  On halt: reconstructs full survivor list
  -- as `reverse acc ++ (halted ∷ remaining)` and reverses the completion
  -- accumulator.  On exhaustion: reverses both accumulators.
  iterateImpl : {S E C : Set} → (S → StepOutcome S E C)
              → List S → List S → List C → List S × Maybe E × List C
  iterateImpl step [] acc compAcc = (reverse acc , nothing , reverse compAcc)
  iterateImpl step (x ∷ xs) acc compAcc with step x
  ... | halt e     = (reverse acc ++ₗ (x ∷ xs) , just e , reverse compAcc)
  ... | advance x' = iterateImpl step xs (x' ∷ acc) compAcc
  ... | complete c = iterateImpl step xs acc (c ∷ compAcc)

-- ============================================================================
-- PUBLIC API
-- ============================================================================

-- Iterate over a list with early termination on halt + completion tracking.
-- Returns (survivor list, halt evidence if any, completion payloads in source-order).
iterate : {S E C : Set} → (S → StepOutcome S E C) → List S → List S × Maybe E × List C
iterate step props = iterateImpl step props [] []

-- ============================================================================
-- EQUIVALENCE PROOF (internal machinery + public theorem)
-- ============================================================================
--
-- Strategy: Generalize over arbitrary survivor + completion accumulators,
-- then specialize to ([] , []).
--
-- The generalized invariant states that at any point in the iteration,
-- the accumulated survivor prefix (reversed) followed by the spec result
-- of the remaining elements gives the correct survivor output, AND the
-- accumulated completion prefix (reversed) followed by the spec
-- completions of the remaining elements gives the correct completion
-- output.
--
-- List algebra needed (all from stdlib):
--   unfold-reverse : reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
--   ++-assoc       : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
--   ++-identityʳ   : xs ++ [] ≡ xs

private
  -- Local cong₂ — stdlib's lives in a different module path and the
  -- Properties.PropositionalEquality.cong₂ takes a different signature
  -- (≡-by-≡ on a parameterised function); the local form below
  -- pattern-matches both refl arguments and stays inside
  -- ≡-without-K reasoning.
  cong₂' : ∀ {A B Z : Set} (f : A → B → Z) {a a' : A} {b b' : B}
        → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂' f refl refl = refl

  -- Generalized lemma: with any survivor + completion accumulator prefix.
  iterate-equiv : ∀ {S E C : Set} (step : S → StepOutcome S E C)
    (props : List S) (acc : List S) (compAcc : List C)
    → iterateImpl step props acc compAcc ≡
        (reverse acc ++ₗ specResult step props
        , specHalt step props
        , reverse compAcc ++ₗ specCompletions step props)
  iterate-equiv step [] acc compAcc =
    cong₂' (λ ys cs → (ys , nothing , cs))
           (sym (++-identityʳ (reverse acc)))
           (sym (++-identityʳ (reverse compAcc)))
  iterate-equiv step (x ∷ xs) acc compAcc with step x
  ... | halt e     =
    -- LHS: (reverse acc ++ₗ (x ∷ xs) , just e , reverse compAcc)
    -- RHS: (reverse acc ++ₗ (x ∷ xs) , just e , reverse compAcc ++ₗ [])
    -- Bridge the third component via ++-identityʳ.
    cong (λ cs → (reverse acc ++ₗ (x ∷ xs) , just e , cs))
         (sym (++-identityʳ (reverse compAcc)))
  ... | advance x' =
    trans (iterate-equiv step xs (x' ∷ acc) compAcc)
          (cong (λ ys → (ys , specHalt step xs , reverse compAcc ++ₗ specCompletions step xs))
                (trans (cong (_++ₗ specResult step xs) (unfold-reverse x' acc))
                       (++-assoc (reverse acc) (x' ∷ []) (specResult step xs))))
  ... | complete c =
    trans (iterate-equiv step xs acc (c ∷ compAcc))
          (cong (λ cs → (reverse acc ++ₗ specResult step xs , specHalt step xs , cs))
                (trans (cong (_++ₗ specCompletions step xs) (unfold-reverse c compAcc))
                       (++-assoc (reverse compAcc) (c ∷ []) (specCompletions step xs))))

-- Main theorem: iterate ≡ (specResult , specHalt , specCompletions).
-- At ([] , []), both `reverse [] ++ specResult` and `reverse [] ++
-- specCompletions` reduce by computation.
iterate-correct : ∀ {S E C : Set} (step : S → StepOutcome S E C)
  (props : List S)
  → iterate step props ≡
      (specResult step props , specHalt step props , specCompletions step props)
iterate-correct step props = iterate-equiv step props [] []

-- ============================================================================
-- ACTIVE-SET MONOTONICITY (AGDA-B-9.2 closure)
-- ============================================================================
--
-- The post-iteration survivor list is no longer than the input.  `halt`
-- keeps the list (re-emits `x ∷ xs`); `advance` keeps the list one-for-one
-- (replaces `x` with `x'`); `complete _` shrinks the list by one (drops
-- `x`).  The streaming runtime relies on this to argue that re-evaluating
-- the active set on subsequent frames cannot grow without explicit user
-- input.
length-specResult-≤ : ∀ {S E C : Set} (step : S → StepOutcome S E C) (props : List S)
  → length (specResult step props) ≤ length props
length-specResult-≤ step [] = z≤n
length-specResult-≤ step (x ∷ xs) with step x
... | halt _     = ≤-refl
... | advance _  = s≤s (length-specResult-≤ step xs)
... | complete _ = m≤n⇒m≤1+n (length-specResult-≤ step xs)
