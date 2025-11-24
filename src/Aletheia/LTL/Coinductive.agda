{-# OPTIONS --without-K --guardedness --sized-types #-}

-- NOTE: This module uses --sized-types which is incompatible with --safe.
-- All other Aletheia modules remain --safe --without-K.
-- This module is isolated to contain the unsafe boundary.

module Aletheia.LTL.Coinductive where

open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤ᵇ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _++_)
open import Data.Nat.Show using (show)

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.Trace.Context using (timestamp)
open import Aletheia.LTL.Incremental using (CheckResult; Pass; Fail; Counterexample; mkCounterexample)

-- ============================================================================
-- LTL CHECKER STATE MACHINES
-- ============================================================================

-- Each LTL operator has a state that tracks progress through the trace.
-- States support:
--   - update: process next frame
--   - earlyDecision: can we decide now?
--   - finalDecision: what to return at EOF (with last frame for infinite extension)

-- State for atomic/simple predicates
record AtomicState : Set where
  constructor mkAtomicState
  field
    result : Bool

-- State for Always: all frames so far satisfy predicate
record AlwaysState : Set where
  constructor mkAlwaysState
  field
    allSatisfy : Bool

-- State for Eventually: some frame satisfied predicate
record EventuallyState : Set where
  constructor mkEventuallyState
  field
    someSatisfied : Bool

-- State for Until: φ held so far, waiting for ψ
record UntilState : Set where
  constructor mkUntilState
  field
    phiHolds : Bool      -- φ held on all frames so far
    psiFound : Bool      -- ψ was found

-- State for bounded operators (within time window)
record BoundedState : Set where
  constructor mkBoundedState
  field
    startTime : ℕ
    window : ℕ
    satisfied : Bool     -- for Eventually: found one
    allSatisfy : Bool    -- for Always: all in window satisfy

-- ============================================================================
-- PREDICATE EVALUATION
-- ============================================================================

-- Evaluate a formula at a single frame (for atomic predicates only)
evalAtFrame : TimedFrame → LTL (TimedFrame → Bool) → Bool
evalAtFrame tf (Atomic pred) = pred tf
evalAtFrame tf (Not ψ) = not (evalAtFrame tf ψ)
evalAtFrame tf (And ψ₁ ψ₂) = evalAtFrame tf ψ₁ ∧ evalAtFrame tf ψ₂
evalAtFrame tf (Or ψ₁ ψ₂) = evalAtFrame tf ψ₁ ∨ evalAtFrame tf ψ₂
evalAtFrame _ _ = true  -- Temporal operators handled by state machine

-- ============================================================================
-- COINDUCTIVE LTL CHECKER
-- ============================================================================

-- Main checker: processes colist, returns delayed result
-- Uses infinite extension semantics: last frame repeats forever at EOF

checkColist : ∀ {i : Size}
            → LTL (TimedFrame → Bool)
            → Colist TimedFrame i
            → Delay Bool i

-- Handle empty trace
checkColist φ [] = now true  -- Empty trace, vacuously true

-- Non-empty trace: use state machine approach
checkColist φ (frame ∷ rest) = later λ where .force → go φ frame (rest .force)
  where
    -- Recursive checker: takes current frame and forced tail
    go : ∀ {i : Size}
       → LTL (TimedFrame → Bool)
       → TimedFrame
       → Colist TimedFrame i
       → Delay Bool i

    -- Atomic: just evaluate on last frame
    go (Atomic pred) frame [] = now (pred frame)
    go (Atomic pred) frame (next ∷ rest') =
      later λ where .force → go (Atomic pred) next (rest' .force)

    -- Not: negate result
    go (Not ψ) frame colist = Delay.map not (go ψ frame colist)
      where import Codata.Sized.Delay as Delay

    -- And: check both (short-circuit on false)
    go (And ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
    go (And ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
        then (later λ where .force → go (And ψ₁ ψ₂) next (rest' .force))
        else now false

    -- Or: check either (short-circuit on true)
    go (Or ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂)
    go (Or ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂
        then now true
        else (later λ where .force → go (Or ψ₁ ψ₂) next (rest' .force))

    -- Next: check next frame (infinite extension: next is same frame at EOF)
    go (Next ψ) frame [] = now (evalAtFrame frame ψ)
    go (Next ψ) frame (next ∷ rest') =
      later λ where .force → go ψ next (rest' .force)

    -- Always: all frames must satisfy (early termination on failure)
    go (Always ψ) frame [] = now (evalAtFrame frame ψ)
    go (Always ψ) frame (next ∷ rest') =
      if evalAtFrame frame ψ
        then (later λ where .force → go (Always ψ) next (rest' .force))
        else now false

    -- Eventually: some frame must satisfy (early termination on success)
    go (Eventually ψ) frame [] = now (evalAtFrame frame ψ)
    go (Eventually ψ) frame (next ∷ rest') =
      if evalAtFrame frame ψ
        then now true
        else (later λ where .force → go (Eventually ψ) next (rest' .force))

    -- Until: ψ₁ holds until ψ₂ (need ψ₂ to eventually hold)
    go (Until ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₂)
    go (Until ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₂
        then now true
        else if evalAtFrame frame ψ₁
             then (later λ where .force → go (Until ψ₁ ψ₂) next (rest' .force))
             else now false

    -- EventuallyWithin: must satisfy within time window
    go (EventuallyWithin window ψ) frame colist = goEW (timestamp frame) frame colist
      where
        goEW : ∀ {i : Size} → ℕ → TimedFrame → Colist TimedFrame i → Delay Bool i
        goEW start frame [] =
          now (((timestamp frame ∸ start) ≤ᵇ window) ∧ evalAtFrame frame ψ)
        goEW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then now true
                    else (later λ where .force → goEW start next (rest' .force)))
            else now false

    -- AlwaysWithin: must satisfy throughout time window
    go (AlwaysWithin window ψ) frame colist = goAW (timestamp frame) frame colist
      where
        goAW : ∀ {i : Size} → ℕ → TimedFrame → Colist TimedFrame i → Delay Bool i
        goAW start frame [] =
          now (not ((timestamp frame ∸ start) ≤ᵇ window) ∨ evalAtFrame frame ψ)
        goAW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then (later λ where .force → goAW start next (rest' .force))
                    else now false)
            else now true

-- ============================================================================
-- COINDUCTIVE LTL CHECKER WITH COUNTEREXAMPLES
-- ============================================================================

-- Main checker with counterexample generation
checkColistCE : ∀ {i : Size}
              → LTL (TimedFrame → Bool)
              → Colist TimedFrame i
              → Delay CheckResult i

-- Handle empty trace
checkColistCE φ [] = now Pass  -- Empty trace, vacuously true

-- Non-empty trace
checkColistCE φ (frame ∷ rest) = later λ where .force → go φ frame (rest .force)
  where
    -- Helper to create failure result
    fail : TimedFrame → String → Delay CheckResult ∞
    fail tf reason = now (Fail (mkCounterexample tf reason))

    -- Recursive checker with counterexample tracking
    go : ∀ {i : Size}
       → LTL (TimedFrame → Bool)
       → TimedFrame
       → Colist TimedFrame i
       → Delay CheckResult i

    -- Atomic: just evaluate on last frame
    go (Atomic pred) frame [] =
      if pred frame then now Pass
      else now (Fail (mkCounterexample frame "Atomic predicate failed"))
    go (Atomic pred) frame (next ∷ rest') =
      later λ where .force → go (Atomic pred) next (rest' .force)

    -- Not: negate result (swap Pass/Fail)
    go (Not ψ) frame colist = Delay.map negate (go ψ frame colist)
      where
        import Codata.Sized.Delay as Delay
        negate : CheckResult → CheckResult
        negate Pass = Fail (mkCounterexample frame "Negation: inner formula passed")
        negate (Fail _) = Pass

    -- And: check both (short-circuit on false)
    go (And ψ₁ ψ₂) frame [] =
      if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂ then now Pass
      else now (Fail (mkCounterexample frame "And: conjunct failed at end of trace"))
    go (And ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
        then (later λ where .force → go (And ψ₁ ψ₂) next (rest' .force))
        else now (Fail (mkCounterexample frame "And: conjunct failed"))

    -- Or: check either (short-circuit on true)
    go (Or ψ₁ ψ₂) frame [] =
      if evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂ then now Pass
      else now (Fail (mkCounterexample frame "Or: both disjuncts failed at end of trace"))
    go (Or ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂
        then now Pass
        else (later λ where .force → go (Or ψ₁ ψ₂) next (rest' .force))

    -- Next: check next frame
    go (Next ψ) frame [] =
      if evalAtFrame frame ψ then now Pass
      else now (Fail (mkCounterexample frame "Next: predicate failed at end of trace"))
    go (Next ψ) frame (next ∷ rest') =
      later λ where .force → go ψ next (rest' .force)

    -- Always: all frames must satisfy (early termination on failure)
    go (Always ψ) frame [] =
      if evalAtFrame frame ψ then now Pass
      else now (Fail (mkCounterexample frame "Always: predicate failed at end of trace"))
    go (Always ψ) frame (next ∷ rest') =
      if evalAtFrame frame ψ
        then (later λ where .force → go (Always ψ) next (rest' .force))
        else now (Fail (mkCounterexample frame "Always: predicate failed"))

    -- Eventually: some frame must satisfy (early termination on success)
    go (Eventually ψ) frame [] =
      if evalAtFrame frame ψ then now Pass
      else now (Fail (mkCounterexample frame "Eventually: predicate never satisfied"))
    go (Eventually ψ) frame (next ∷ rest') =
      if evalAtFrame frame ψ
        then now Pass
        else (later λ where .force → go (Eventually ψ) next (rest' .force))

    -- Until: ψ₁ holds until ψ₂
    go (Until ψ₁ ψ₂) frame [] =
      if evalAtFrame frame ψ₂ then now Pass
      else now (Fail (mkCounterexample frame "Until: ψ₂ never satisfied"))
    go (Until ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₂
        then now Pass
        else if evalAtFrame frame ψ₁
             then (later λ where .force → go (Until ψ₁ ψ₂) next (rest' .force))
             else now (Fail (mkCounterexample frame "Until: ψ₁ failed before ψ₂"))

    -- EventuallyWithin: must satisfy within time window
    go (EventuallyWithin window ψ) frame colist = goEW (timestamp frame) frame colist
      where
        goEW : ∀ {i : Size} → ℕ → TimedFrame → Colist TimedFrame i → Delay CheckResult i
        goEW start frame [] =
          if ((timestamp frame ∸ start) ≤ᵇ window) ∧ evalAtFrame frame ψ then now Pass
          else now (Fail (mkCounterexample frame ("EventuallyWithin: not satisfied within " ++ show window ++ "ms")))
        goEW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then now Pass
                    else (later λ where .force → goEW start next (rest' .force)))
            else now (Fail (mkCounterexample frame ("EventuallyWithin: window of " ++ show window ++ "ms expired")))

    -- AlwaysWithin: must satisfy throughout time window
    go (AlwaysWithin window ψ) frame colist = goAW (timestamp frame) frame colist
      where
        goAW : ∀ {i : Size} → ℕ → TimedFrame → Colist TimedFrame i → Delay CheckResult i
        goAW start frame [] =
          if not ((timestamp frame ∸ start) ≤ᵇ window) ∨ evalAtFrame frame ψ then now Pass
          else now (Fail (mkCounterexample frame ("AlwaysWithin: failed within " ++ show window ++ "ms window")))
        goAW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then (later λ where .force → goAW start next (rest' .force))
                    else now (Fail (mkCounterexample frame ("AlwaysWithin: failed at t=" ++ show (timestamp frame)))))
            else now Pass

-- ============================================================================
-- PUBLIC API
-- ============================================================================

-- Check LTL property on a stream (coinductive input/output)
checkProperty : LTL (TimedFrame → Bool) → Colist TimedFrame ∞ → Delay Bool ∞
checkProperty = checkColist

-- Check with counterexample generation (coinductive input/output)
checkPropertyWithCE : LTL (TimedFrame → Bool) → Colist TimedFrame ∞ → Delay CheckResult ∞
checkPropertyWithCE = checkColistCE
