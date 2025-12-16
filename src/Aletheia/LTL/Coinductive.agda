{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Coinductive LTL semantics over infinite traces (DelayedColist).
--
-- Purpose: Define LTL evaluation for potentially infinite traces with proper productivity.
-- Semantics: Standard LTL semantics (Always = forall frames, Eventually = exists frame, etc.).
-- Role: Formal semantics foundation; Incremental checker approximates this for finite traces.
--
-- Design: Uses DelayedColist for infinite traces, guardedness ensures productivity.
-- NOTE: Uses --sized-types which is incompatible with --safe.
module Aletheia.LTL.Coinductive where

open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤ᵇ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Nat.Show using (show)

open import Aletheia.LTL.Syntax
open import Aletheia.LTL.Evaluation using () renaming (evalAtFrame to evalAtFrameWith)
open import Aletheia.Trace.CANTrace using (TimedFrame)
-- Prelude not currently needed (previously used case_of_)
open import Aletheia.Trace.Context using (timestamp)
open import Aletheia.LTL.Incremental using (CheckResult; Pass; Fail; Counterexample; mkCounterexample)
open import Aletheia.DBC.Types using (DBC)
open import Data.Product using (_,_)
open import Aletheia.Data.DelayedColist using (DelayedColist) renaming (later to wait)
open Aletheia.Data.DelayedColist

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
-- Temporal operators return true (handled by state machine elsewhere)
-- Delegates to LTL.Evaluation.evalAtFrame with temporalDefault=true
evalAtFrame : TimedFrame → LTL (TimedFrame → Bool) → Bool
evalAtFrame = evalAtFrameWith true

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
          else now (Fail (mkCounterexample frame ("EventuallyWithin: not satisfied within " ++ₛ show window ++ₛ "ms")))
        goEW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then now Pass
                    else (later λ where .force → goEW start next (rest' .force)))
            else now (Fail (mkCounterexample frame ("EventuallyWithin: window of " ++ₛ show window ++ₛ "ms expired")))

    -- AlwaysWithin: must satisfy throughout time window
    go (AlwaysWithin window ψ) frame colist = goAW (timestamp frame) frame colist
      where
        goAW : ∀ {i : Size} → ℕ → TimedFrame → Colist TimedFrame i → Delay CheckResult i
        goAW start frame [] =
          if not ((timestamp frame ∸ start) ≤ᵇ window) ∨ evalAtFrame frame ψ then now Pass
          else now (Fail (mkCounterexample frame ("AlwaysWithin: failed within " ++ₛ show window ++ₛ "ms window")))
        goAW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then (later λ where .force → goAW start next (rest' .force))
                    else now (Fail (mkCounterexample frame ("AlwaysWithin: failed at t=" ++ₛ show (timestamp frame)))))
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

-- ============================================================================
-- DELAYED COLIST CHECKERS
-- ============================================================================

-- Check LTL property on a delayed stream
-- The 'wait' constructors in input become 'later' in output
checkDelayedColist : ∀ {i : Size}
                   → LTL (TimedFrame → Bool)
                   → DelayedColist TimedFrame i
                   → Delay Bool i
checkDelayedColist φ [] = now true
checkDelayedColist φ (wait rest) = later λ where .force → checkDelayedColist φ (rest .force)
checkDelayedColist φ (frame ∷ rest) = later λ where .force → goDelayed φ frame (rest .force)
  where
    -- Recursive checker for delayed colist
    goDelayed : ∀ {i : Size}
              → LTL (TimedFrame → Bool)
              → TimedFrame
              → DelayedColist TimedFrame i
              → Delay Bool i

    goDelayed (Atomic pred) frame [] = now (pred frame)
    goDelayed (Atomic pred) frame (wait rest) = later λ where .force → goDelayed (Atomic pred) frame (rest .force)
    goDelayed (Atomic pred) frame (next ∷ rest') = later λ where .force → goDelayed (Atomic pred) next (rest' .force)

    goDelayed (Not ψ) frame dc = Delay.map not (goDelayed ψ frame dc)
      where import Codata.Sized.Delay as Delay

    goDelayed (And ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂)
    goDelayed (And ψ₁ ψ₂) frame (wait rest) = later λ where .force → goDelayed (And ψ₁ ψ₂) frame (rest .force)
    goDelayed (And ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₁ ∧ evalAtFrame frame ψ₂
        then (later λ where .force → goDelayed (And ψ₁ ψ₂) next (rest' .force))
        else now false

    goDelayed (Or ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂)
    goDelayed (Or ψ₁ ψ₂) frame (wait rest) = later λ where .force → goDelayed (Or ψ₁ ψ₂) frame (rest .force)
    goDelayed (Or ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₁ ∨ evalAtFrame frame ψ₂
        then now true
        else (later λ where .force → goDelayed (Or ψ₁ ψ₂) next (rest' .force))

    goDelayed (Next ψ) frame [] = now (evalAtFrame frame ψ)
    goDelayed (Next ψ) frame (wait rest) = later λ where .force → goDelayed (Next ψ) frame (rest .force)
    goDelayed (Next ψ) frame (next ∷ rest') = later λ where .force → goDelayed ψ next (rest' .force)

    goDelayed (Always ψ) frame [] = now (evalAtFrame frame ψ)
    goDelayed (Always ψ) frame (wait rest) = later λ where .force → goDelayed (Always ψ) frame (rest .force)
    goDelayed (Always ψ) frame (next ∷ rest') =
      if evalAtFrame frame ψ
        then (later λ where .force → goDelayed (Always ψ) next (rest' .force))
        else now false

    goDelayed (Eventually ψ) frame [] = now (evalAtFrame frame ψ)
    goDelayed (Eventually ψ) frame (wait rest) = later λ where .force → goDelayed (Eventually ψ) frame (rest .force)
    goDelayed (Eventually ψ) frame (next ∷ rest') =
      if evalAtFrame frame ψ
        then now true
        else (later λ where .force → goDelayed (Eventually ψ) next (rest' .force))

    goDelayed (Until ψ₁ ψ₂) frame [] = now (evalAtFrame frame ψ₂)
    goDelayed (Until ψ₁ ψ₂) frame (wait rest) = later λ where .force → goDelayed (Until ψ₁ ψ₂) frame (rest .force)
    goDelayed (Until ψ₁ ψ₂) frame (next ∷ rest') =
      if evalAtFrame frame ψ₂
        then now true
        else if evalAtFrame frame ψ₁
             then (later λ where .force → goDelayed (Until ψ₁ ψ₂) next (rest' .force))
             else now false

    goDelayed (EventuallyWithin window ψ) frame dc = goEW (timestamp frame) frame dc
      where
        goEW : ∀ {i : Size} → ℕ → TimedFrame → DelayedColist TimedFrame i → Delay Bool i
        goEW start frame [] = now (((timestamp frame ∸ start) ≤ᵇ window) ∧ evalAtFrame frame ψ)
        goEW start frame (wait rest) = later λ where .force → goEW start frame (rest .force)
        goEW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then now true
                    else (later λ where .force → goEW start next (rest' .force)))
            else now false

    goDelayed (AlwaysWithin window ψ) frame dc = goAW (timestamp frame) frame dc
      where
        goAW : ∀ {i : Size} → ℕ → TimedFrame → DelayedColist TimedFrame i → Delay Bool i
        goAW start frame [] = now (not ((timestamp frame ∸ start) ≤ᵇ window) ∨ evalAtFrame frame ψ)
        goAW start frame (wait rest) = later λ where .force → goAW start frame (rest .force)
        goAW start frame (next ∷ rest') =
          if (timestamp frame ∸ start) ≤ᵇ window
            then (if evalAtFrame frame ψ
                    then (later λ where .force → goAW start next (rest' .force))
                    else now false)
            else now true

-- Public API for delayed streams
checkDelayedProperty : LTL (TimedFrame → Bool) → DelayedColist TimedFrame ∞ → Delay Bool ∞
checkDelayedProperty = checkDelayedColist

-- ============================================================================
-- STREAMING SIGNAL PREDICATE CHECKER
-- ============================================================================

-- Import the stateful predicate evaluator
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; evalPredicateWithPrev)

-- Check LTL SignalPredicate formula on a delayed stream
-- Threads previous frame through for ChangedBy predicates
checkSignalPredicateStream : ∀ {i : Size}
                           → DBC
                           → LTL SignalPredicate
                           → DelayedColist TimedFrame i
                           → Delay Bool i
checkSignalPredicateStream dbc formula stream = go nothing formula stream
  where
    -- Eval SignalPredicate on a frame
    evalPred : Maybe TimedFrame → SignalPredicate → TimedFrame → Bool
    evalPred prev pred frame = evalPredicateWithPrev dbc prev pred frame

    -- Evaluate LTL formula at a frame (for operators like And, Or)
    evalFormula : Maybe TimedFrame → LTL SignalPredicate → TimedFrame → Bool
    evalFormula prev (Atomic pred) frame = evalPred prev pred frame
    evalFormula prev (Not ψ) frame = not (evalFormula prev ψ frame)
    evalFormula prev (And ψ₁ ψ₂) frame = evalFormula prev ψ₁ frame ∧ evalFormula prev ψ₂ frame
    evalFormula prev (Or ψ₁ ψ₂) frame = evalFormula prev ψ₁ frame ∨ evalFormula prev ψ₂ frame
    evalFormula prev (Next ψ) frame = evalFormula prev ψ frame
    evalFormula prev (Always ψ) frame = evalFormula prev ψ frame
    evalFormula prev (Eventually ψ) frame = evalFormula prev ψ frame
    evalFormula prev (Until ψ₁ ψ₂) frame = evalFormula prev ψ₂ frame
    evalFormula prev (EventuallyWithin _ ψ) frame = evalFormula prev ψ frame
    evalFormula prev (AlwaysWithin _ ψ) frame = evalFormula prev ψ frame

    mutual
      -- Helper: threads previous frame through the stream
      go : ∀ {i : Size}
         → Maybe TimedFrame  -- previous frame (state)
         → LTL SignalPredicate
         → DelayedColist TimedFrame i
         → Delay Bool i
      go prev φ [] = now true
      go prev φ (wait rest) = later λ where .force → go prev φ (rest .force)
      go prev φ (frame ∷ rest) = later λ where .force → goFrame prev φ frame (rest .force)

      -- Process one frame with the formula
      goFrame : ∀ {i : Size}
              → Maybe TimedFrame
              → LTL SignalPredicate
              → TimedFrame
              → DelayedColist TimedFrame i
              → Delay Bool i

      goFrame prev (Atomic pred) frame stream = go (just frame) (Atomic pred) stream
      goFrame prev (Not ψ) frame stream = Delay.map not (goFrame prev ψ frame stream)
        where import Codata.Sized.Delay as Delay
      goFrame prev (And ψ₁ ψ₂) frame stream =
        if evalFormula prev (And ψ₁ ψ₂) frame
          then go (just frame) (And ψ₁ ψ₂) stream
          else now false
      goFrame prev (Or ψ₁ ψ₂) frame stream =
        if evalFormula prev (Or ψ₁ ψ₂) frame
          then now true
          else go (just frame) (Or ψ₁ ψ₂) stream
      goFrame prev (Next ψ) frame stream = go (just frame) ψ stream
      goFrame prev (Always ψ) frame stream =
        if evalFormula prev ψ frame
          then go (just frame) (Always ψ) stream
          else now false
      goFrame prev (Eventually ψ) frame stream =
        if evalFormula prev ψ frame
          then now true
          else go (just frame) (Eventually ψ) stream
      goFrame prev (Until ψ₁ ψ₂) frame stream =
        if evalFormula prev ψ₂ frame
          then now true
          else if evalFormula prev ψ₁ frame
               then go (just frame) (Until ψ₁ ψ₂) stream
               else now false
      goFrame prev (EventuallyWithin window ψ) frame stream = goEW (timestamp frame) prev ψ frame stream
        where
          goEW : ∀ {i : Size} → ℕ → Maybe TimedFrame → LTL SignalPredicate → TimedFrame → DelayedColist TimedFrame i → Delay Bool i
          goEW start prevFrame φ curFrame [] = now (((timestamp curFrame ∸ start) ≤ᵇ window) ∧ evalFormula prevFrame φ curFrame)
          goEW start prevFrame φ curFrame (wait rest) = later λ where .force → goEW start prevFrame φ curFrame (rest .force)
          goEW start prevFrame φ curFrame (next ∷ rest') =
            if (timestamp curFrame ∸ start) ≤ᵇ window
              then (if evalFormula prevFrame φ curFrame
                      then now true
                      else later λ where .force → goEW start (just curFrame) φ next (rest' .force))
              else now false
      goFrame prev (AlwaysWithin window ψ) frame stream = goAW (timestamp frame) prev ψ frame stream
        where
          goAW : ∀ {i : Size} → ℕ → Maybe TimedFrame → LTL SignalPredicate → TimedFrame → DelayedColist TimedFrame i → Delay Bool i
          goAW start prevFrame φ curFrame [] = now (not ((timestamp curFrame ∸ start) ≤ᵇ window) ∨ evalFormula prevFrame φ curFrame)
          goAW start prevFrame φ curFrame (wait rest) = later λ where .force → goAW start prevFrame φ curFrame (rest .force)
          goAW start prevFrame φ curFrame (next ∷ rest') =
            let inWindow = (timestamp curFrame ∸ start) ≤ᵇ window
                holds = evalFormula prevFrame φ curFrame
                continue = later λ where .force → goAW start (just curFrame) φ next (rest' .force)
            in if inWindow
               then (if holds then continue else now false)
               else now true

-- Public API for streaming SignalPredicate checking
checkStreamingProperty : DBC → LTL SignalPredicate → DelayedColist TimedFrame ∞ → Delay Bool ∞
checkStreamingProperty = checkSignalPredicateStream

-- ============================================================================
-- INCREMENTAL MULTI-PROPERTY CHECKER
-- ============================================================================

-- Import PropertyResult type from Protocol
open import Aletheia.Protocol.Response using (PropertyResult; Violation; Satisfaction; Pending; StreamComplete; CounterexampleData; mkCounterexampleData)
open import Data.List as List using (List; []; _∷_; filter; partition)
open import Data.List.Properties using ()
open import Data.Product using (_×_; _,_)

-- Check multiple properties incrementally on a delayed stream
-- Emits PropertyResult whenever a property is decided (violated/satisfied)
-- Removes decided properties from active set
checkAllPropertiesIncremental : ∀ {i : Size}
                              → DBC
                              → List (ℕ × LTL SignalPredicate)
                              → DelayedColist TimedFrame i
                              → DelayedColist PropertyResult i
checkAllPropertiesIncremental dbc properties stream = go nothing properties stream
  where
    -- Evaluate predicate on frame
    evalPred : Maybe TimedFrame → SignalPredicate → TimedFrame → Bool
    evalPred prev pred frame = evalPredicateWithPrev dbc prev pred frame

    -- Evaluate full formula on frame
    evalFormula : Maybe TimedFrame → LTL SignalPredicate → TimedFrame → Bool
    evalFormula prev (Atomic pred) frame = evalPred prev pred frame
    evalFormula prev (Not ψ) frame = not (evalFormula prev ψ frame)
    evalFormula prev (And ψ₁ ψ₂) frame = evalFormula prev ψ₁ frame ∧ evalFormula prev ψ₂ frame
    evalFormula prev (Or ψ₁ ψ₂) frame = evalFormula prev ψ₁ frame ∨ evalFormula prev ψ₂ frame
    evalFormula prev (Next ψ) frame = evalFormula prev ψ frame
    evalFormula prev (Always ψ) frame = evalFormula prev ψ frame
    evalFormula prev (Eventually ψ) frame = evalFormula prev ψ frame
    evalFormula prev (Until ψ₁ ψ₂) frame = evalFormula prev ψ₂ frame
    evalFormula prev (EventuallyWithin _ ψ) frame = evalFormula prev ψ frame
    evalFormula prev (AlwaysWithin _ ψ) frame = evalFormula prev ψ frame

    -- Check if a property can be decided early at current frame
    -- Returns: Just (True) = satisfied, Just (False) = violated, Nothing = still checking
    canDecideEarly : Maybe TimedFrame → LTL SignalPredicate → TimedFrame → Maybe Bool
    canDecideEarly prev (Atomic pred) frame =
      -- Atomic predicate decided on each frame, but doesn't terminate checking
      nothing
    canDecideEarly prev (Not ψ) frame = canDecideEarly prev ψ frame
    canDecideEarly prev (And ψ₁ ψ₂) frame with canDecideEarly prev ψ₁ frame
    ... | just false = just false  -- Can fail early if either conjunct fails
    ... | _ = canDecideEarly prev ψ₂ frame
    canDecideEarly prev (Or ψ₁ ψ₂) frame with canDecideEarly prev ψ₁ frame
    ... | just true = just true  -- Can succeed early if either disjunct succeeds
    ... | _ = canDecideEarly prev ψ₂ frame
    canDecideEarly prev (Always ψ) frame with evalFormula prev ψ frame
    ... | false = just false  -- Violation found - can decide immediately
    ... | true = nothing  -- Still holding - need more frames
    canDecideEarly prev (Eventually ψ) frame with evalFormula prev ψ frame
    ... | true = just true  -- Satisfaction found - can decide immediately
    ... | false = nothing  -- Not yet - need more frames
    canDecideEarly prev (Until ψ₁ ψ₂) frame with evalFormula prev ψ₂ frame
    ... | true = just true  -- ψ₂ satisfied - can decide immediately
    ... | false with evalFormula prev ψ₁ frame
    ...   | false = just false  -- ψ₁ failed before ψ₂ - violation
    ...   | true = nothing  -- Still waiting for ψ₂
    canDecideEarly prev _ frame = nothing  -- Other operators can't decide early

    -- Check each property and partition into decided/active
    checkProperties : Maybe TimedFrame
                    → List (ℕ × LTL SignalPredicate)
                    → TimedFrame
                    → (List PropertyResult × List (ℕ × LTL SignalPredicate))
    checkProperties prev [] frame = ([] , [])
    checkProperties prev ((idx , φ) ∷ rest) frame =
      let (decidedRest , activeRest) = checkProperties prev rest frame
      in aux decidedRest activeRest (canDecideEarly prev φ frame)
      where
        aux : List PropertyResult → List (ℕ × LTL SignalPredicate) → Maybe Bool → (List PropertyResult × List (ℕ × LTL SignalPredicate))
        aux decidedRest activeRest (just false) =
          let reason = "Property violated at t=" ++ₛ show (timestamp frame)
              ce = mkCounterexampleData (timestamp frame) reason
          in ((Violation idx ce) ∷ decidedRest , activeRest)
        aux decidedRest activeRest (just true) = ((Satisfaction idx) ∷ decidedRest , activeRest)
        aux decidedRest activeRest nothing = (decidedRest , (idx , φ) ∷ activeRest)

    -- Emit list of results to output stream
    emitResults : ∀ {i : Size} → List PropertyResult → DelayedColist PropertyResult i → DelayedColist PropertyResult i
    emitResults [] rest = rest
    emitResults (r ∷ rs) rest = r ∷ λ where .force → emitResults rs rest

    -- At EndStream: emit pending results for active properties
    emitPending : List (ℕ × LTL SignalPredicate) → Maybe TimedFrame → DelayedColist PropertyResult ∞
    emitPending [] prev = StreamComplete ∷ λ where .force → []
    emitPending ((idx , φ) ∷ rest) prev =
      let result = finalDecision prev φ
      in (Pending idx result) ∷ λ where .force → emitPending rest prev
      where
        -- Decide result based on finite prefix semantics
        finalDecision : Maybe TimedFrame → LTL SignalPredicate → Bool
        finalDecision prev (Always ψ) = true  -- No violations found
        finalDecision prev (Eventually ψ) = false  -- Never satisfied
        finalDecision prev (Until ψ₁ ψ₂) = false  -- ψ₂ never satisfied
        finalDecision prev _ = true  -- Other operators default to true

    mutual
      -- Main loop: process stream with active properties
      go : ∀ {i : Size}
         → Maybe TimedFrame  -- previous frame
         → List (ℕ × LTL SignalPredicate)  -- active properties
         → DelayedColist TimedFrame i
         → DelayedColist PropertyResult i
      go prev [] stream = emitPending [] prev  -- All properties decided
      go prev props [] = emitPending props prev  -- EndStream reached
      go prev props (wait rest) = wait λ where .force → go prev props (rest .force)
      go prev props (frame ∷ rest) = wait λ where .force → processFrame prev props frame (rest .force)

      -- Process one frame against all active properties
      processFrame : ∀ {i : Size}
                   → Maybe TimedFrame
                   → List (ℕ × LTL SignalPredicate)
                   → TimedFrame
                   → DelayedColist TimedFrame i
                   → DelayedColist PropertyResult i
      processFrame prev props frame rest =
        let (decided , stillActive) = checkProperties prev props frame
        in emitResults decided (go (just frame) stillActive rest)

-- Public API for incremental multi-property checking
checkAllPropertiesStream : DBC
                         → List (ℕ × LTL SignalPredicate)
                         → DelayedColist TimedFrame ∞
                         → DelayedColist PropertyResult ∞
checkAllPropertiesStream = checkAllPropertiesIncremental
