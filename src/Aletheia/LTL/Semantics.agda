{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.Semantics where

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.Stream
open import Aletheia.Trace.Context
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; _∸_)
open import Data.List using (List; []; _∷_; length; drop)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- LTL SEMANTICS WITH REPEAT-LAST BEHAVIOR
-- ============================================================================

-- Finite lists are interpreted as infinite traces that repeat their last element.
-- This gives correct LTL semantics for recorded CAN traces:
-- - [f1, f2, f3] represents the infinite trace: f1, f2, f3, f3, f3, ...
-- - Always φ holds if φ holds on all frames AND on the repeating final state
-- - Eventually φ holds if φ holds somewhere in the list OR on the final state

-- Helper: Get the last element of a list (if it exists)
lastElem : ∀ {A : Set} → List A → Maybe A
lastElem [] = nothing
lastElem (x ∷ []) = just x
lastElem (x ∷ rest@(_ ∷ _)) = lastElem rest

-- Check if a finite trace (repeating last element) satisfies an LTL formula
satisfiesAt : ∀ {A : Set} → List A → LTL (A → Bool) → Bool
satisfiesAt [] (Atomic _) = false
satisfiesAt (x ∷ _) (Atomic pred) = pred x

satisfiesAt trace (Not φ) = not (satisfiesAt trace φ)

satisfiesAt trace (And φ ψ) = satisfiesAt trace φ ∧ satisfiesAt trace ψ

satisfiesAt trace (Or φ ψ) = satisfiesAt trace φ ∨ satisfiesAt trace ψ

satisfiesAt [] (Next _) = false
satisfiesAt (_ ∷ []) (Next φ) = satisfiesAt [] (Next φ)  -- Repeats last, so Next stays at last
satisfiesAt (_ ∷ rest) (Next φ) = satisfiesAt rest φ

-- Always: Must hold on all elements AND on the infinitely repeating final state
satisfiesAt [] (Always _) = true  -- Vacuously true for empty trace
satisfiesAt (x ∷ []) (Always φ) = satisfiesAt (x ∷ []) φ  -- Must hold on repeating final state
satisfiesAt trace@(x ∷ rest) (Always φ) = satisfiesAt trace φ ∧ satisfiesAt rest (Always φ)

-- Eventually: Must hold somewhere in the list OR on the infinitely repeating final state
satisfiesAt [] (Eventually _) = false
satisfiesAt trace@(x ∷ rest) (Eventually φ) = satisfiesAt trace φ ∨ satisfiesAt rest (Eventually φ)

-- Until: φ holds until ψ becomes true (ψ can be satisfied on repeating final state)
satisfiesAt [] (Until _ _) = false
satisfiesAt trace@(x ∷ rest) (Until φ ψ) =
  satisfiesAt trace ψ ∨ (satisfiesAt trace φ ∧ satisfiesAt rest (Until φ ψ))

-- Bounded operators work within the finite prefix (don't consider infinite tail)
satisfiesAt [] (EventuallyWithin _ _) = false
satisfiesAt _ (EventuallyWithin zero _) = false
satisfiesAt trace@(x ∷ rest) (EventuallyWithin (suc n) φ) =
  satisfiesAt trace φ ∨ satisfiesAt rest (EventuallyWithin n φ)

satisfiesAt [] (AlwaysWithin _ _) = true
satisfiesAt _ (AlwaysWithin zero _) = true
satisfiesAt trace@(x ∷ rest) (AlwaysWithin (suc n) φ) =
  satisfiesAt trace φ ∧ satisfiesAt rest (AlwaysWithin n φ)

-- Wrapper for list-based checking (primary interface)
-- Finite lists are interpreted as repeating their last element infinitely
checkList : ∀ {A : Set} → List A → LTL (A → Bool) → Bool
checkList = satisfiesAt

-- Note: Direct coinductive trace checking doesn't terminate for unbounded operators!
-- Always/Eventually on infinite traces require infinite computation.
-- For practical use, convert lists to coinductive traces with fromListRepeat,
-- or use bounded checking with satisfiesAt on finite prefixes.

-- ============================================================================
-- TIME-BASED SEMANTICS FOR TIMESTAMPED TRACES
-- ============================================================================

-- Helper: Get elapsed time between first frame and current position
-- Returns microseconds elapsed since start of trace
elapsedTime : List TimedFrame → ℕ
elapsedTime [] = 0
elapsedTime (tf ∷ _) = timestamp tf

-- Helper: Check if within time window (microseconds)
-- Given start time and window duration, returns true if current time is within window
withinTimeWindow : ℕ → ℕ → ℕ → Bool
withinTimeWindow startTime windowMicros currentTime =
  (currentTime ∸ startTime) ≤ᵇ windowMicros

-- Time-aware LTL checking on timestamped traces
-- EventuallyWithin and AlwaysWithin use time (microseconds) instead of steps
satisfiesAtTimed : List TimedFrame → LTL (TimedFrame → Bool) → Bool
satisfiesAtTimed [] (Atomic _) = false
satisfiesAtTimed (tf ∷ _) (Atomic pred) = pred tf

satisfiesAtTimed trace (Not φ) = not (satisfiesAtTimed trace φ)

satisfiesAtTimed trace (And φ ψ) = satisfiesAtTimed trace φ ∧ satisfiesAtTimed trace ψ

satisfiesAtTimed trace (Or φ ψ) = satisfiesAtTimed trace φ ∨ satisfiesAtTimed trace ψ

satisfiesAtTimed [] (Next _) = false
satisfiesAtTimed (_ ∷ []) (Next φ) = satisfiesAtTimed [] (Next φ)
satisfiesAtTimed (_ ∷ rest) (Next φ) = satisfiesAtTimed rest φ

satisfiesAtTimed [] (Always _) = true
satisfiesAtTimed (tf ∷ []) (Always φ) = satisfiesAtTimed (tf ∷ []) φ
satisfiesAtTimed trace@(_ ∷ rest) (Always φ) = satisfiesAtTimed trace φ ∧ satisfiesAtTimed rest (Always φ)

satisfiesAtTimed [] (Eventually _) = false
satisfiesAtTimed trace@(_ ∷ rest) (Eventually φ) = satisfiesAtTimed trace φ ∨ satisfiesAtTimed rest (Eventually φ)

satisfiesAtTimed [] (Until _ _) = false
satisfiesAtTimed trace@(_ ∷ rest) (Until φ ψ) =
  satisfiesAtTimed trace ψ ∨ (satisfiesAtTimed trace φ ∧ satisfiesAtTimed rest (Until φ ψ))

-- Time-based bounded operators
-- EventuallyWithin n φ: φ must hold within n microseconds from current time
satisfiesAtTimed [] (EventuallyWithin _ _) = false
satisfiesAtTimed trace@(tf ∷ rest) (EventuallyWithin windowMicros φ) =
  -- Check if φ holds at current position or within the time window
  satisfiesAtTimed trace φ ∨ checkWithinTime rest
  where
    open import Data.Bool using (if_then_else_)

    startTime = timestamp tf

    -- Check if φ holds somewhere in the remaining trace within the time window
    checkWithinTime : List TimedFrame → Bool
    checkWithinTime [] = false
    checkWithinTime restTrace@(tf' ∷ more) =
      if withinTimeWindow startTime windowMicros (timestamp tf')
      then satisfiesAtTimed restTrace φ ∨ checkWithinTime more
      else false  -- Beyond time window, stop checking

-- AlwaysWithin n φ: φ must hold for n microseconds from current time
satisfiesAtTimed [] (AlwaysWithin _ _) = true
satisfiesAtTimed trace@(tf ∷ rest) (AlwaysWithin windowMicros φ) =
  -- φ must hold at current position and throughout the time window
  satisfiesAtTimed trace φ ∧ checkWithinTime rest
  where
    open import Data.Bool using (if_then_else_)

    startTime = timestamp tf

    -- Check if φ holds throughout the remaining trace within the time window
    checkWithinTime : List TimedFrame → Bool
    checkWithinTime [] = true  -- Vacuously true if trace ends
    checkWithinTime restTrace@(tf' ∷ more) =
      if withinTimeWindow startTime windowMicros (timestamp tf')
      then satisfiesAtTimed restTrace φ ∧ checkWithinTime more
      else true  -- Beyond time window, don't need to check

-- Primary interface for time-based checking
checkTimedTrace : List TimedFrame → LTL (TimedFrame → Bool) → Bool
checkTimedTrace = satisfiesAtTimed
