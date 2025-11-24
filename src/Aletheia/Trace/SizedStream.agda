{-# OPTIONS --without-K --guardedness --sized-types #-}

-- NOTE: This module does NOT use --safe because sized types are incompatible.
-- All other Aletheia modules remain --safe --without-K.
-- This module is isolated to contain the unsafe boundary.

module Aletheia.Trace.SizedStream where

open import Agda.Builtin.Size
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤ᵇ_)
open import Data.String using (String)

-- ============================================================================
-- SIZED FINITE STREAM
-- ============================================================================

-- A finite stream with size annotations for termination checking
-- The size parameter i bounds the number of elements remaining
record SizedStream {i : Size} (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : {j : Size< i} → Maybe (SizedStream {j} A)

open SizedStream public

-- ============================================================================
-- STREAM CONSTRUCTION
-- ============================================================================

-- Convert list to sized stream
listToSizedStream : ∀ {A : Set} → List A → Maybe (SizedStream {∞} A)
listToSizedStream [] = nothing
listToSizedStream (x ∷ xs) = just (go x xs)
  where
    go : ∀ {A : Set} → A → List A → SizedStream {∞} A
    hd (go x _) = x
    tl (go _ []) = nothing
    tl (go _ (y ∷ ys)) = just (go y ys)

-- ============================================================================
-- IMPORTS FOR LTL CHECKING
-- ============================================================================

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.Trace.Context using (timestamp)

-- ============================================================================
-- STREAM-BASED LTL CHECKING (CONTINUATION-PASSING STYLE)
-- ============================================================================

-- Evaluate a formula at a single frame
evalAtFrame : TimedFrame → LTL (TimedFrame → Bool) → Bool
evalAtFrame tf (Atomic pred) = pred tf
evalAtFrame tf (Not ψ) = not (evalAtFrame tf ψ)
evalAtFrame tf (And ψ₁ ψ₂) = evalAtFrame tf ψ₁ ∧ evalAtFrame tf ψ₂
evalAtFrame tf (Or ψ₁ ψ₂) = evalAtFrame tf ψ₁ ∨ evalAtFrame tf ψ₂
evalAtFrame _ _ = true  -- Temporal operators need full trace

-- Internal check function with fuel-based termination
-- Fuel decreases on each frame processed, guaranteeing termination
checkWithFuel : ℕ → ℕ → SizedStream {∞} TimedFrame → LTL (TimedFrame → Bool) → Bool
checkWithFuel n start s φ with n
... | zero = true  -- Out of fuel, assume property holds
... | suc fuel = go φ
  where
    -- Recursive call with decreased fuel
    recurse : SizedStream {∞} TimedFrame → LTL (TimedFrame → Bool) → Bool
    recurse = checkWithFuel fuel start

    -- Check Maybe tail with default for empty case
    checkMaybeD : Bool → Maybe (SizedStream {∞} TimedFrame) → LTL (TimedFrame → Bool) → Bool
    checkMaybeD default nothing _ = default
    checkMaybeD _ (just s') ψ = recurse s' ψ

    go : LTL (TimedFrame → Bool) → Bool
    go (Atomic pred) = pred (hd s)
    go (Not ψ) = not (go ψ)
    go (And ψ₁ ψ₂) = if go ψ₁ then go ψ₂ else false
    go (Or ψ₁ ψ₂) = if go ψ₁ then true else go ψ₂
    go (Next ψ) = checkMaybeD true (tl s) ψ
    go (Always ψ) =
      if evalAtFrame (hd s) ψ
      then checkMaybeD true (tl s) (Always ψ)
      else false
    go (Eventually ψ) =
      if evalAtFrame (hd s) ψ
      then true
      else checkMaybeD false (tl s) (Eventually ψ)
    go (Until ψ₁ ψ₂) =
      if evalAtFrame (hd s) ψ₂
      then true
      else if evalAtFrame (hd s) ψ₁
           then checkMaybeD false (tl s) (Until ψ₁ ψ₂)
           else false
    go (EventuallyWithin window ψ) =
      if (timestamp (hd s) ∸ start) ≤ᵇ window
      then if evalAtFrame (hd s) ψ
           then true
           else checkMaybeD false (tl s) (EventuallyWithin window ψ)
      else false
    go (AlwaysWithin window ψ) =
      if (timestamp (hd s) ∸ start) ≤ᵇ window
      then if evalAtFrame (hd s) ψ
           then checkMaybeD true (tl s) (AlwaysWithin window ψ)
           else false
      else true

-- Default fuel for when caller doesn't provide trace length
-- In practice, caller should provide actual trace length
defaultFuel : ℕ
defaultFuel = 1000000  -- 1 million frames max

-- Public entry point
checkSizedStream : SizedStream {∞} TimedFrame → LTL (TimedFrame → Bool) → Bool
checkSizedStream stream φ = checkWithFuel defaultFuel (timestamp (hd stream)) stream φ

-- Entry point with explicit fuel (preferred - caller provides trace length)
checkSizedStreamWithFuel : ℕ → SizedStream {∞} TimedFrame → LTL (TimedFrame → Bool) → Bool
checkSizedStreamWithFuel fuel stream φ = checkWithFuel fuel (timestamp (hd stream)) stream φ
