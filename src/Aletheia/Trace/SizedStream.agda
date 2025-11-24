{-# OPTIONS --without-K --guardedness --sized-types #-}

-- NOTE: This module does NOT use --safe because sized types are incompatible.
-- All other Aletheia modules remain --safe --without-K.
-- This module is isolated to contain the unsafe boundary.

module Aletheia.Trace.SizedStream where

open import Agda.Builtin.Size
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ; _∸_; _≤ᵇ_)
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
-- TODO: STREAM-BASED LTL CHECKING
-- ============================================================================
--
-- The LTL checker implementation needs careful handling of size constraints
-- with 'with' patterns. The basic structure is:
--
--   checkSizedStream : ∀ {i} → SizedStream {i} TimedFrame → ℕ → LTL (TimedFrame → Bool) → Bool
--
-- Key challenges:
-- 1. 'with' patterns don't automatically thread size constraints
-- 2. Need explicit size annotations on helper functions
-- 3. May need to avoid 'with' and use direct pattern matching
--
-- Alternative approach: Use the sized stream as input but implement checking
-- using explicit Maybe pattern matching rather than 'with'.
--
-- For now, the list-based checker in Incremental.agda works correctly.
-- The sized stream foundation is in place for future optimization.
