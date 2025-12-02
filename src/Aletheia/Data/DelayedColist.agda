{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Coinductive delayed colists for potentially infinite traces.
--
-- Purpose: Provide coinductive stream type with built-in delay (Thunk).
-- Key feature: Guardedness checking ensures productivity (no infinite loops).
-- Role: Foundation for LTL.Coinductive semantics over infinite traces.
--
-- Design: DelayedColist A ∞ represents a potentially infinite list of A values.
-- Each tail is wrapped in Thunk to satisfy guardedness requirements.
--
-- NOTE: Uses --sized-types and --guardedness (incompatible with --safe).
module Aletheia.Data.DelayedColist where

open import Size using (Size)
open import Codata.Sized.Thunk using (Thunk)

-- ============================================================================
-- DELAYED COLIST TYPE
-- ============================================================================

-- A colist where production of elements may be delayed
-- This generalizes both Colist and Delay
--
-- Constructors:
-- - []    : Empty stream
-- - _∷_   : Produce an element, continue with rest
-- - later : Delay without producing (for buffering, lazy computation)
data DelayedColist (A : Set) (i : Size) : Set where
  []    : DelayedColist A i
  _∷_   : A → Thunk (DelayedColist A) i → DelayedColist A i
  later : Thunk (DelayedColist A) i → DelayedColist A i
