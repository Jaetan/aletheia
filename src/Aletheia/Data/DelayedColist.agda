{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Shared DelayedColist type used by both StreamParser and LTL checking
-- Combines Colist with Delay - allows pausing without producing elements

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
