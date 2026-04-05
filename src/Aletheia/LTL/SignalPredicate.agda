{-# OPTIONS --safe --without-K #-}

-- Signal predicates for LTL properties: public API.
--
-- Purpose: Re-export types, cache, and evaluation from submodules.
-- Submodules:
--   Types      — TruthVal, predicate types, Kleene logic operations
--   Cache      — CachedSignal, SignalCache, lookupCache, updateCache
--   Evaluation — evalPredicateTV, extractTruthValue, comparison helpers
-- Role: Instantiate LTL.Syntax with signal-specific predicates for CAN verification.
module Aletheia.LTL.SignalPredicate where

open import Aletheia.LTL.SignalPredicate.Types public
open import Aletheia.LTL.SignalPredicate.Cache public
open import Aletheia.LTL.SignalPredicate.Evaluation public
