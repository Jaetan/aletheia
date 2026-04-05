{-# OPTIONS --safe --without-K #-}

-- Signal value cache: association list mapping signal names to cached values.
--
-- Purpose: Maintain last-known signal values with observation timestamps.
-- Operations: lookupCache, updateCache, emptyCache.
-- Role: Used by StreamState for incremental LTL evaluation with cache fallback.
module Aletheia.LTL.SignalPredicate.Cache where

open import Aletheia.Prelude
open import Data.Rational using (ℚ)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)

-- Cached signal value with observation timestamp.
record CachedSignal : Set where
  constructor mkCachedSignal
  field
    value        : ℚ
    lastObserved : ℕ  -- timestamp in microseconds

-- Signal cache: association list mapping signal names to cached values.
SignalCache : Set
SignalCache = List (String × CachedSignal)

-- Empty cache
emptyCache : SignalCache
emptyCache = []

-- Lookup a signal in the cache
lookupCache : String → SignalCache → Maybe CachedSignal
lookupCache _ [] = nothing
lookupCache name ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋ then just cached else lookupCache name rest

-- Update or insert a signal value in the cache
updateCache : String → ℚ → ℕ → SignalCache → SignalCache
updateCache name val ts [] = (name , mkCachedSignal val ts) ∷ []
updateCache name val ts ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋
  then (name , mkCachedSignal val ts) ∷ rest
  else (n , cached) ∷ updateCache name val ts rest
