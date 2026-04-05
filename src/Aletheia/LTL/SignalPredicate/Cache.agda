{-# OPTIONS --safe --without-K #-}

-- Signal value cache: association list mapping signal names to cached values,
-- with an erased (@0) proof that keys are unique.
--
-- Purpose: Maintain last-known signal values with observation timestamps.
-- Operations: lookupCache, updateCache, emptyCache (record-level API).
-- List-level: lookupEntries, updateEntries (exported for proofs).
-- Role: Used by StreamState for incremental LTL evaluation with cache fallback.
module Aletheia.LTL.SignalPredicate.Cache where

open import Aletheia.Prelude
open import Data.Rational using (ℚ)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs as AP using (AllPairs; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- Cached signal value with observation timestamp.
record CachedSignal : Set where
  constructor mkCachedSignal
  field
    value        : ℚ
    lastObserved : ℕ  -- timestamp in microseconds

-- Bare list of cache entries (exported for proof use).
CacheEntries : Set
CacheEntries = List (String × CachedSignal)

-- Key-uniqueness predicate: all pairs of entries have distinct keys.
UniqueKeys : CacheEntries → Set
UniqueKeys = AllPairs (λ p₁ p₂ → proj₁ p₁ ≢ proj₁ p₂)

-- Signal cache: association list with erased uniqueness proof.
-- The @0 field is type-checked by Agda but erased by MAlonzo (zero runtime cost).
record SignalCache : Set where
  constructor mkSignalCache
  field
    entries  : CacheEntries
    @0 unique : UniqueKeys entries

-- ============================================================================
-- LIST-LEVEL OPERATIONS (for proofs in Properties.agda)
-- ============================================================================

-- Lookup a signal in a cache entry list
lookupEntries : String → CacheEntries → Maybe CachedSignal
lookupEntries _ [] = nothing
lookupEntries name ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋ then just cached else lookupEntries name rest

-- Update or insert a signal value in a cache entry list
updateEntries : String → ℚ → ℕ → CacheEntries → CacheEntries
updateEntries name val ts [] = (name , mkCachedSignal val ts) ∷ []
updateEntries name val ts ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋
  then (name , mkCachedSignal val ts) ∷ rest
  else (n , cached) ∷ updateEntries name val ts rest

-- ============================================================================
-- ERASED PRESERVATION PROOFS (@0 — type-checked, MAlonzo-erased)
-- ============================================================================

-- Helper: updateEntries preserves All-distinct-from-key.
-- If all keys in es are ≢ key, and key ≢ name, then all keys in the
-- updated list are still ≢ key.
@0 updateEntries-All-neq : ∀ key name val ts es →
  All (λ p → key ≢ proj₁ p) es →
  key ≢ name →
  All (λ p → key ≢ proj₁ p) (updateEntries name val ts es)
updateEntries-All-neq key name val ts [] _ key≢name = key≢name ∷ []
updateEntries-All-neq key name val ts ((n , v) ∷ rest) (key≢n ∷ allRest) key≢name
  with name ≟ₛ n
... | yes refl = key≢name ∷ allRest
... | no  _   = key≢n ∷ updateEntries-All-neq key name val ts rest allRest key≢name

-- Main preservation: updateEntries preserves key uniqueness.
@0 updateEntries-unique : ∀ name val ts es →
  UniqueKeys es → UniqueKeys (updateEntries name val ts es)
updateEntries-unique name val ts [] _ = [] ∷ []
updateEntries-unique name val ts ((n , v) ∷ rest) (allN ∷ uniqueRest)
  with name ≟ₛ n
... | yes refl = allN ∷ uniqueRest
... | no  ¬p  = updateEntries-All-neq n name val ts rest allN (¬p ∘ sym)
                ∷ updateEntries-unique name val ts rest uniqueRest

-- ============================================================================
-- RECORD-LEVEL API (for consumers)
-- ============================================================================

-- Empty cache (trivially unique).
emptyCache : SignalCache
emptyCache = mkSignalCache [] []

-- Lookup a signal in the cache.
lookupCache : String → SignalCache → Maybe CachedSignal
lookupCache name cache = lookupEntries name (SignalCache.entries cache)

-- Update or insert a signal value, preserving key uniqueness.
updateCache : String → ℚ → ℕ → SignalCache → SignalCache
updateCache name val ts (mkSignalCache es u) =
  mkSignalCache (updateEntries name val ts es) (updateEntries-unique name val ts es u)
