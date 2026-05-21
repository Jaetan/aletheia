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
open import Data.Bool using ()
open import Data.Char using (Char)
open import Data.Rational using ()
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs as AP using (AllPairs; []; _∷_)
open import Data.Unit using ()
open import Relation.Binary.PropositionalEquality using (_≢_; subst)
open import Aletheia.Trace.Time using (Timestamp; μs)

-- Bool-valued List Char equality (Path-A.5 hot-path Dec-allocation escape).
-- Soundness/completeness via `Identifier.≡csᵇ-sound` / `≡csᵇ-complete` /
-- `≡csᵇ-false→≢`; structural and `--safe` (no axioms).
open import Aletheia.DBC.Identifier using (_≡csᵇ_; ≡csᵇ-sound; ≡csᵇ-false→≢)

-- Cached signal value with observation timestamp.
--
-- R6-B7.3 — 2026-05-17: `lastObserved` lifted from `ℕ` to `Timestamp μs`.
-- The prior `ℕ` rationale ("avoids an unwrap at every cache lookup / update")
-- was a phantom hazard — `lastObserved` has zero runtime READ sites
-- (verified by grep; only proof-side use in `Cache/Properties.AllTimestamps≤`).
-- `Timestamp μs` here lets the sole runtime caller (`StreamState.handleDataFrame`)
-- pass `timestamp tf` directly instead of `timestampℕ tf`, eliminating the
-- per-frame unwrap entirely.
record CachedSignal : Set where
  constructor mkCachedSignal
  field
    value        : ℚ
    lastObserved : Timestamp μs

-- Bare list of cache entries (exported for proof use).
CacheEntries : Set
CacheEntries = List (List Char × CachedSignal)

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

-- Lookup a signal in a cache entry list.
--
-- Bool fast path (`_≡csᵇ_ : List Char → List Char → Bool`): structural
-- recursion + soundness/completeness in `Identifier.{≡csᵇ-sound, ≡csᵇ-complete,
-- ≡csᵇ-false→≢, ≡csᵇ-refl-eq}`, all `--safe`. The `@0` proofs below
-- (`updateEntries-All-neq`, `updateEntries-unique`) bridge from `_≡csᵇ_`'s
-- Bool result back to propositional `name ≡ n` via `≡csᵇ-sound` in the
-- `true` branch, so `UniqueKeys` preservation is preserved without a
-- `prim-string-eq-sound` postulate. Path A.5 confirmed +9–39% Stream LTL
-- throughput across all bindings vs the prior `_≟ₗᶜ_` form.
lookupEntries : List Char → CacheEntries → Maybe CachedSignal
lookupEntries _ [] = nothing
lookupEntries name ((n , cached) ∷ rest) =
  if name ≡csᵇ n then just cached else lookupEntries name rest

-- Update or insert a signal value in a cache entry list.
updateEntries : List Char → ℚ → Timestamp μs → CacheEntries → CacheEntries
updateEntries name val ts [] = (name , mkCachedSignal val ts) ∷ []
updateEntries name val ts ((n , cached) ∷ rest) =
  if name ≡csᵇ n
  then (name , mkCachedSignal val ts) ∷ rest
  else (n , cached) ∷ updateEntries name val ts rest

-- ============================================================================
-- ERASED PRESERVATION PROOFS (@0 — type-checked, MAlonzo-erased)
-- ============================================================================

-- Helper: updateEntries preserves All-distinct-from-key.
-- If all keys in es are ≢ key, and key ≢ name, then all keys in the
-- updated list are still ≢ key.
--
-- Proof reasons about the Bool fast path via `with name ≡csᵇ n in eq`,
-- then bridges to propositional `name ≡ n` via `≡csᵇ-sound` (in the `true`
-- branch) or to `name ≢ n` via `≡csᵇ-false→≢` (in the `false` branch).
@0 updateEntries-All-neq : ∀ key name val (ts : Timestamp μs) es →
  All (λ p → key ≢ proj₁ p) es →
  key ≢ name →
  All (λ p → key ≢ proj₁ p) (updateEntries name val ts es)
updateEntries-All-neq key name val ts [] _ key≢name = key≢name ∷ []
updateEntries-All-neq key name val ts ((n , v) ∷ rest) (key≢n ∷ allRest) key≢name
  with name ≡csᵇ n in eq
... | true  rewrite ≡csᵇ-sound name n (subst T (sym eq) tt) = key≢name ∷ allRest
... | false = key≢n ∷ updateEntries-All-neq key name val ts rest allRest key≢name

-- Main preservation: updateEntries preserves key uniqueness.
@0 updateEntries-unique : ∀ name val (ts : Timestamp μs) es →
  UniqueKeys es → UniqueKeys (updateEntries name val ts es)
updateEntries-unique name val ts [] _ = [] ∷ []
updateEntries-unique name val ts ((n , v) ∷ rest) (allN ∷ uniqueRest)
  with name ≡csᵇ n in eq
... | true  rewrite ≡csᵇ-sound name n (subst T (sym eq) tt) = allN ∷ uniqueRest
... | false = updateEntries-All-neq n name val ts rest allN
                (≡csᵇ-false→≢ name n eq ∘ sym)
              ∷ updateEntries-unique name val ts rest uniqueRest

-- ============================================================================
-- RECORD-LEVEL API (for consumers)
-- ============================================================================

-- Empty cache (trivially unique).
emptyCache : SignalCache
emptyCache = mkSignalCache [] []

-- Lookup a signal in the cache.
lookupCache : List Char → SignalCache → Maybe CachedSignal
lookupCache name cache = lookupEntries name (SignalCache.entries cache)

-- Update or insert a signal value, preserving key uniqueness.
updateCache : List Char → ℚ → Timestamp μs → SignalCache → SignalCache
updateCache name val ts (mkSignalCache es u) =
  mkSignalCache (updateEntries name val ts es) (updateEntries-unique name val ts es u)
