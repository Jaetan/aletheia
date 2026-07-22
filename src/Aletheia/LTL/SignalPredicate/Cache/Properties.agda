-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal cache monotonicity and temporal coherence properties.
--
-- Purpose: Prove that the signal cache is monotone (entries survive updates)
-- and temporally coherent (timestamps are bounded by the frame timestamp).
--
-- Properties (list-level):
--   updateEntries-monotone    — existing entries survive updates
--   updateEntries-timestamps≤ — timestamp bound preserved through update
--   updateEntries-length≤     — cache size never decreases
--
-- Properties (record-level):
--   updateCache-monotone      — record-level entry preservation
--   updateCache-timestamps≤   — record-level timestamp bound
--   emptyCache-timestamps≤    — empty cache satisfies any bound
--
-- Role: Building blocks for composite properties in FrameProcessor/Properties.agda
-- (cacheFromTable-monotone, updateCacheFromFrame-timestamps≤, etc.)
module Aletheia.LTL.SignalPredicate.Cache.Properties where

open import Aletheia.LTL.SignalPredicate.Cache
  using ( CachedSignal; mkCachedSignal; CacheEntries; SignalCache; mkSignalCache
        ; lookupEntries; updateEntries; lookupCache; updateCache; emptyCache )
open import Aletheia.DBC.Identifier using
  (_≡csᵇ_; ≡csᵇ-sound; ≡csᵇ-refl-eq)
open import Data.Bool using (true; false; T)
open import Data.List using ([]; _∷_; length; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-refl; ⊆-trans; ∷⁺ʳ; xs⊆x∷xs; ∈-∷⁺ʳ)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Aletheia.Trace.Time using (Timestamp; μs; _≤ᵗ_)
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

-- ============================================================================
-- PREDICATES
-- ============================================================================

-- All cache entries have observation timestamps ≤ a given bound.
-- Under monotonic frame streams, this bound is the current frame timestamp.
--
-- Bound type lifted from `ℕ` to `Timestamp μs`
-- alongside `CachedSignal.lastObserved`.  Comparison via `_≤ᵗ_` (Trace.Time)
-- which unfolds to `tsValue _ ≤ tsValue _`, so existing `≤-refl` proofs
-- continue to work via Agda's automatic unfolding of the type alias.
AllTimestamps≤ : Timestamp μs → CacheEntries → Set
AllTimestamps≤ ts = All (λ e → CachedSignal.lastObserved (proj₂ e) ≤ᵗ ts)

-- ============================================================================
-- LIST-LEVEL PROPERTIES
-- ============================================================================

-- Monotonicity: if a key was present before an update, it is still present after.
-- The value may change (if name ≡ name'), but the entry is never lost.
--
-- Uses nested with (not simultaneous) because updateEntries must reduce before
-- the inner lookupEntries exposes its decision expression for abstraction.
--
-- Proofs use the Bool fast path `_≡csᵇ_` (mirrors Cache.agda's runtime
-- definition) and recover propositional equality via `≡csᵇ-sound` /
-- `≡csᵇ-refl-eq` at the proof step.
updateEntries-monotone : ∀ name val ts es name' cached →
  lookupEntries name' es ≡ just cached →
  ∃ λ cached' → lookupEntries name' (updateEntries name val ts es) ≡ just cached'
updateEntries-monotone name val ts [] name' cached ()
updateEntries-monotone name val ts ((n , v) ∷ rest) name' cached eq
  with name ≡csᵇ n in eq-name
... | true  with ≡csᵇ-sound name n (subst T (sym eq-name) tt)
...   | refl with name' ≡csᵇ name in eq-name'
...     | true  with ≡csᵇ-sound name' name (subst T (sym eq-name') tt)
...       | refl rewrite ≡csᵇ-refl-eq name' = mkCachedSignal val ts , refl
updateEntries-monotone name val ts ((.name , v) ∷ rest) name' cached eq
  | true | refl | false = cached , eq
updateEntries-monotone name val ts ((n , v) ∷ rest) name' cached eq
  | false with name' ≡csᵇ n in eq-name'
... | true  = v , refl
... | false = updateEntries-monotone name val ts rest name' cached eq

-- Timestamp bound: updating with timestamp ts preserves AllTimestamps≤ ts.
-- The new/overwritten entry gets exactly ts (≤-refl), others are unchanged.
updateEntries-timestamps≤ : ∀ name val (ts : Timestamp μs) es →
  AllTimestamps≤ ts es →
  AllTimestamps≤ ts (updateEntries name val ts es)
updateEntries-timestamps≤ name val ts [] _ = ≤-refl ∷ []
updateEntries-timestamps≤ name val ts ((n , v) ∷ rest) (h ∷ t)
  with name ≡csᵇ n
... | true  = ≤-refl ∷ t
... | false = h ∷ updateEntries-timestamps≤ name val ts rest t

-- Size bound: cache never shrinks — length is non-decreasing.
updateEntries-length≤ : ∀ name val ts es →
  length es ≤ length (updateEntries name val ts es)
updateEntries-length≤ name val ts [] = z≤n
updateEntries-length≤ name val ts ((n , v) ∷ rest)
  with name ≡csᵇ n
... | true  = ≤-refl
... | false = s≤s (updateEntries-length≤ name val ts rest)

-- Key-set containment: one update introduces at most the updated `name` as a
-- new key.  Every key of the updated list is either `name` or a key that was
-- already present — the update never invents an unrelated key.  This is the
-- per-update step of the trace-independent entry-count bound: iterated over a
-- frame's extraction table and then over a trace, it confines the cache's key
-- set to the readable-signal set.
updateEntries-keys-⊆ : ∀ name val ts es →
  map proj₁ (updateEntries name val ts es) ⊆ (name ∷ map proj₁ es)
updateEntries-keys-⊆ name val ts [] = ⊆-refl
updateEntries-keys-⊆ name val ts ((n , cached) ∷ rest)
  with name ≡csᵇ n
... | true  = ∷⁺ʳ name (xs⊆x∷xs (map proj₁ rest) n)
... | false =
  ∈-∷⁺ʳ (there (here refl))
        (⊆-trans (updateEntries-keys-⊆ name val ts rest)
                 (∷⁺ʳ name (xs⊆x∷xs (map proj₁ rest) n)))

-- ============================================================================
-- RECORD-LEVEL PROPERTIES
-- ============================================================================

-- Empty cache trivially satisfies any timestamp bound.
emptyCache-timestamps≤ : ∀ (ts : Timestamp μs) → AllTimestamps≤ ts (SignalCache.entries emptyCache)
emptyCache-timestamps≤ _ = []

-- Record-level monotonicity: delegates to list-level proof.
updateCache-monotone : ∀ name val ts cache name' cached →
  lookupCache name' cache ≡ just cached →
  ∃ λ cached' → lookupCache name' (updateCache name val ts cache) ≡ just cached'
updateCache-monotone name val ts (mkSignalCache es _) =
  updateEntries-monotone name val ts es

-- Record-level timestamp bound: delegates to list-level proof.
updateCache-timestamps≤ : ∀ name val (ts : Timestamp μs) cache →
  AllTimestamps≤ ts (SignalCache.entries cache) →
  AllTimestamps≤ ts (SignalCache.entries (updateCache name val ts cache))
updateCache-timestamps≤ name val ts (mkSignalCache es _) =
  updateEntries-timestamps≤ name val ts es
