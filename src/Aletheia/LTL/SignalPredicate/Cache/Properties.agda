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
-- (updateSignals-monotone, updateCacheFromFrame-timestamps≤, etc.)
module Aletheia.LTL.SignalPredicate.Cache.Properties where

open import Aletheia.LTL.SignalPredicate.Cache
  using ( CachedSignal; mkCachedSignal; CacheEntries; SignalCache; mkSignalCache
        ; lookupEntries; updateEntries; lookupCache; updateCache; emptyCache )
open import Data.Rational using (ℚ)
open import Data.String using (String)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

-- ============================================================================
-- PREDICATES
-- ============================================================================

-- All cache entries have observation timestamps ≤ a given bound.
-- Under monotonic frame streams, this bound is the current frame timestamp.
AllTimestamps≤ : ℕ → CacheEntries → Set
AllTimestamps≤ ts = All (λ e → CachedSignal.lastObserved (proj₂ e) ≤ ts)

-- ============================================================================
-- LIST-LEVEL PROPERTIES
-- ============================================================================

-- Monotonicity: if a key was present before an update, it is still present after.
-- The value may change (if name ≡ name'), but the entry is never lost.
--
-- Uses nested with (not simultaneous) because updateEntries must reduce before
-- the inner lookupEntries exposes its decision expression for abstraction.
updateEntries-monotone : ∀ name val ts es name' cached →
  lookupEntries name' es ≡ just cached →
  ∃ λ cached' → lookupEntries name' (updateEntries name val ts es) ≡ just cached'
updateEntries-monotone name val ts [] name' cached ()
updateEntries-monotone name val ts ((n , v) ∷ rest) name' cached eq
  with name ≟ₛ n
... | yes refl with name' ≟ₛ name
...   | yes refl = mkCachedSignal val ts , refl
...   | no _     = cached , eq
updateEntries-monotone name val ts ((n , v) ∷ rest) name' cached eq
  | no _ with name' ≟ₛ n
... | yes refl = v , refl
... | no _     = updateEntries-monotone name val ts rest name' cached eq

-- Timestamp bound: updating with timestamp ts preserves AllTimestamps≤ ts.
-- The new/overwritten entry gets exactly ts (≤-refl), others are unchanged.
updateEntries-timestamps≤ : ∀ name val ts es →
  AllTimestamps≤ ts es →
  AllTimestamps≤ ts (updateEntries name val ts es)
updateEntries-timestamps≤ name val ts [] _ = ≤-refl ∷ []
updateEntries-timestamps≤ name val ts ((n , v) ∷ rest) (h ∷ t)
  with name ≟ₛ n
... | yes _ = ≤-refl ∷ t
... | no _  = h ∷ updateEntries-timestamps≤ name val ts rest t

-- Size bound: cache never shrinks — length is non-decreasing.
updateEntries-length≤ : ∀ name val ts es →
  length es ≤ length (updateEntries name val ts es)
updateEntries-length≤ name val ts [] = z≤n
updateEntries-length≤ name val ts ((n , v) ∷ rest)
  with name ≟ₛ n
... | yes _ = ≤-refl
... | no _  = s≤s (updateEntries-length≤ name val ts rest)

-- ============================================================================
-- RECORD-LEVEL PROPERTIES
-- ============================================================================

-- Empty cache trivially satisfies any timestamp bound.
emptyCache-timestamps≤ : ∀ ts → AllTimestamps≤ ts (SignalCache.entries emptyCache)
emptyCache-timestamps≤ _ = []

-- Record-level monotonicity: delegates to list-level proof.
updateCache-monotone : ∀ name val ts cache name' cached →
  lookupCache name' cache ≡ just cached →
  ∃ λ cached' → lookupCache name' (updateCache name val ts cache) ≡ just cached'
updateCache-monotone name val ts (mkSignalCache es _) =
  updateEntries-monotone name val ts es

-- Record-level timestamp bound: delegates to list-level proof.
updateCache-timestamps≤ : ∀ name val ts cache →
  AllTimestamps≤ ts (SignalCache.entries cache) →
  AllTimestamps≤ ts (SignalCache.entries (updateCache name val ts cache))
updateCache-timestamps≤ name val ts (mkSignalCache es _) =
  updateEntries-timestamps≤ name val ts es
