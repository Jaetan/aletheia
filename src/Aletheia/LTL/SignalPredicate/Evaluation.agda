-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal predicate evaluation with cache fallback.
--
-- Purpose: Evaluate signal predicates against CAN frames with last-known-value
-- semantics via SignalCache.
-- Exports: evalPredicateTV, extractTruthValue, getTruthValue,
--   evalValuePredicateTV, evalDeltaPredicateTV, comparison helpers.
-- Role: Called by StreamState.Internals during incremental LTL checking.
module Aletheia.LTL.SignalPredicate.Evaluation where

open import Agda.Builtin.Strict using (primForce; primForceLemma)
open import Aletheia.Prelude using (Bool; List; Maybe; _∧_; _×_; _,_; _∷_; []; if_then_else_; just; nothing; true; ℚ)
open import Data.Char using (Char)
open import Data.Rational as Rat using (∣_∣; 0ℚ)
open import Data.Maybe using (_<∣>_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Aletheia.Data.Dec0 using (does₀)
open import Aletheia.Data.Dec0.Rational using (_≟ℚ₀_; _≤ℚ₀_; _<ℚ₀_; _>ℚ₀_; _≥ℚ₀_)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.SignalExtraction using (extractSignalWithContext)
open import Aletheia.CAN.ExtractionResult using (getValue)
open import Aletheia.DBC.Identifier using (_≡csᵇ_)
open import Aletheia.DBC.Types using (DBC)

open import Aletheia.LTL.SignalPredicate.Types using (Between; ChangedBy; DeltaP; DeltaPredicate; Equals; GreaterThan; GreaterThanOrEqual; LessThan; LessThanOrEqual; Pending; SignalPredicate; StableWithin; TruthVal; Unknown; ValueP; ValuePredicate; deltaPredicateSignal; fromBool; valuePredicateSignal)
open import Aletheia.LTL.SignalPredicate.Cache using (CachedSignal; SignalCache; lookupCache)

-- ============================================================================
-- COMPARISON HELPERS
-- ============================================================================

-- Self-certifying comparisons: each `Dec₀` twin (Aletheia.Data.Dec0.Rational)
-- carries the `Rat._≤ᵇ_`-built Bool (`does₀` — compiles to a direct ℤ
-- comparison, no `Dec` proof cell per call) together with an ERASED
-- `Reflects` certificate pinning its meaning (`≡` via antisymmetry, `≤`/`<`
-- via the stdlib `≤ᵇ` bridges).  The Bool comparators below are definitional
-- projections of the twins, so the fast path and its correctness can never
-- drift apart; MAlonzo erases the certificates (Dec₀ is a newtype over Bool
-- — pinned by `check-erasure`).

_==ℚ_ : ℚ → ℚ → Bool
x ==ℚ y = does₀ (x ≟ℚ₀ y)

_≤ℚ_ : ℚ → ℚ → Bool
x ≤ℚ y = does₀ (x ≤ℚ₀ y)

_<ℚ_ : ℚ → ℚ → Bool
x <ℚ y = does₀ (x <ℚ₀ y)

_>ℚ_ : ℚ → ℚ → Bool
x >ℚ y = does₀ (x >ℚ₀ y)

_≥ℚ_ : ℚ → ℚ → Bool
x ≥ℚ y = does₀ (x ≥ℚ₀ y)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Extract signal value using extraction with multiplexing support.
-- Signal name is List Char throughout.
extractTruthValue : ∀ {n} → List Char → DBC → CANFrame n → Maybe ℚ
extractTruthValue sigName dbc frame = getValue (extractSignalWithContext dbc frame sigName)

-- Project a cached signal entry to its rational value, or `nothing` on miss.
-- Top-level (not a `with`-introduced closure) so MAlonzo compiles it to a
-- direct pattern match without the per-call closure `Data.Maybe.map
-- CachedSignal.value` would allocate. Standalone form also lets proofs bridge
-- `lookupCache sig cache ≡ just cs` to `lookupCacheValue sig cache ≡ just
-- (CachedSignal.value cs)` via a single `cong cachedSignalValue`.
cachedSignalValue : Maybe CachedSignal → Maybe ℚ
cachedSignalValue nothing   = nothing
cachedSignalValue (just cs) = just (CachedSignal.value cs)

lookupCacheValue : List Char → SignalCache → Maybe ℚ
lookupCacheValue sigName cache = cachedSignalValue (lookupCache sigName cache)

-- ============================================================================
-- PURE PREDICATE EVALUATION
-- ============================================================================
--
-- These are exposed (no longer private) so that Evaluation/Properties.agda can
-- state definiteness lemmas by case-splitting on their Bool outputs. They
-- characterize the raw predicate semantics over definite (already extracted)
-- values; the *TV wrappers below add cache fallback and Unknown/Pending.

evalValuePredicate : ValuePredicate → ℚ → Bool
evalValuePredicate (Equals _ v) x             = x ==ℚ v
evalValuePredicate (LessThan _ v) x           = x <ℚ v
evalValuePredicate (GreaterThan _ v) x        = x >ℚ v
evalValuePredicate (LessThanOrEqual _ v) x    = x ≤ℚ v
evalValuePredicate (GreaterThanOrEqual _ v) x = x ≥ℚ v
evalValuePredicate (Between _ lo hi) x        = lo ≤ℚ x ∧ x ≤ℚ hi

evalDeltaPredicate : DeltaPredicate → ℚ → ℚ → Bool
evalDeltaPredicate (ChangedBy _ delta) prev curr =
  let diff = curr Rat.- prev
  in  if 0ℚ ≤ℚ delta then delta ≤ℚ diff else diff ≤ℚ delta
evalDeltaPredicate (StableWithin _ tol) prev curr = ∣ curr Rat.- prev ∣ ≤ℚ tol

-- ============================================================================
-- THREE-VALUED PREDICATE EVALUATION
-- ============================================================================

-- Get signal value: try frame first, then cache (via Maybe's _<∣>_ alternative).
getTruthValue : ∀ {n} → List Char → DBC → SignalCache → CANFrame n → Maybe ℚ
getTruthValue sigName dbc cache frame =
  extractTruthValue sigName dbc frame <∣> lookupCacheValue sigName cache

-- Evaluate value predicate with cache fallback
evalValuePredicateTV : ∀ {n} → DBC → SignalCache → ValuePredicate → CANFrame n → TruthVal
evalValuePredicateTV dbc cache vp frame =
  case getTruthValue (valuePredicateSignal vp) dbc cache frame of λ where
    (just v) → fromBool (evalValuePredicate vp v)
    nothing  → Unknown

-- Evaluate delta predicate with cache
evalDeltaPredicateTV : ∀ {n} → DBC → SignalCache → DeltaPredicate → CANFrame n → TruthVal
evalDeltaPredicateTV dbc cache dp frame =
  let sigName = deltaPredicateSignal dp
      currVal = getTruthValue sigName dbc cache frame
      prevVal = lookupCacheValue sigName cache
  in case currVal of λ where
    nothing   → Unknown
    (just cv) → case prevVal of λ where
      nothing   → Pending
      (just pv) → fromBool (evalDeltaPredicate dp pv cv)

-- Evaluate any signal predicate with cache
evalPredicateTV : ∀ {n} → DBC → SignalCache → SignalPredicate → CANFrame n → TruthVal
evalPredicateTV dbc cache (ValueP vp) frame = evalValuePredicateTV dbc cache vp frame
evalPredicateTV dbc cache (DeltaP dp) frame = evalDeltaPredicateTV dbc cache dp frame

-- ============================================================================
-- SHARED EXTRACTION TABLE (extract-once streaming hot path)
-- ============================================================================
--
-- The streaming step extracts each readable signal from the accepted frame
-- exactly once and records the successes in one name-keyed table.  Both the
-- signal-cache update (`cacheFromTable` in `Protocol.StreamState.Internals`)
-- and predicate evaluation (`mkPredTableT` there) then read that single table
-- instead of re-running `extractSignalWithContext` per consumer.  Before this,
-- every readable signal was extracted twice per accepted frame — once to warm
-- the cache and once to evaluate the atoms that target it.
--
-- The `*TVT` mirrors below are the eval-side readers.  They take the frame's
-- extraction result as the pre-computed `ExtractTable` rather than re-deriving
-- it from `dbc`/`frame`, so they carry neither argument.  The last-known-value
-- fallback still reads the OLD `cache` (`lookupCacheValue`), exactly as the
-- `getTruthValue` originals do — the evaluate-then-update ordering that keeps
-- delta predicates seeing distinct previous/current values is unchanged.

-- Successful readable extractions for the current frame: signal name ↦ value.
ExtractTable : Set
ExtractTable = List (List Char × ℚ)

-- Association lookup into the extraction table (Bool `_≡csᵇ_` fast path, never
-- `Dec` — a proof-term allocation per lookup on the hot path).
lookupET : List Char → ExtractTable → Maybe ℚ
lookupET _    []               = nothing
lookupET name ((n , v) ∷ rest) = if name ≡csᵇ n then just v else lookupET name rest

-- Get signal value: try the current-frame table first, then the cache
-- fallback.  Mirrors `getTruthValue`, but the frame extraction is read from
-- the shared table (`lookupET`) instead of recomputed.
getTruthValueT : List Char → ExtractTable → SignalCache → Maybe ℚ
getTruthValueT name table cache = lookupET name table <∣> lookupCacheValue name cache

-- Evaluate a value predicate against the shared table with cache fallback.
evalValuePredicateTVT : ExtractTable → SignalCache → ValuePredicate → TruthVal
evalValuePredicateTVT table cache vp =
  case getTruthValueT (valuePredicateSignal vp) table cache of λ where
    (just v) → fromBool (evalValuePredicate vp v)
    nothing  → Unknown

-- Evaluate a delta predicate against the shared table.  The previous value
-- still comes from the OLD cache (`lookupCacheValue`), so evaluate-then-update
-- ordering is preserved.
evalDeltaPredicateTVT : ExtractTable → SignalCache → DeltaPredicate → TruthVal
evalDeltaPredicateTVT table cache dp =
  let sigName = deltaPredicateSignal dp
      currVal = getTruthValueT sigName table cache
      prevVal = lookupCacheValue sigName cache
  in case currVal of λ where
    nothing   → Unknown
    (just cv) → case prevVal of λ where
      nothing   → Pending
      (just pv) → fromBool (evalDeltaPredicate dp pv cv)

-- Evaluate any signal predicate against the shared table with cache fallback.
evalPredicateTVT : ExtractTable → SignalCache → SignalPredicate → TruthVal
evalPredicateTVT table cache (ValueP vp) = evalValuePredicateTVT table cache vp
evalPredicateTVT table cache (DeltaP dp) = evalDeltaPredicateTVT table cache dp

-- ── Extraction-table spine forcing (bounded streaming residency) ─────────────
--
-- Companion to `Cache.withForcedCache`.  Forcing the outgoing cache's entry
-- spine already forces the table transitively (`cacheFromTable` folds over the
-- table, so reducing the cache to weak head normal form walks the whole table
-- spine), but the streaming step demands the table spine directly too so the
-- optimization does not silently depend on that fold's evaluation order.  Spine
-- only, matching `withForcedCache`: an unevaluated extracted `ℚ` retains its
-- frame but the next observation of that signal overwrites it, so retention is
-- bounded by the DBC's signal count, not by the trace length.
tableSpineForced : ExtractTable → Bool
tableSpineForced []       = true
tableSpineForced (_ ∷ es) = tableSpineForced es

-- Evaluate the table's spine, then return the result value.  Unlike
-- `withForcedCache` (which threads the cache into a continuation), the table is
-- consumed by both the cache update and the eval inside the result value, so it
-- is already fully applied here.
withForcedTable : {B : Set} → ExtractTable → B → B
withForcedTable t b = primForce (tableSpineForced t) (λ _ → b)

-- Transparency: forcing changes evaluation order only, never the value.
withForcedTable-id : {B : Set} (t : ExtractTable) (b : B) → withForcedTable t b ≡ b
withForcedTable-id t b = primForceLemma (tableSpineForced t) (λ _ → b)
