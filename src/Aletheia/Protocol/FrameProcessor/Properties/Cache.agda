-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal cache update properties.
--
-- `updateCache` step lemmas (P10/P11) plus the properties of the shared
-- per-frame extraction table (`extractTable`/`cacheFromTable`) that
-- `updateCacheFromFrame` folds: faithfulness of the table lookup to
-- `extractTruthValue` for readable names, cache coherence (a read signal's
-- cached value equals what the frame extracts), and the monotonicity /
-- timestamp-bound / no-message preservation lemmas used by the cache-warmness
-- adequacy chain in `Protocol.Adequacy.WarmCache` / `Protocol.Adequacy.StreamingWarm`.
--
-- All lemmas in this module are about the `SignalCache` data structure and the
-- table/cache update functions in `Aletheia.Protocol.StreamState.Internals` —
-- they do NOT touch `handleDataFrame` or `stepL`.
module Aletheia.Protocol.FrameProcessor.Properties.Cache where
open import Aletheia.DBC.Identifier using
    (_≡csᵇ_; ≡csᵇ-sound; ≡csᵇ-false→≢; ≡csᵇ-refl-eq)

open import Aletheia.Protocol.StreamState.Internals
    using (updateCacheFromFrame; extractTable; cacheFromTable; _∈ᵇ_)
open import Aletheia.LTL.SignalPredicate
    using (SignalCache; mkSignalCache; CacheEntries;
           mkCachedSignal; lookupCache; updateCache;
           lookupEntries; updateEntries; extractTruthValue;
           lookupET)
open import Aletheia.LTL.SignalPredicate.Cache.Properties
    using (AllTimestamps≤; updateCache-monotone; updateCache-timestamps≤; updateEntries-keys-⊆)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Data.Bool using (true; false; T)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; ∃-syntax)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.Any using (here; there; index; _─_)
open import Data.List.Relation.Unary.All as All using ()
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᵖ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties
    using (⊆-trans; xs⊆x∷xs; ∈-∷⁺ʳ)
open import Data.List.Properties using (length-removeAt′)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- ============================================================================
-- PROPERTY 10: Signal cache update — same name lookup
-- ============================================================================

private
  -- Helper: looking up name in (name , v) ∷ rest returns just v.
  -- Uses Bool fast path: `≡csᵇ-refl-eq name : (name ≡csᵇ name) ≡ true`
  -- rewrites the `if` to its true branch.
  lookupEntries-head : ∀ name v rest →
    lookupEntries name ((name , v) ∷ rest) ≡ just v
  lookupEntries-head name v rest rewrite ≡csᵇ-refl-eq name = refl

  -- Helper: looking up name' ≢ name skips the head entry.
  -- Bool fast path: `with name' ≡csᵇ name in eq` — true branch contradicts neq
  -- via `≡csᵇ-sound`, false branch reduces the `if` to its else branch.
  lookupEntries-skip : ∀ name' name v rest →
    name' ≢ name →
    lookupEntries name' ((name , v) ∷ rest) ≡ lookupEntries name' rest
  lookupEntries-skip name' name v rest neq with name' ≡csᵇ name in eq
  ... | true  = ⊥-elim (neq (≡csᵇ-sound name' name (subst T (sym eq) tt)))
  ... | false = refl

  -- List-level: after updateEntries, looking up the updated name returns the new value.
  lookupEntries-updateEntries-hit : ∀ name val ts (es : CacheEntries) →
    lookupEntries name (updateEntries name val ts es) ≡ just (mkCachedSignal val ts)
  lookupEntries-updateEntries-hit name val ts [] =
    lookupEntries-head name (mkCachedSignal val ts) []
  lookupEntries-updateEntries-hit name val ts ((n , cached) ∷ rest)
    with name ≡csᵇ n in eq
  ... | true  = lookupEntries-head name (mkCachedSignal val ts) rest
  ... | false = trans (lookupEntries-skip name n cached (updateEntries name val ts rest)
                         (≡csᵇ-false→≢ name n eq))
                      (lookupEntries-updateEntries-hit name val ts rest)

  -- List-level: after updateEntries, looking up a different name is unchanged.
  lookupEntries-updateEntries-miss : ∀ name name' val ts (es : CacheEntries) →
    name ≢ name' →
    lookupEntries name' (updateEntries name val ts es) ≡ lookupEntries name' es
  lookupEntries-updateEntries-miss name name' val ts [] name≢name' =
    lookupEntries-skip name' name (mkCachedSignal val ts) [] (λ p → name≢name' (sym p))
  lookupEntries-updateEntries-miss name name' val ts ((n , cached) ∷ rest) name≢name'
    with name ≡csᵇ n in eq | name' ≡csᵇ n in eq'
  ... | true  | true  = ⊥-elim (name≢name'
                          (trans (≡csᵇ-sound name n (subst T (sym eq) tt))
                                 (sym (≡csᵇ-sound name' n (subst T (sym eq') tt)))))
  ... | true  | false =
    lookupEntries-skip name' name (mkCachedSignal val ts) rest (λ p → name≢name' (sym p))
  ... | false | true  rewrite ≡csᵇ-sound name' n (subst T (sym eq') tt) | ≡csᵇ-refl-eq n = refl
  ... | false | false =
    trans (lookupEntries-skip name' n cached (updateEntries name val ts rest)
             (≡csᵇ-false→≢ name' n eq'))
          (lookupEntries-updateEntries-miss name name' val ts rest name≢name')

-- After updateCache, looking up the updated name returns the new value.
-- Delegates to list-level proof via record decomposition.
lookupCache-updateCache-hit : ∀ name val ts cache →
  lookupCache name (updateCache name val ts cache) ≡ just (mkCachedSignal val ts)
lookupCache-updateCache-hit name val ts (mkSignalCache es _) =
  lookupEntries-updateEntries-hit name val ts es

-- ============================================================================
-- PROPERTY 11: Signal cache update — different name lookup unchanged
-- ============================================================================

-- After updateCache, looking up a different name returns the original value.
-- Combined with Property 10, this proves updateCache is a correct map-update.
lookupCache-updateCache-miss : ∀ name name' val ts cache →
  name ≢ name' →
  lookupCache name' (updateCache name val ts cache) ≡ lookupCache name' cache
lookupCache-updateCache-miss name name' val ts (mkSignalCache es _) name≢name' =
  lookupEntries-updateEntries-miss name name' val ts es name≢name'

-- ============================================================================
-- SHARED EXTRACTION TABLE (extractTable / cacheFromTable) PROPERTIES
-- ============================================================================
--
-- `updateCacheFromFrame` now folds the shared per-frame extraction table
-- (`cacheFromTable ts (extractTable dbc frame readable) cache`).  These lemmas
-- characterize that fold: the table lookup is faithful to `extractTruthValue`
-- for readable names, the cache is coherent with the frame's extraction, and
-- monotonicity / timestamp bounds / the no-message case are preserved — exactly
-- the shape the adequacy chain (`Protocol.Adequacy.StreamingWarm`,
-- `Protocol.Adequacy.WarmCache`) consumes.

private
  just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

-- A frame that matches no message extracts nothing for any signal name:
-- `extractSignalWithContext` returns `SignalNotInDBC` when `findMessageById`
-- misses, and `getValue SignalNotInDBC ≡ nothing`.
extractTruthValue-no-msg : ∀ {n} dbc (frame : CANFrame n) name →
  findMessageById (CANFrame.id frame) dbc ≡ nothing →
  extractTruthValue name dbc frame ≡ nothing
extractTruthValue-no-msg dbc frame name eq
  with findMessageById (CANFrame.id frame) dbc
... | nothing = refl
... | just _  = ⊥-elim (just≢nothing eq)

-- No matching message ⇒ every readable name fails ⇒ the extraction table is
-- empty.
extractTable-nil-no-msg : ∀ {n} dbc (frame : CANFrame n) readable →
  findMessageById (CANFrame.id frame) dbc ≡ nothing →
  extractTable dbc frame readable ≡ []
extractTable-nil-no-msg dbc frame []             eq = refl
extractTable-nil-no-msg dbc frame (name ∷ names) eq
  rewrite extractTruthValue-no-msg dbc frame name eq =
    extractTable-nil-no-msg dbc frame names eq

-- If `name` fails to extract on the frame it is absent from the table built
-- over ANY name list: only successful extractions are recorded, so no entry can
-- be keyed by a name that extracts to `nothing`.
lookupET-extractTable-nothing : ∀ {n} dbc (frame : CANFrame n) names name →
  extractTruthValue name dbc frame ≡ nothing →
  lookupET name (extractTable dbc frame names) ≡ nothing
lookupET-extractTable-nothing dbc frame []       name ext = refl
lookupET-extractTable-nothing dbc frame (m ∷ ms) name ext
  with extractTruthValue m dbc frame in eqm
... | nothing = lookupET-extractTable-nothing dbc frame ms name ext
... | just w  with name ≡csᵇ m in eqnm
...   | false = lookupET-extractTable-nothing dbc frame ms name ext
...   | true  = ⊥-elim (just≢nothing (trans (sym extmw) ext))
  where
    nameEq : name ≡ m
    nameEq = ≡csᵇ-sound name m (subst T (sym eqnm) tt)
    extmw : extractTruthValue name dbc frame ≡ just w
    extmw = trans (cong (λ y → extractTruthValue y dbc frame) nameEq) eqm

-- CRUX: for a readable name the table lookup is exactly the frame extraction.
-- A name-keyed entry's value is a pure function of the name, so no validity or
-- last-writer condition is needed.
extractTable-faithful : ∀ {n} dbc (frame : CANFrame n) readable name →
  (name ∈ᵇ readable) ≡ true →
  lookupET name (extractTable dbc frame readable) ≡ extractTruthValue name dbc frame
extractTable-faithful dbc frame []       name ()
extractTable-faithful dbc frame (x ∷ xs) name mem
  with name ≡csᵇ x in eqx
extractTable-faithful dbc frame (x ∷ xs) name mem | false
  with extractTruthValue x dbc frame
... | nothing         = extractTable-faithful dbc frame xs name mem
... | just w rewrite eqx = extractTable-faithful dbc frame xs name mem
extractTable-faithful dbc frame (x ∷ xs) name mem | true
  with extractTruthValue x dbc frame in eqv
... | just v rewrite eqx = sym (trans (cong (λ y → extractTruthValue y dbc frame) nameEqT) eqv)
  where
    nameEqT : name ≡ x
    nameEqT = ≡csᵇ-sound name x (subst T (sym eqx) tt)
... | nothing = trans (lookupET-extractTable-nothing dbc frame xs name extN) (sym extN)
  where
    nameEqT : name ≡ x
    nameEqT = ≡csᵇ-sound name x (subst T (sym eqx) tt)
    extN : extractTruthValue name dbc frame ≡ nothing
    extN = trans (cong (λ y → extractTruthValue y dbc frame) nameEqT) eqv

-- ============================================================================
-- cacheFromTable preserves a warm entry
-- ============================================================================

-- If `name`'s value is already correct in the cache and `name` extracts to that
-- same value on this frame, folding the frame's table keeps the entry correct.
-- Any re-write of `name` in the table writes the SAME `(v , ts)` (the entry
-- value is `extractTruthValue name`, a function), so the fold cannot corrupt it.
cacheFromTable-preserves-hit :
  ∀ {n} ts dbc (frame : CANFrame n) names cache name v →
  extractTruthValue name dbc frame ≡ just v →
  lookupCache name cache ≡ just (mkCachedSignal v ts) →
  lookupCache name (cacheFromTable ts (extractTable dbc frame names) cache)
    ≡ just (mkCachedSignal v ts)
cacheFromTable-preserves-hit ts dbc frame []       cache name v extv hit = hit
cacheFromTable-preserves-hit ts dbc frame (m ∷ ms) cache name v extv hit
  with extractTruthValue m dbc frame in eqm
... | nothing = cacheFromTable-preserves-hit ts dbc frame ms cache name v extv hit
... | just w  with name ≡csᵇ m in eqnm
...   | true  =
        cacheFromTable-preserves-hit ts dbc frame ms (updateCache m w ts cache) name v extv hitT
  where
    nameEq : name ≡ m
    nameEq = ≡csᵇ-sound name m (subst T (sym eqnm) tt)
    v≡w : v ≡ w
    v≡w = just-injective
            (trans (sym extv) (trans (cong (λ y → extractTruthValue y dbc frame) nameEq) eqm))
    hitT : lookupCache name (updateCache m w ts cache) ≡ just (mkCachedSignal v ts)
    hitT = trans (cong (λ y → lookupCache y (updateCache m w ts cache)) nameEq)
                 (trans (lookupCache-updateCache-hit m w ts cache)
                        (cong (λ z → just (mkCachedSignal z ts)) (sym v≡w)))
...   | false =
        cacheFromTable-preserves-hit ts dbc frame ms (updateCache m w ts cache) name v extv hitF
  where
    m≢name : m ≢ name
    m≢name p = ≡csᵇ-false→≢ name m eqnm (sym p)
    hitF : lookupCache name (updateCache m w ts cache) ≡ just (mkCachedSignal v ts)
    hitF = trans (lookupCache-updateCache-miss m name w ts cache m≢name) hit

-- ============================================================================
-- PROPERTY 30': cacheFromTable warms a readable observed name (coherence)
-- ============================================================================

-- Inductive core of coherence: a readable name that extracts to `v` lands in
-- the folded cache as exactly `mkCachedSignal v ts`.  At the matching readable
-- position `lookupCache-updateCache-hit` writes it and `cacheFromTable-preserves-hit`
-- carries it through the rest of the fold; earlier positions only shift the
-- starting cache, which the (cache-universal) induction absorbs.
cacheFromTable-warms-readable :
  ∀ {n} ts dbc (frame : CANFrame n) readable cache name v →
  (name ∈ᵇ readable) ≡ true →
  extractTruthValue name dbc frame ≡ just v →
  lookupCache name (cacheFromTable ts (extractTable dbc frame readable) cache)
    ≡ just (mkCachedSignal v ts)
cacheFromTable-warms-readable ts dbc frame []       cache name v () extv
cacheFromTable-warms-readable ts dbc frame (x ∷ xs) cache name v mem extv
  with name ≡csᵇ x in eqx
... | true  =
        trans (cong (λ t → lookupCache name (cacheFromTable ts t cache)) etEq)
              (cacheFromTable-preserves-hit ts dbc frame xs (updateCache x v ts cache) name v extv hit0)
  where
    nameEq : name ≡ x
    nameEq = ≡csᵇ-sound name x (subst T (sym eqx) tt)
    extXv : extractTruthValue x dbc frame ≡ just v
    extXv = trans (cong (λ y → extractTruthValue y dbc frame) (sym nameEq)) extv
    etEq : extractTable dbc frame (x ∷ xs) ≡ (x , v) ∷ extractTable dbc frame xs
    etEq rewrite extXv = refl
    hit0 : lookupCache name (updateCache x v ts cache) ≡ just (mkCachedSignal v ts)
    hit0 = trans (cong (λ y → lookupCache y (updateCache x v ts cache)) nameEq)
                 (lookupCache-updateCache-hit x v ts cache)
... | false with extractTruthValue x dbc frame
...   | nothing = cacheFromTable-warms-readable ts dbc frame xs cache name v mem extv
...   | just w  = cacheFromTable-warms-readable ts dbc frame xs (updateCache x w ts cache) name v mem extv

-- Cache coherence (P30, restated and strengthened): after `updateCacheFromFrame`
-- the cache value for a readable signal name that extracts to `v` is exactly
-- `mkCachedSignal v ts`.  The old proof needed a `prefix ++ sig ∷ suffix` split
-- with a `NotInSignals suffix` last-writer condition; the extract-once form
-- drops both — `extractTruthValue name` is a function of `name`, so duplicates
-- are consistent by construction.
updateCacheFromFrame-coherent :
  ∀ {n} dbc cache ts (frame : CANFrame n) readable name v →
  (name ∈ᵇ readable) ≡ true →
  extractTruthValue name dbc frame ≡ just v →
  lookupCache name (updateCacheFromFrame dbc cache ts frame readable)
    ≡ just (mkCachedSignal v ts)
updateCacheFromFrame-coherent dbc cache ts frame readable name v inSet extv =
  cacheFromTable-warms-readable ts dbc frame readable cache name v inSet extv

-- ============================================================================
-- PROPERTY 13: updateCacheFromFrame — no matching message leaves cache intact
-- ============================================================================

-- When no message matches the frame, the extraction table is empty and the fold
-- is the identity.
updateCacheFromFrame-no-match : ∀ {n} dbc cache ts (frame : CANFrame n) readable →
  findMessageById (CANFrame.id frame) dbc ≡ nothing →
  updateCacheFromFrame dbc cache ts frame readable ≡ cache
updateCacheFromFrame-no-match dbc cache ts frame readable eq
  rewrite extractTable-nil-no-msg dbc frame readable eq = refl

-- ============================================================================
-- PROPERTY 23'/25: cacheFromTable / updateCacheFromFrame monotonicity
-- ============================================================================

-- Any key already in the cache stays in the cache across the whole fold
-- (`updateCache-monotone` per entry).
cacheFromTable-monotone : ∀ ts table cache name cached →
  lookupCache name cache ≡ just cached →
  ∃[ cached' ] lookupCache name (cacheFromTable ts table cache) ≡ just cached'
cacheFromTable-monotone ts []               cache name cached eq = cached , eq
cacheFromTable-monotone ts ((m , w) ∷ rest) cache name cached eq =
  let (c₁ , eq₁) = updateCache-monotone m w ts cache name cached eq
  in cacheFromTable-monotone ts rest (updateCache m w ts cache) name c₁ eq₁

-- If a key was in the cache, it is still present after processing any frame.
-- (The readable set only affects WHICH updates happen; existing entries survive.)
updateCacheFromFrame-monotone : ∀ {m} dbc cache ts (frame : CANFrame m) readable name cached →
  lookupCache name cache ≡ just cached →
  ∃[ cached' ] lookupCache name (updateCacheFromFrame dbc cache ts frame readable) ≡ just cached'
updateCacheFromFrame-monotone dbc cache ts frame readable name cached eq =
  cacheFromTable-monotone ts (extractTable dbc frame readable) cache name cached eq

-- ============================================================================
-- PROPERTY 24'/26: cacheFromTable / updateCacheFromFrame timestamp bound
-- ============================================================================

-- The fold uses one shared timestamp `ts`, so `AllTimestamps≤ ts` is preserved
-- entry by entry (`updateCache-timestamps≤`).
cacheFromTable-timestamps≤ : ∀ ts table cache →
  AllTimestamps≤ ts (SignalCache.entries cache) →
  AllTimestamps≤ ts (SignalCache.entries (cacheFromTable ts table cache))
cacheFromTable-timestamps≤ ts []               cache h = h
cacheFromTable-timestamps≤ ts ((m , w) ∷ rest) cache h =
  cacheFromTable-timestamps≤ ts rest (updateCache m w ts cache)
    (updateCache-timestamps≤ m w ts cache h)

-- If all cache entries had timestamps ≤ ts, they still do after processing a frame.
updateCacheFromFrame-timestamps≤ : ∀ {m} dbc cache ts (frame : CANFrame m) readable →
  AllTimestamps≤ ts (SignalCache.entries cache) →
  AllTimestamps≤ ts (SignalCache.entries (updateCacheFromFrame dbc cache ts frame readable))
updateCacheFromFrame-timestamps≤ dbc cache ts frame readable h =
  cacheFromTable-timestamps≤ ts (extractTable dbc frame readable) cache h

-- ============================================================================
-- STRUCTURAL ENTRY-COUNT BOUND (key-set ⊆ readable set + pigeonhole)
-- ============================================================================
--
-- The cache's entry count is bounded by the length of the readable-signal set,
-- independent of trace length.  This is a STRUCTURAL COMPLETENESS statement: it
-- rules out a hypothetical "entries grow with the trace" failure mode by pinning
-- the key set to the (fixed) readable set and counting with the uniqueness
-- invariant.  It is NOT the residency bound — bounded residency is a
-- thunk-forcing property of the compiled runtime, outside what Agda observes.
--
-- It combines a key-set containment (every cache key is a readable name —
-- `…-keys-⊆` below, built from `updateEntries-keys-⊆`) with a pigeonhole (a
-- duplicate-free list all of whose elements lie in `ys` has length ≤ `length
-- ys`).  The cache's key set is duplicate-free by the `SignalCache`'s
-- `UniqueKeys` invariant.
--
-- On reusing the standard library: the only pigeonhole stdlib provides
-- (`Data.List.Fresh.Membership.Setoid.Properties.injection`) types BOTH lists as
-- duplicate-free `List#`, so it would require the readable set to be
-- duplicate-free too — but `readableSignals` is a plain concatenation with
-- repeats.  The form needed here (unique `xs`, arbitrary `ys`) is not in the
-- library, so it is proved directly, reusing the stdlib removal machinery
-- (`_─_` = `removeAt` at an `Any` index, and `length-removeAt′`) for the step.

private
  -- Removing the element pointed at by `x∈xs` from `xs` either was `z` itself
  -- (`x ≡ z`) or leaves `z` in the remainder.  Each case reduces
  -- definitionally through `_─_ = removeAt … (index …)`.
  remove-inv : ∀ {a} {A : Set a} {x z : A} {xs} (x∈xs : x ∈ xs) →
    z ∈ xs → x ≡ z ⊎ z ∈ (xs ─ x∈xs)
  remove-inv (here x≡w) (here z≡w) = inj₁ (trans x≡w (sym z≡w))
  remove-inv (here x≡w) (there z∈) = inj₂ z∈
  remove-inv (there x∈) (here z≡w) = inj₂ (here z≡w)
  remove-inv (there x∈) (there z∈) = map₂ there (remove-inv x∈ z∈)

-- Pigeonhole: a duplicate-free `xs`, all of whose elements are members of `ys`,
-- has `length xs ≤ length ys` (`ys` need not be duplicate-free).  Induct on `xs`,
-- removing the head's witnessed occurrence from `ys` each step; uniqueness of
-- `xs` discharges the "head reappears in the tail" case.
pigeonhole : ∀ {a} {A : Set a} (xs ys : List A) →
  Unique xs → xs ⊆ ys → length xs ≤ length ys
pigeonhole []       ys u             sub = z≤n
pigeonhole (x ∷ xs) ys (x∉xs ∷ᵖ uxs) sub =
  ≤-trans (s≤s (pigeonhole xs (ys ─ x∈ys) uxs sub'))
          (≤-reflexive (sym (length-removeAt′ ys (index x∈ys))))
  where
    x∈ys : x ∈ ys
    x∈ys = sub (here refl)
    sub' : xs ⊆ (ys ─ x∈ys)
    sub' z∈xs with remove-inv x∈ys (sub (there z∈xs))
    ... | inj₁ x≡z   = ⊥-elim (All.lookup x∉xs z∈xs x≡z)
    ... | inj₂ z∈ys─ = z∈ys─

-- Every key the extraction table records is one of the readable names it was
-- built from (`extractTable` only keeps `name ∷ …` entries for `name ∈ readable`).
extractTable-keys-⊆-readable : ∀ {n} dbc (frame : CANFrame n) readable →
  map proj₁ (extractTable dbc frame readable) ⊆ readable
extractTable-keys-⊆-readable dbc frame []             = λ ()
extractTable-keys-⊆-readable dbc frame (name ∷ names)
  with extractTruthValue name dbc frame
... | nothing = ⊆-trans (extractTable-keys-⊆-readable dbc frame names)
                        (xs⊆x∷xs names name)
... | just v  = ∈-∷⁺ʳ (here refl)
                      (⊆-trans (extractTable-keys-⊆-readable dbc frame names)
                               (xs⊆x∷xs names name))

-- Record-level lift of `updateEntries-keys-⊆`.
updateCache-keys-⊆ : ∀ name val ts cache →
  map proj₁ (SignalCache.entries (updateCache name val ts cache))
    ⊆ (name ∷ map proj₁ (SignalCache.entries cache))
updateCache-keys-⊆ name val ts (mkSignalCache es _) = updateEntries-keys-⊆ name val ts es

-- Folding a table into the cache keeps every key inside `bound`, given the
-- table's keys and the incoming cache's keys are both inside `bound`.
cacheFromTable-keys-⊆ : ∀ ts table cache bound →
  map proj₁ table ⊆ bound →
  map proj₁ (SignalCache.entries cache) ⊆ bound →
  map proj₁ (SignalCache.entries (cacheFromTable ts table cache)) ⊆ bound
cacheFromTable-keys-⊆ ts []               cache bound _        cacheSub = cacheSub
cacheFromTable-keys-⊆ ts ((m , w) ∷ rest) cache bound tableSub cacheSub =
  cacheFromTable-keys-⊆ ts rest (updateCache m w ts cache) bound
    (⊆-trans (xs⊆x∷xs (map proj₁ rest) m) tableSub)
    (⊆-trans (updateCache-keys-⊆ m w ts cache)
             (∈-∷⁺ʳ (tableSub (here refl)) cacheSub))

-- Processing one frame keeps every cache key inside the readable set.
updateCacheFromFrame-keys-⊆ : ∀ {n} dbc cache ts (frame : CANFrame n) readable →
  map proj₁ (SignalCache.entries cache) ⊆ readable →
  map proj₁ (SignalCache.entries (updateCacheFromFrame dbc cache ts frame readable)) ⊆ readable
updateCacheFromFrame-keys-⊆ dbc cache ts frame readable cacheSub =
  cacheFromTable-keys-⊆ ts (extractTable dbc frame readable) cache readable
    (extractTable-keys-⊆-readable dbc frame readable)
    cacheSub
