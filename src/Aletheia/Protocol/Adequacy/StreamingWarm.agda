-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Streaming cache warming: discharges the `AllCached` premise of
-- `warm-cache-agreement` by running the cache update over an observing trace.
--
-- Purpose: Close SA.19.3. Before this module, `warm-cache-agreement` in
-- `Protocol.Adequacy.WarmCache` was a conditional theorem: it assumes
-- `AllCached cache atoms` as a hypothesis, and no lemma established that
-- hypothesis for a cache produced by the streaming pipeline. This module
-- supplies that lemma.
--
-- Headline theorem:
--   streaming-warms-cache : ∀ dbc σ atoms cache₀
--     → AllObserved dbc σ atoms
--     → AllCached (cacheAfter dbc σ cache₀) atoms
--
-- where `cacheAfter` folds `updateCacheFromFrame` over a trace and
-- `AllObserved` says every atom's target signal is extracted from at least
-- one frame in the trace. Composed with `warm-cache-agreement`, this
-- converts the warm-cache agreement theorem from conditional to
-- unconditional on observing traces.
--
-- Proof architecture (three-lemma layout over the shared extraction table):
--   L2 `updateCacheFromFrame-warms` — a readable observed name lands in the
--      cache.  Direct corollary of `updateCacheFromFrame-coherent`
--      (FrameProcessor.Properties.Cache): the extract-once fold is keyed by the
--      readable name (`extractTruthValue name`, a function of the name), so a
--      successful extraction plus `(name ∈ᵇ readable) ≡ true` suffices — no
--      signal-list presence witness or filter bridge is required.
--   L3 `cacheAfter-warms` — inducts on `ObservedIn`. At `here`: warm the
--      cache for this frame, then iterate `updateCacheFromFrame-monotone`
--      over the tail. At `there`: recurse on the tail.
--   L4 `streaming-warms-cache` — inducts on the atom list, zipping
--      `AllObserved` / `AllCached` via L3.
--
-- The `Monotonic σ` premise in the original SA.19.3 sketch is dropped here:
-- cache warming is order-independent. `Monotonic σ` is required by metric-LTL
-- resolution lemmas elsewhere in the adequacy chain, not by the cache-warming
-- step. Callers that need to compose with metric operators will pass
-- `Monotonic σ` to those lemmas independently.
module Aletheia.Protocol.Adequacy.StreamingWarm where
open import Aletheia.DBC.Identifier using
    (_≡csᵇ_; ≡csᵇ-refl-eq)

open import Aletheia.Prelude using (List; Maybe; []; _,_; _×_; _∷_; _≡_; false; just; length; proj₁; proj₂; refl; true; tt)
open import Data.List using (map)
open import Data.Product using (∃-syntax)
open import Data.Char using (Char)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)

open import Aletheia.LTL.SignalPredicate using
  (SignalPredicate; SignalCache; mkCachedSignal;
   lookupCache; extractTruthValue)
open import Aletheia.LTL.SignalPredicate.Evaluation.Properties using (signalOf)
open import Aletheia.Protocol.StreamState.Internals using
  (updateCacheFromFrame; mkPredTable; _∈ᵇ_)
open import Aletheia.Protocol.FrameProcessor.Properties.Cache using
  (updateCacheFromFrame-coherent;
   updateCacheFromFrame-monotone)
open import Aletheia.LTL.Coalgebra using (LTLProc; denot)
open import Aletheia.LTL.Semantics using (⟦_⟧)
open import Aletheia.LTL.Adequacy using (runL)
open import Aletheia.Protocol.FrameProcessor.Properties using (AllBelow)
open import Aletheia.Protocol.Adequacy.WarmCache using (AllCached; warm-cache-agreement)

-- ============================================================================
-- L2: updateCacheFromFrame WARMS THE CACHE
-- ============================================================================

-- If a readable name extracts on the frame, the cache has an entry for it after
-- `updateCacheFromFrame`.  A direct corollary of cache coherence
-- (`updateCacheFromFrame-coherent`): the extract-once fold records the exact
-- extracted value, so the entry is `mkCachedSignal v ts`.  The extraction table
-- is keyed by the readable name (`extractTruthValue name`, a function of the
-- name), so no signal-list presence witness or filter bridge is needed — the
-- `(name ∈ᵇ readable) ≡ true` premise alone discharges it.
updateCacheFromFrame-warms : ∀ {n} dbc cache ts (frame : CANFrame n) readable name v →
  (name ∈ᵇ readable) ≡ true →
  extractTruthValue name dbc frame ≡ just v →
  ∃[ cs ] lookupCache name (updateCacheFromFrame dbc cache ts frame readable) ≡ just cs
updateCacheFromFrame-warms dbc cache ts frame readable name v inSet ext =
  mkCachedSignal v ts
  , updateCacheFromFrame-coherent dbc cache ts frame readable name v inSet ext

-- ============================================================================
-- CACHE FOLD AND OBSERVATION PREDICATE
-- ============================================================================

-- Trace-level cache update: fold `updateCacheFromFrame` over σ starting
-- from `cache₀`. This is what the streaming pipeline actually computes
-- (up to monotonicity checks, which do not affect the cache state).
cacheAfter : DBC → List TimedFrame → SignalCache → List (List Char) → SignalCache
cacheAfter dbc []       cache readable = cache
cacheAfter dbc (tf ∷ σ) cache readable =
  cacheAfter dbc σ
    (updateCacheFromFrame dbc cache (timestamp tf) (TimedFrame.frame tf) readable) readable

-- `name` is extracted from some frame in σ. Structural on σ to match the
-- recursion pattern of `cacheAfter`; existential over the extracted value
-- is carried inside the `here` constructor.
data ObservedIn (dbc : DBC) (name : List Char) : List TimedFrame → Set where
  here  : ∀ {tf σ v} →
          extractTruthValue name dbc (TimedFrame.frame tf) ≡ just v →
          ObservedIn dbc name (tf ∷ σ)
  there : ∀ {tf σ} →
          ObservedIn dbc name σ →
          ObservedIn dbc name (tf ∷ σ)

-- ============================================================================
-- L3: cacheAfter WARMS OBSERVED NAMES (with iterated monotonicity)
-- ============================================================================

-- Monotonicity of `cacheAfter`: any key already in the cache stays in the
-- cache throughout the trace. Folds `updateCacheFromFrame-monotone` (P25)
-- over σ; each step preserves presence, with the value possibly updated.
cacheAfter-monotone : ∀ dbc σ cache readable name cached →
  lookupCache name cache ≡ just cached →
  ∃[ cached' ] lookupCache name (cacheAfter dbc σ cache readable) ≡ just cached'
cacheAfter-monotone dbc []       cache readable name cached eq = cached , eq
cacheAfter-monotone dbc (tf ∷ σ) cache readable name cached eq =
  let ts     = timestamp tf
      frame  = TimedFrame.frame tf
      step   = updateCacheFromFrame-monotone dbc cache ts frame readable name cached eq
      c₁     = proj₁ step
      eq₁    = proj₂ step
  in cacheAfter-monotone dbc σ
       (updateCacheFromFrame dbc cache ts frame readable) readable name c₁ eq₁

-- If `name` is observed somewhere in σ, then `cacheAfter σ cache` has an
-- entry for `name`. At the observing frame, L2 warms the cache; then
-- `cacheAfter-monotone` carries the entry through the remaining trace.
cacheAfter-warms : ∀ dbc σ cache readable name →
  (name ∈ᵇ readable) ≡ true →
  ObservedIn dbc name σ →
  ∃[ cs ] lookupCache name (cacheAfter dbc σ cache readable) ≡ just cs
cacheAfter-warms dbc (tf ∷ σ) cache readable name inSet (here {v = v} ext) =
  let ts    = timestamp tf
      frame = TimedFrame.frame tf
      l2    = updateCacheFromFrame-warms dbc cache ts frame readable name v inSet ext
      c₁    = proj₁ l2
      eq₁   = proj₂ l2
  in cacheAfter-monotone dbc σ
       (updateCacheFromFrame dbc cache ts frame readable) readable name c₁ eq₁
cacheAfter-warms dbc (tf ∷ σ) cache readable name inSet (there rest) =
  let ts    = timestamp tf
      frame = TimedFrame.frame tf
  in cacheAfter-warms dbc σ
       (updateCacheFromFrame dbc cache ts frame readable) readable name inSet rest

-- ============================================================================
-- L4: STREAMING WARMS CACHE (HEADLINE SA.19.3)
-- ============================================================================

-- Every atom's target signal is observed somewhere in σ. Structural on
-- the atom list; mirrors the shape of `AllCached` so that composition
-- with `streaming-warms-cache` is a direct zip.
AllObserved : DBC → List TimedFrame → List SignalPredicate → Set
AllObserved dbc σ []       = ⊤
AllObserved dbc σ (p ∷ ps) = ObservedIn dbc (signalOf p) σ × AllObserved dbc σ ps

-- Every atom's target signal is in the readable set. Mirrors AllObserved's
-- shape so streaming-warms-cache can zip it. At the real config the readable
-- set IS the atoms' signals (map signalOf atoms), so this holds by
-- construction — proven by all-atoms-readable below — and never becomes a
-- caller-facing premise: streaming-adequacy discharges it internally.
AllReadable : List SignalPredicate → List (List Char) → Set
AllReadable []       readable = ⊤
AllReadable (p ∷ ps) readable = ((signalOf p ∈ᵇ readable) ≡ true) × AllReadable ps readable

-- Membership is monotone under a larger (cons-extended) readable set.
∈ᵇ-cons : ∀ name y xs → (name ∈ᵇ xs) ≡ true → (name ∈ᵇ (y ∷ xs)) ≡ true
∈ᵇ-cons name y xs h with name ≡csᵇ y
... | true  = refl
... | false = h

AllReadable-cons : ∀ atoms y readable →
  AllReadable atoms readable → AllReadable atoms (y ∷ readable)
AllReadable-cons []       y readable _              = tt
AllReadable-cons (p ∷ ps) y readable (inSet , rest) =
  ∈ᵇ-cons (signalOf p) y readable inSet , AllReadable-cons ps y readable rest

-- The atoms' own signal-name list is a readable set covering every atom.
all-atoms-readable : ∀ (atoms : List SignalPredicate) → AllReadable atoms (map signalOf atoms)
all-atoms-readable []       = tt
all-atoms-readable (p ∷ ps) = head∈ , AllReadable-cons ps (signalOf p) (map signalOf ps) (all-atoms-readable ps)
  where
    head∈ : (signalOf p ∈ᵇ (signalOf p ∷ map signalOf ps)) ≡ true
    head∈ rewrite ≡csᵇ-refl-eq (signalOf p) = refl

-- Headline theorem closing SA.19.3. Each atom `p`'s target signal is
-- observed in σ ⇒ `AllCached` holds on the cache produced by streaming.
-- Composed with `warm-cache-agreement`, removes the dangling premise
-- that made the streaming-adequacy theorem conditional.
streaming-warms-cache : ∀ dbc σ atoms cache readable →
  AllObserved dbc σ atoms →
  AllReadable atoms readable →
  AllCached (cacheAfter dbc σ cache readable) atoms
streaming-warms-cache dbc σ []       cache readable _              _               = tt
streaming-warms-cache dbc σ (p ∷ ps) cache readable (obs , obsAll) (inSet , rdAll) =
    cacheAfter-warms dbc σ cache readable (signalOf p) inSet obs
  , streaming-warms-cache dbc σ ps cache readable obsAll rdAll

-- ============================================================================
-- UNCONDITIONAL STREAMING ADEQUACY
-- ============================================================================

-- UNCACHED-ATOM DIAGNOSTICS.
--
-- BACKGROUND.  The `AllObserved` premise on `streaming-adequacy` (line
-- below) is a documented caller obligation.  When violated at runtime
-- (a property's atom whose target signal never appears in trace), the
-- kernel's `finalizeL` returns `Unsure → PropertyResult.Unresolved` —
-- sound (three-valued Kleene Unknown) but indistinguishable from a
-- genuinely undecided property without diagnostic context.
--
-- Mechanism:
--   * `WarningKind` + `Warning` ADTs (UncachedAtom kind),
--     `Response.Complete : List PropertyResult → List Warning →
--     Response`, `formatResponse` adds the `warnings:[...]` field to the
--     JSON envelope.
--   * `collectUncachedWarnings` in `Protocol.Handlers` walks each
--     `PropertyState`'s `atoms` list, looks up each atom's `signalOf` in
--     the cache, emits `mkWarning UncachedAtom (toℕ ps.index) (fromList
--     sigName)` on miss; `handleEndStream` populates the wire field via
--     the walker.
--   * Three bindings decode + surface the warnings list:
--       - Python: `CompleteWarning` TypedDict + `CompleteResponse.warnings`
--       - Go:     `StreamWarning` struct + `StreamResult.Warnings`
--       - C++:    `StreamWarning` struct + `StreamResult::warnings`
--     Each binding's `stream.ended` log line records `numWarnings`.
--   * A test trio (Python + Go + C++) asserts that an atom referencing an
--     unobserved signal produces exactly one `uncached_atom` warning at
--     EndStream and that all-observed traces produce none.
--   * Feature matrix row `end_stream_uncached_atom_warnings` declares
--     the parity across bindings; per-binding parity tests pass.
--
-- Soundness rationale: the existing `Unresolved` verdict is still
-- emitted unchanged.  Warnings are additive diagnostic context — they
-- ratify (do not replace or reinterpret) the verdict.
--
-- Logging + docs mirror:
--   * `LogEvent.endstream.uncached_atom` enumerant — in
--     `docs/LOG_EVENTS.yaml` (warn, "End-of-stream diagnostics"
--     section), `python/aletheia/client/_log.py` (`LogEvent`),
--     `go/aletheia/client.go` (slog.LevelWarn emit in `EndStream`),
--     `cpp/src/client.cpp` (`logger_.warn` in
--     `log_end_stream_summary` helper).  Cross-binding parity tests
--     (`test_log_events_parity.{py,go,cpp}` + `test_logging.py
--     TestEndStreamWarnings`) exercise the uncached_atom scenario via
--     mock backend.  Per-warning events carry `property_index` +
--     `detail` so operators can grep for specific properties.
--   * `check-runbook` entry — `#### `endstream.uncached_atom``
--     section under "End-of-stream diagnostics" in
--     `docs/operations/RUNBOOK.md`; covered by
--     `tools/check_runbook_coverage.py`.
--   * PROTOCOL.md `§ End-of-stream Warnings` under the Complete
--     Response documents wire shape (kind / property_index / detail),
--     defined kinds (currently `uncached_atom`), the evolution rule for
--     adding a new kind, and the logging mirror.
--
-- Cross-binding parity tests + the check-runbook gate enforce
-- non-regression.

-- One-shot closure of the streaming adequacy chain. Composes
-- `streaming-warms-cache` (discharges AllCached) with `warm-cache-agreement`
-- (BoundedTwoValued + AllBelow ⇒ runL ≡ ⟦_⟧) to get an unconditional
-- adequacy theorem: if σ is an observing trace for the atoms in `proc` and
-- `proc` is AllBelow at the atom count, then `runL` on the cached table
-- matches the denotational semantics on ANY evaluation trace σ'.
--
-- The observation trace σ and evaluation trace σ' are intentionally
-- separate: in practice they will typically be the same trace, but the
-- theorem does not require that — once the cache has seen every atom's
-- signal at least once, future evaluations on any trace are definite.
-- The runtime cache is `cacheAfter … (map signalOf atoms)` — the readable set
-- the streaming filter uses. `AllReadable` is discharged internally by
-- `all-atoms-readable`, so the caller-facing precondition set stays exactly
-- {AllObserved, AllBelow} — the added premise is proven here, never exposed.
streaming-adequacy : ∀ dbc σ atoms cache₀ (proc : LTLProc) σ'
  → AllObserved dbc σ atoms
  → AllBelow (length atoms) proc
  → runL (mkPredTable dbc (cacheAfter dbc σ cache₀ (map signalOf atoms)) atoms) proc σ'
    ≡ ⟦ denot (mkPredTable dbc (cacheAfter dbc σ cache₀ (map signalOf atoms)) atoms) proc ⟧ σ'
streaming-adequacy dbc σ atoms cache₀ proc σ' obs bound =
  warm-cache-agreement dbc (cacheAfter dbc σ cache₀ (map signalOf atoms)) atoms proc σ'
    (streaming-warms-cache dbc σ atoms cache₀ (map signalOf atoms) obs (all-atoms-readable atoms))
    bound
