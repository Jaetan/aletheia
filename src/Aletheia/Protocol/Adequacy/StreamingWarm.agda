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
-- Proof architecture (advisor-approved four-lemma layout):
--   L1 `updateSignals-warms` — inducts on `SigPresent name sigs` (derived
--      from `findSignalInList name sigs ≡ just sig`). At the matching
--      position: `updateSignals-step-hit` + `lookupCache-updateCache-hit`
--      + `updateSignals-monotone` (P23). At non-matching positions:
--      case-split on `extractTruthValue (Identifier.name (DBCSignal.name s)) dbc frame` and
--      recurse — `updateSignals` reduces in parallel because it
--      pattern-matches on the same scrutinee.
--   L2 `updateCacheFromFrame-warms` — decomposes `extractTruthValue ≡ just v`
--      through the nested `with`s of `extractSignalWithContext`, then
--      composes `updateCacheFromFrame-match` with L1.
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
--
-- No bridging lemma is needed for the name↔Identifier.name (DBCSignal.name matchup):
-- `updateSignals` pattern-matches on `extractTruthValue (Identifier.name (DBCSignal.name sig))
-- dbc frame` with exactly that syntactic form, so `subst` on the
-- name-equality suffices to align hypothesis types.
module Aletheia.Protocol.Adequacy.StreamingWarm where
open import Aletheia.DBC.Identifier using
    (Identifier; _≡csᵇ_; ≡csᵇ-sound)

open import Aletheia.Prelude
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ()
open import Data.Maybe using ()
open import Data.Product using (∃-syntax)
open import Data.Char using (Char)
open import Data.Bool using ()
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (subst)

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DBCHelpers using (findMessageById; findSignalByName; findSignalInList)
open import Aletheia.CAN.SignalExtraction using ()
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)

open import Aletheia.LTL.SignalPredicate using
  (SignalPredicate; SignalCache; mkCachedSignal;
   lookupCache; updateCache; extractTruthValue)
open import Aletheia.LTL.SignalPredicate.Evaluation.Properties using (signalOf)
open import Aletheia.Protocol.StreamState.Internals using
  (updateCacheFromFrame; updateSignals; mkPredTable)
open import Aletheia.Protocol.FrameProcessor.Properties.Cache using
  (lookupCache-updateCache-hit;
   updateSignals-step-hit;
   updateCacheFromFrame-match;
   updateSignals-monotone;
   updateCacheFromFrame-monotone)
open import Aletheia.LTL.Coalgebra using (LTLProc; denot)
open import Aletheia.LTL.Semantics using (⟦_⟧)
open import Aletheia.LTL.Adequacy using (runL)
open import Aletheia.Protocol.FrameProcessor.Properties using (AllBelow)
open import Aletheia.Protocol.Adequacy.WarmCache using (AllCached; warm-cache-agreement)

-- ============================================================================
-- ABSURDITY HELPER
-- ============================================================================

-- `nothing ≡ just v` is uninhabited. Local helper to avoid littering the
-- proof with inline `λ ()` at each impossible branch.
--
-- DO NOT RE-RAISE IN REVIEW (R20-AGDA-D-19.3 / R20-AGDA-D-GA20.1 — FP-VERIFIED).
--   Future Cat 27 "stdlib coverage" sweeps may flag this as re-inventing
--   `Data.Maybe.Properties.just≢nothing`.  Closed FP after re-audit: the
--   stdlib equivalent gives the OPPOSITE direction (`just v ≡ nothing → ⊥`),
--   so adoption requires `≢-sym` wrapping + an import.  Local 2-line
--   absurdity helper is shorter than the stdlib path AND reads more
--   directly at the call sites (`⊥-elim (nothing≢just eq)` matches the
--   shape of `eq : nothing ≡ just v` produced by the `with`-discrimination
--   on line 213/215).  Revisit only if stdlib gains a directly-signatured
--   `nothing≢just`, OR a project-wide audit standardises on stdlib
--   absurdity imports.
private
  nothing≢just : ∀ {A : Set} {v : A} → _≡_ {A = Maybe A} nothing (just v) → ⊥
  nothing≢just ()

-- ============================================================================
-- SIGNAL PRESENCE IN A SIGNAL LIST
-- ============================================================================

-- Witness that `name` is the name of some signal in `sigs`. Structural on
-- the list; used as the induction parameter for `updateSignals-warms`.
-- Dual to `findSignalInList`'s `just` outcome: every result of
-- `findSignalInList name sigs ≡ just sig` produces a `SigPresent name sigs`
-- via `findSignalInList→SigPresent`.
data SigPresent (name : List Char) : List DBCSignal → Set where
  here  : ∀ {sig sigs} →
          Identifier.name (DBCSignal.name sig) ≡ name →
          SigPresent name (sig ∷ sigs)
  there : ∀ {sig sigs} →
          SigPresent name sigs →
          SigPresent name (sig ∷ sigs)

-- `findSignalInList` discovery establishes `SigPresent`. The `yes` branch
-- of `findSignalInList` witnesses `name ≡ Identifier.name (DBCSignal.name s)`, which is the
-- `here` case (with `sym` to flip the equation direction). The `no` branch
-- recurses on the tail, giving the `there` case.
findSignalInList→SigPresent : ∀ name sigs sig →
  findSignalInList name sigs ≡ just sig →
  SigPresent name sigs
findSignalInList→SigPresent name (s ∷ ss) sig eq
  with name ≡csᵇ Identifier.name (DBCSignal.name s) in eq-name
... | true  = here (sym (≡csᵇ-sound name (Identifier.name (DBCSignal.name s))
                          (subst T (sym eq-name) tt)))
... | false = there (findSignalInList→SigPresent name ss sig eq)

-- ============================================================================
-- L1: updateSignals WARMS THE CACHE FOR OBSERVED NAMES
-- ============================================================================

-- If `name` appears as the name of some signal in `sigs` and extraction for
-- `name` succeeds on `frame`, then the cache has an entry for `name` after
-- `updateSignals` processes `sigs`.
--
-- Structural induction on `SigPresent`:
--  * `here nameEq` — the head signal's name matches `name`. Write `(name, v)`
--    into the cache via `updateSignals-step-hit` + `lookupCache-updateCache-hit`,
--    then use `updateSignals-monotone` (P23) so the entry survives the
--    remaining signals in the list.
--  * `there pres` — `name` is somewhere deeper in `sigs`. Case-split on the
--    head's extraction outcome: skip (no cache change) or write the head's
--    value (cache grows); both paths recurse structurally on `pres`.
updateSignals-warms : ∀ {n} dbc (frame : CANFrame n) ts name v sigs cache →
  SigPresent name sigs →
  extractTruthValue name dbc frame ≡ just v →
  ∃[ cs ] lookupCache name (updateSignals dbc frame ts sigs cache) ≡ just cs
updateSignals-warms dbc frame ts name v (s ∷ ss) cache (here nameEq) ext =
  let ext' : extractTruthValue (Identifier.name (DBCSignal.name s)) dbc frame ≡ just v
      ext' = subst (λ n → extractTruthValue n dbc frame ≡ just v) (sym nameEq) ext

      step : updateSignals dbc frame ts (s ∷ ss) cache
           ≡ updateSignals dbc frame ts ss (updateCache (Identifier.name (DBCSignal.name s)) v ts cache)
      step = updateSignals-step-hit dbc frame ts s ss cache v ext'

      hit₁ : lookupCache (Identifier.name (DBCSignal.name s)) (updateCache (Identifier.name (DBCSignal.name s)) v ts cache)
           ≡ just (mkCachedSignal v ts)
      hit₁ = lookupCache-updateCache-hit (Identifier.name (DBCSignal.name s)) v ts cache

      mono = updateSignals-monotone dbc frame ts ss
               (updateCache (Identifier.name (DBCSignal.name s)) v ts cache)
               (Identifier.name (DBCSignal.name s)) (mkCachedSignal v ts) hit₁
      cs'    = proj₁ mono
      monoEq = proj₂ mono

      shifted : lookupCache name
                  (updateSignals dbc frame ts ss (updateCache (Identifier.name (DBCSignal.name s)) v ts cache))
              ≡ just cs'
      shifted = subst
                  (λ m → lookupCache m
                            (updateSignals dbc frame ts ss
                               (updateCache (Identifier.name (DBCSignal.name s)) v ts cache))
                          ≡ just cs')
                  nameEq monoEq
  in cs' , trans (cong (lookupCache name) step) shifted
updateSignals-warms dbc frame ts name v (s ∷ ss) cache (there pres) ext
  with extractTruthValue (Identifier.name (DBCSignal.name s)) dbc frame
... | nothing = updateSignals-warms dbc frame ts name v ss cache pres ext
... | just v' = updateSignals-warms dbc frame ts name v ss
                  (updateCache (Identifier.name (DBCSignal.name s)) v' ts cache) pres ext

-- ============================================================================
-- STRUCTURE RECOVERY FROM A SUCCESSFUL EXTRACTION
-- ============================================================================

-- A successful `extractTruthValue` witnesses both a message match and a
-- signal match at that message. Decomposes the nested `with`s of
-- `extractSignalWithContext`; the only non-absurd outcome is
-- `findMessageById ≡ just msg ∧ findSignalByName name msg ≡ just sig`, in
-- which case `extractSignalDirect` must have returned `Success`.
--
-- Proof shape: two nested `with`s, with asymmetric equation handling.
-- * The outer `with findMessageById …` DOES abstract in the goal — the
--   goal mentions `findMessageById …` directly on the LHS of the first
--   equation, so the `just msg` branch commits that slot to `just msg ≡
--   just msg`, filled by `refl`. Un-abstracted at the caller, this becomes
--   `findMessageById … ≡ just msg` as advertised.
-- * The inner `with findSignalByName name msg` does NOT abstract — the
--   goal mentions `findSignalByName name m` where `m` is the outer Σ-bound
--   variable (not yet committed to `msg`), so the inner scrutinee has no
--   syntactic occurrences to abstract. We need `in sigEq` to carry the
--   equation explicitly into the branch, then return `sigEq` itself.
extractTruthValue→msg-sig : ∀ {n} dbc (frame : CANFrame n) name v →
  extractTruthValue name dbc frame ≡ just v →
  ∃[ msg ] ∃[ sig ]
    (findMessageById (CANFrame.id frame) dbc ≡ just msg ×
     findSignalByName name msg ≡ just sig)
extractTruthValue→msg-sig dbc frame name v eq
  with findMessageById (CANFrame.id frame) dbc
... | nothing  = ⊥-elim (nothing≢just eq)
... | just msg with findSignalByName name msg in sigEq
...   | nothing  = ⊥-elim (nothing≢just eq)
...   | just sig = msg , sig , refl , sigEq

-- ============================================================================
-- L2: updateCacheFromFrame WARMS THE CACHE
-- ============================================================================

-- If extraction for `name` succeeds on the frame, then the cache has an
-- entry for `name` after `updateCacheFromFrame`. The proof composes the
-- message/signal decomposition with L1 via `updateCacheFromFrame-match`.
--
-- Uses the `trans (cong _ matchEq) …` template (mirroring Cache.agda's
-- `updateCacheFromFrame-coherent`) rather than `rewrite findEq`, since
-- `findMessageById` appears in both the outer reduction of
-- `updateCacheFromFrame` and the inner reduction of
-- `extractSignalWithContext` — a single `rewrite` would re-abstract both
-- occurrences and leave goal and hypothesis types with different normal
-- forms.
updateCacheFromFrame-warms : ∀ {n} dbc cache ts (frame : CANFrame n) name v →
  extractTruthValue name dbc frame ≡ just v →
  ∃[ cs ] lookupCache name (updateCacheFromFrame dbc cache ts frame) ≡ just cs
updateCacheFromFrame-warms dbc cache ts frame name v ext =
  let decomp  = extractTruthValue→msg-sig dbc frame name v ext
      msg     = proj₁ decomp
      rest₁   = proj₂ decomp
      sig     = proj₁ rest₁
      rest₂   = proj₂ rest₁
      findEq  = proj₁ rest₂
      sigEq   = proj₂ rest₂

      pres : SigPresent name (DBCMessage.signals msg)
      pres = findSignalInList→SigPresent name (DBCMessage.signals msg) sig sigEq

      l1 = updateSignals-warms dbc frame ts name v (DBCMessage.signals msg) cache pres ext
      cs    = proj₁ l1
      l1Eq  = proj₂ l1

      matchEq : updateCacheFromFrame dbc cache ts frame
              ≡ updateSignals dbc frame ts (DBCMessage.signals msg) cache
      matchEq = updateCacheFromFrame-match dbc cache ts frame msg findEq
  in cs , trans (cong (lookupCache name) matchEq) l1Eq

-- ============================================================================
-- CACHE FOLD AND OBSERVATION PREDICATE
-- ============================================================================

-- Trace-level cache update: fold `updateCacheFromFrame` over σ starting
-- from `cache₀`. This is what the streaming pipeline actually computes
-- (up to monotonicity checks, which do not affect the cache state).
cacheAfter : DBC → List TimedFrame → SignalCache → SignalCache
cacheAfter dbc []       cache = cache
cacheAfter dbc (tf ∷ σ) cache =
  cacheAfter dbc σ
    (updateCacheFromFrame dbc cache (timestamp tf) (TimedFrame.frame tf))

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
cacheAfter-monotone : ∀ dbc σ cache name cached →
  lookupCache name cache ≡ just cached →
  ∃[ cached' ] lookupCache name (cacheAfter dbc σ cache) ≡ just cached'
cacheAfter-monotone dbc []       cache name cached eq = cached , eq
cacheAfter-monotone dbc (tf ∷ σ) cache name cached eq =
  let ts     = timestamp tf
      frame  = TimedFrame.frame tf
      step   = updateCacheFromFrame-monotone dbc cache ts frame name cached eq
      c₁     = proj₁ step
      eq₁    = proj₂ step
  in cacheAfter-monotone dbc σ
       (updateCacheFromFrame dbc cache ts frame) name c₁ eq₁

-- If `name` is observed somewhere in σ, then `cacheAfter σ cache` has an
-- entry for `name`. At the observing frame, L2 warms the cache; then
-- `cacheAfter-monotone` carries the entry through the remaining trace.
cacheAfter-warms : ∀ dbc σ cache name →
  ObservedIn dbc name σ →
  ∃[ cs ] lookupCache name (cacheAfter dbc σ cache) ≡ just cs
cacheAfter-warms dbc (tf ∷ σ) cache name (here {v = v} ext) =
  let ts    = timestamp tf
      frame = TimedFrame.frame tf
      l2    = updateCacheFromFrame-warms dbc cache ts frame name v ext
      c₁    = proj₁ l2
      eq₁   = proj₂ l2
  in cacheAfter-monotone dbc σ
       (updateCacheFromFrame dbc cache ts frame) name c₁ eq₁
cacheAfter-warms dbc (tf ∷ σ) cache name (there rest) =
  let ts    = timestamp tf
      frame = TimedFrame.frame tf
  in cacheAfter-warms dbc σ
       (updateCacheFromFrame dbc cache ts frame) name rest

-- ============================================================================
-- L4: STREAMING WARMS CACHE (HEADLINE SA.19.3)
-- ============================================================================

-- Every atom's target signal is observed somewhere in σ. Structural on
-- the atom list; mirrors the shape of `AllCached` so that composition
-- with `streaming-warms-cache` is a direct zip.
AllObserved : DBC → List TimedFrame → List SignalPredicate → Set
AllObserved dbc σ []       = ⊤
AllObserved dbc σ (p ∷ ps) = ObservedIn dbc (signalOf p) σ × AllObserved dbc σ ps

-- Headline theorem closing SA.19.3. Each atom `p`'s target signal is
-- observed in σ ⇒ `AllCached` holds on the cache produced by streaming.
-- Composed with `warm-cache-agreement`, removes the dangling premise
-- that made the streaming-adequacy theorem conditional.
streaming-warms-cache : ∀ dbc σ atoms cache →
  AllObserved dbc σ atoms →
  AllCached (cacheAfter dbc σ cache) atoms
streaming-warms-cache dbc σ []       cache _              = tt
streaming-warms-cache dbc σ (p ∷ ps) cache (obs , obsAll) =
    cacheAfter-warms dbc σ cache (signalOf p) obs
  , streaming-warms-cache dbc σ ps cache obsAll

-- ============================================================================
-- UNCONDITIONAL STREAMING ADEQUACY
-- ============================================================================

-- R21 cluster 1 — AGDA-D-12.1 CLOSED (walker landed via `afd28f3`):
--
-- BACKGROUND.  The `AllObserved` premise on `streaming-adequacy` (line
-- below) is a documented caller obligation.  When violated at runtime
-- (a property's atom whose target signal never appears in trace), the
-- kernel's `finalizeL` returns `Unsure → PropertyResult.Unresolved` —
-- sound (three-valued Kleene Unknown) but indistinguishable from a
-- genuinely undecided property without diagnostic context.
--
-- LANDED:
--   * Scaffold (`85623b7`): `WarningKind` + `Warning` ADTs (UncachedAtom
--     kind), `Response.Complete : List PropertyResult → List Warning
--     → Response`, `formatResponse` adds `warnings:[...]` field to the
--     JSON envelope.
--   * Walker (`afd28f3`): `collectUncachedWarnings` in
--     `Protocol.Handlers` walks each `PropertyState`'s `atoms` list,
--     looks up each atom's `signalOf` in the cache, emits
--     `mkWarning UncachedAtom (toℕ ps.index) (fromList sigName)` on
--     miss; `handleEndStream` populates the wire field via the walker.
--   * Three bindings decode + surface the warnings list:
--       - Python: `CompleteWarning` TypedDict + `CompleteResponse.warnings`
--       - Go:     `StreamWarning` struct + `StreamResult.Warnings`
--       - C++:    `StreamWarning` struct + `StreamResult::warnings`
--     Each binding's `stream.ended` log line records `numWarnings`.
--   * Test trio (Python + Go + C++) asserts that an atom referencing an
--     unobserved signal produces exactly one `uncached_atom` warning at
--     EndStream and that all-observed traces produce none.
--   * Feature matrix row `end_stream_uncached_atom_warnings` declares
--     the parity across bindings; per-binding parity tests pass.
--
-- Soundness rationale: the existing `Unresolved` verdict is still
-- emitted unchanged.  Warnings are additive diagnostic context — they
-- ratify (do not replace or reinterpret) the verdict.
--
-- REQUIRED follow-ups — ✅ CLOSED 2026-05-22 (R22 AGDA-D-12.1 closure):
--   * `LogEvent.endstream.uncached_atom` enumerant — added to
--     `docs/LOG_EVENTS.yaml` (warn, new "End-of-stream diagnostics"
--     section), `python/aletheia/client/_log.py` (`LogEvent`),
--     `go/aletheia/client.go` (slog.LevelWarn emit in `EndStream`),
--     `cpp/src/client.cpp` (`logger_.warn` in
--     `log_end_stream_summary` helper).  Cross-binding parity tests
--     (`test_log_events_parity.{py,go,cpp}` + `test_logging.py
--     TestEndStreamWarnings`) bump the canonical event count 15 → 16
--     and exercise the uncached_atom scenario via mock backend.
--     Per-warning events carry `property_index` + `detail` so
--     operators can grep for specific properties.
--   * `check-runbook` entry — `#### `endstream.uncached_atom``
--     section added under "End-of-stream diagnostics" in
--     `docs/operations/RUNBOOK.md`; `tools/check_runbook_coverage.py`
--     now reports 16/16 covered.
--   * PROTOCOL.md section — `§ End-of-stream Warnings` added under
--     the Complete Response, documenting wire shape (kind /
--     property_index / detail), defined kinds (currently
--     `uncached_atom`), evolution rule (7-step coordinated change
--     when adding a new kind), and the logging mirror.
--
-- DO NOT RE-RAISE in review.  All four pieces (scaffold / walker /
-- bindings / log+runbook+protocol mirror) are durable; cross-binding
-- parity tests + check-runbook gate enforce non-regression.

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
streaming-adequacy : ∀ dbc σ atoms cache₀ (proc : LTLProc) σ'
  → AllObserved dbc σ atoms
  → AllBelow (length atoms) proc
  → runL (mkPredTable dbc (cacheAfter dbc σ cache₀) atoms) proc σ'
    ≡ ⟦ denot (mkPredTable dbc (cacheAfter dbc σ cache₀) atoms) proc ⟧ σ'
streaming-adequacy dbc σ atoms cache₀ proc σ' obs bound =
  warm-cache-agreement dbc (cacheAfter dbc σ cache₀) atoms proc σ'
    (streaming-warms-cache dbc σ atoms cache₀ obs)
    bound
