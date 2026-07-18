-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Text-roundtrip-specific well-formedness predicates.
--
-- Extends `Aletheia.DBC.Formatter.WellFormed` with constraints that hold
-- ONLY on the text-format roundtrip path (and not on the JSON-format path
-- it already covers).  Three constraints per signal + one per message,
-- each motivated by a specific lossy region of `TextFormatter.Topology`.
--
-- 1. `NoVectorXXXReceiver` — `emitReceivers-chars []` emits the cantools
--    `Vector__XXX` placeholder; `parseReceiverList` (derived
--    from the Format DSL `canonicalReceiversFmt` via the iso `fwd =
--    mkCanonicalFromList`) parses it back as `[]` directly.  A
--    user-supplied list `[Identifier "Vector__XXX"]` would also emit
--    `"Vector__XXX"`, parse back to `[]` — a non-roundtrip.  We
--    exclude any signal whose receivers list contains an identifier
--    literally named `"Vector__XXX"` (`[]` is fine; `[Vector__XXX]`
--    is not; longer lists cannot contain it either).
--
-- 2. `WellFormedTextPresence` — `emitMuxMarker-chars` emits only the
--    HEAD value of the `When _ (v ∷ vs)` selector list, so `vs ≢ []`
--    means the tail is dropped.  The `parseMuxMarker` parser produces
--    `SelBy v` (singleton) for `m<v>` markers; `resolvePresence` rebuilds
--    `When master (v ∷ [])`.  Multi-value selectors require the deferred
--    `SG_MUL_VAL_` cross-line integration (see TextParser.Topology
--    docstring §"Deferred to later sub-commits").  We restrict every
--    signal's presence to `Always` or `When m (v ∷ [])` (singleton).
--
-- 3. `MasterCoherent` — `findMuxMaster` (formatter, scans for the first
--    `When _ _` signal and pulls its master name) and `findMuxName`
--    (parser, scans for the first signal with `IsMux`/`BothMux` marker
--    and returns its identifier) must agree modulo emit/parse.  This
--    requires: if any `When` slave references master `m`, then a signal
--    with name = `m` and presence = `Always` exists in the same message;
--    every `When` slave references that same `m`; the master signal
--    appears before any signal that uses it (since `findMuxName` returns
--    the first `IsMux` it sees on the parser side, and the formatter's
--    `findMuxMaster` returns the first `When` clause's master name).
--
-- 4. `WellFormedTextMessage` extends `WellFormedMessageRT` with these.
--    (The former `senders ≡ []` constraint was removed: `BO_TX_BU_` now
--    round-trips, with `senders` restored at DBC level by `attachSenders`.)
--
-- All predicates are `Set`-valued data types or records, no proofs.
-- The per-construct roundtrip lemmas discharge them.
module Aletheia.DBC.Formatter.WellFormedText where

open import Data.List using ([])
open import Data.List.NonEmpty using (_∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedMessageRT)


-- ============================================================================
-- PER-SIGNAL TEXT WF
-- ============================================================================

-- Receivers list contains no element with identifier name `"Vector__XXX"`.
-- (`[]` is the empty-list case; the formatter emits the placeholder
-- exactly there and the parser collapses it back to `[]`.  Forbidding
-- `"Vector__XXX"` in any element is the simplest sufficient condition.)
-- `DBCSignal.receivers s : CanonicalReceivers` excludes the
-- singleton-Vector__XXX placeholder by the type-level invariant.  The
-- length≥2 case still admits Vector__XXX (rare third-party wire form);
-- the All-precondition is preserved here for those callers, projected
-- through `.list`.
NoVectorXXXReceiver : DBCSignal → Set
NoVectorXXXReceiver s =
  All (λ r → ¬ (Identifier.name r ≡ toList "Vector__XXX"))
      (CanonicalReceivers.list (DBCSignal.receivers s))

-- Presence is `Always` or a singleton `When m (v ∷ [])` selector.  Multi-
-- value mux selectors are deferred (see module header §2).
data WellFormedTextPresence : SignalPresence → Set where
  wftp-always       : WellFormedTextPresence Always
  wftp-when-single  : ∀ {m v} → WellFormedTextPresence (When m (v ∷ []))

-- Bundle the per-signal text constraints.
--
-- `vds-empty` was removed.  The per-message roundtrip now
-- claims `parseMessage … ≡ just (mkResult (clearVdsMsg msg) … …)` and
-- the Universal layer threads `attachValueDescs ∘ collectFromMessages
-- ≡ id` (Refine bridge) post-buildDBC to recover the original VAL_
-- entries.  No vds-related constraint at the per-signal level.
record WellFormedTextSignal (s : DBCSignal) : Set where
  field
    no-vector-xxx : NoVectorXXXReceiver s
    presence-wf   : WellFormedTextPresence (DBCSignal.presence s)


-- ============================================================================
-- MASTER COHERENCE (PER-MESSAGE)
-- ============================================================================

-- `MasterCoherent` lives in the `Foundations` child module — the runtime
-- checker decides it there without pulling this module's proof-carrying
-- dependencies (`WellFormedMessageRT` and its lemma imports) into the
-- `libaletheia-ffi.so` closure.  Re-exported here for the proof-side
-- consumers, which read the whole predicate family from this module.
open import Aletheia.DBC.Formatter.WellFormedText.Foundations public
  using (MasterCoherent; mc-no-mux; mc-mux)


-- ============================================================================
-- PER-MESSAGE TEXT WF
-- ============================================================================

-- `WellFormedTextMessage m`: extends `WellFormedMessageRT m` with text-
-- specific constraints.  Sufficient (combined with already-existing
-- `bytesToValidDLC-roundtrip`, `buildCANId-rawCanIdℕ` from 3b, and Layer-2
-- primitive roundtrips) to close `parseMessage (emitMessage-chars m)
-- ≡ just (mkResult m _ _)` once the per-construct lemmas land.
record WellFormedTextMessage (m : DBCMessage) : Set where
  field
    msg-wf-rt     : WellFormedMessageRT m
    sigs-text-wf  : All WellFormedTextSignal (DBCMessage.signals m)
    master-coh    : MasterCoherent (DBCMessage.signals m)
    -- The `senders-empty` field was removed — `BO_TX_BU_` now
    -- round-trips (the universal aggregator restores `senders` via
    -- `attachSenders`), so the in-memory `senders` list no longer has to be
    -- empty.  (This record is now used only via the parser-side `MessageWF`
    -- which re-uses its `WellFormedTextPresence` / `MasterCoherent` pieces.)


-- DBC-level text-roundtrip well-formedness lives in
-- `Aletheia.DBC.TextParser.WellFormed.WellFormedTextDBCAgg` (the
-- aggregator predicate consumed by `parseText-on-formatText` in
-- `Substrate.Unsafe`).  The earlier 1-field stub previously named
-- `WellFormedTextDBC` here was superseded by that 8-field record and is
-- removed.
