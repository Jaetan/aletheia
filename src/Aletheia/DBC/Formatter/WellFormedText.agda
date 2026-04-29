{-# OPTIONS --safe --without-K #-}

-- Text-roundtrip-specific well-formedness predicates (Phase B.3.d Layer 3
-- Commit 3d.1).
--
-- Extends `Aletheia.DBC.Formatter.WellFormed` with constraints that hold
-- ONLY on the text-format roundtrip path (and not on the JSON-format path
-- it already covers).  Three constraints per signal + one per message,
-- each motivated by a specific lossy region of `TextFormatter.Topology`.
--
-- 1. `NoVectorXXXReceiver` — `emitReceivers-chars []` emits the cantools
--    `Vector__XXX` placeholder; `parseReceiverList` (post-ε.3, derived
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
-- 4. `WellFormedTextMessage` extends `WellFormedMessageRT` with these
--    plus an `senders ≡ []` constraint (the `BO_TX_BU_` line is not yet
--    emitted by `TextFormatter.Topology.emitMessage-chars`, so the
--    in-memory `senders` list is dropped on the format path; for the
--    roundtrip to close, the input must already have empty `senders`).
--
-- All predicates are `Set`-valued data types or records, no proofs.
-- 3d.2+ will discharge them in the per-construct roundtrip lemmas.
module Aletheia.DBC.Formatter.WellFormedText where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.Types using
  (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedMessageRT)
open import Aletheia.DBC.TextFormatter.Topology using (findMuxMaster)


-- ============================================================================
-- PER-SIGNAL TEXT WF
-- ============================================================================

-- Receivers list contains no element with identifier name `"Vector__XXX"`.
-- (`[]` is the empty-list case; the formatter emits the placeholder
-- exactly there and the parser collapses it back to `[]`.  Forbidding
-- `"Vector__XXX"` in any element is the simplest sufficient condition.)
-- Post γ.2: `DBCSignal.receivers s : CanonicalReceivers` excludes the
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
record WellFormedTextSignal (s : DBCSignal) : Set where
  field
    no-vector-xxx : NoVectorXXXReceiver s
    presence-wf   : WellFormedTextPresence (DBCSignal.presence s)


-- ============================================================================
-- MASTER COHERENCE (PER-MESSAGE)
-- ============================================================================

-- `MasterCoherent sigs`: either there is no mux in the message
-- (`findMuxMaster sigs ≡ nothing`, i.e. every signal has presence
-- `Always`), or there is a master with all the coherence constraints:
--
--   * `findMuxMaster sigs ≡ just masterName` (some `When` slave exists,
--     and `masterName` is its master's identifier name);
--   * a signal with name matching `masterName` exists in `sigs`, has
--     `presence = Always`, and appears (somewhere) — its position
--     relative to slaves is enforced separately by the parser-side
--     `findMuxName` returning the first `IsMux` marker (which the
--     master is, post-emit);
--   * every `When` slave in `sigs` references the same `masterName`.
--
-- Master *position* (must come before slaves) is currently NOT in the
-- WF — `findMuxMaster` and `findMuxName` both return the first match,
-- so as long as exactly one master exists, the position constraint is
-- automatic.  Multi-master messages are forbidden by point 3 below.

data MasterCoherent : List DBCSignal → Set where
  -- No-mux case: no signal in the list has `When _ _` presence.
  mc-no-mux : ∀ {sigs}
            → findMuxMaster sigs ≡ nothing
            → MasterCoherent sigs

  -- Mux case: one master, every When slave references it.  The master
  -- signal record `masterSig` is exhibited by `Σ`-style witness fields.
  -- Post-3d.4 + JSON-mirror: `findMuxMaster` returns `Maybe (List Char)`
  -- (matching `Identifier.name : List Char`).
  mc-mux : ∀ {sigs}
         → (masterName : List Char)
         → findMuxMaster sigs ≡ just masterName
         -- Master existence (some signal in sigs has name = masterName
         -- and presence = Always).  We carry the full signal record so
         -- downstream proofs can refer to it by name; the `∈` witness
         -- locates it in `sigs` (3d.7 needs this for the parser-side
         -- `findMuxName` resolution proof).
         → (masterSig : DBCSignal)
         → masterSig ∈ sigs
         → Identifier.name (DBCSignal.name masterSig) ≡ masterName
         → DBCSignal.presence masterSig ≡ Always
         -- Every When-clause references masterName.
         → All (λ s → (m : Identifier) (vs : List⁺.List⁺ _)
                    → DBCSignal.presence s ≡ When m vs
                    → Identifier.name m ≡ masterName)
               sigs
         → MasterCoherent sigs


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
    -- BO_TX_BU_ is not yet emitted (see TextFormatter.Topology header
    -- §"BO_TX_BU_ deferred"); the in-memory `senders` list must be empty
    -- for the text roundtrip to close.
    senders-empty : DBCMessage.senders m ≡ []


-- ============================================================================
-- DBC-LEVEL TEXT WF
-- ============================================================================

-- DBC-level extension of `WellFormedDBCRT` for the text-roundtrip path.
-- 3d.x will land the per-message proof; Layer 4 closes the universal via
-- `All`-induction over the message list.
record WellFormedTextDBC (d : DBC) : Set where
  field
    messages-text-wf : All WellFormedTextMessage (DBC.messages d)
