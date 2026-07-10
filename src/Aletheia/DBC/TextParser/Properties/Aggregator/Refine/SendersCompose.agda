-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Composition of the BO_TX_BU_ senders inverse-bridge with the VAL_
-- value-descriptions inverse-bridge.
--
-- `parseMessage` produces messages with BOTH `vds = []` (per signal) AND
-- `senders = []` — i.e. `clearBothMsg msg`.  At `buildDBC`, the two refine
-- passes run nested:
--
--   attachSenders (collectSenders msgs)
--     (attachValueDescs (collectFromMessages msgs) (map clearBothMsg msgs))
--
-- This module closes that nested form to `msgs`.  The reduction reuses the
-- EXISTING per-pass bridges at the ORIGINAL `msgs` (no precondition
-- transfer), exploiting that the two passes touch DISJOINT fields:
--
--   * `attachValueDescs` writes only signals' `valueDescriptions`;
--   * `clearSendersMsg` writes only `senders`;
--   * `attachToMessage` reads `id` + `signals`, both preserved by
--     `clearSendersMsg`.
--
-- So `attachValueDescs X (map clearSendersMsg ms) ≡ map clearSendersMsg
-- (attachValueDescs X ms)` holds DEFINITIONALLY per element (record-η on
-- disjoint fields).  That lets:
--
--   attachValueDescs (cFM msgs) (map clearBothMsg msgs)
--     ≡ map clearSendersMsg msgs                          -- (Step 1)
--
-- via the existing VAL_ bridge at the original `msgs`; then the
-- existing senders lifted bridge closes
--
--   attachSenders (collectSenders msgs) (map clearSendersMsg msgs) ≡ msgs.
--
-- The `unresolvedValueDescs` field of `buildDBC` consumes the same cleared
-- message list, so the unconditional `unresolvedRVDs ≡ []` bridge is lifted
-- to the `clearBothMsg` form here too (senders are ignored by the resolution
-- check, so the existing `clearVds` lemma transports directly).
--
-- The `All MessageWF msgs` hypothesis is forwarded opaquely to the VAL_
-- bridge — its internal field set is never destructured here, so this module
-- is stable across the removal of `MessageWF.senders-
-- empty`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Refine.SendersCompose where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Bool using (true; false; _∨_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; cong; cong₂)

open import Aletheia.DBC.Types using
  (DBCMessage; RawValueDesc; clearVdsMsg; clearSendersMsg; clearBothMsg)
open import Aletheia.DBC.TextParser.ValueDescriptions using
  ( attachValueDescs; attachToMessage; collectFromMessages
  ; unresolvedRVDs; resolvesᵇ-msgs)
open import Aletheia.DBC.TextParser.Senders using
  (collectSenders; attachSenders)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Refine.Senders using
  (attachSenders-on-clearSendersMsgs-collectSenders)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Refine.ValueDescriptions using
  (map-attachToMessage-on-clearVdsMsgs-collected)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Refine.ValueDescriptions.UnresolvedRVDs using
  (unresolvedRVDs-on-clearVdsMsgs-collectFromMessages)
open import Aletheia.DBC.TextParser.Properties.Topology.Message using (MessageWF)

-- ============================================================================
-- clearBothMsg AS A composition OF clearSendersMsg AND clearVdsMsg
-- ============================================================================
--
-- `clearBothMsg = clearSendersMsg ∘ clearVdsMsg` definitionally; lift over
-- `map` (the heads coincide definitionally, so each cons step is `cong`).

map-clearBoth :
    ∀ (msgs : List DBCMessage)
  → map clearBothMsg msgs ≡ map clearSendersMsg (map clearVdsMsg msgs)
map-clearBoth []       = refl
map-clearBoth (m ∷ ms) = cong (clearBothMsg m ∷_) (map-clearBoth ms)

-- ============================================================================
-- DISJOINT-FIELD COMMUTATION — attachValueDescs ↔ clearSendersMsg
-- ============================================================================
--
-- Per element: `attachToMessage rvds (clearSendersMsg m)` and
-- `clearSendersMsg (attachToMessage rvds m)` both normalise to
-- `record m { senders = [] ; signals = … }` — the two record updates touch
-- disjoint fields, so they commute definitionally (`refl` head below).

map-attachToMessage-clearSendersMsg-commute :
    ∀ (rvds : List RawValueDesc) (ms : List DBCMessage)
  → map (attachToMessage rvds) (map clearSendersMsg ms)
    ≡ map clearSendersMsg (map (attachToMessage rvds) ms)
map-attachToMessage-clearSendersMsg-commute _    []       = refl
map-attachToMessage-clearSendersMsg-commute rvds (m ∷ ms) =
  cong₂ _∷_ refl (map-attachToMessage-clearSendersMsg-commute rvds ms)

-- ============================================================================
-- RESOLUTION IS senders-INVARIANT
-- ============================================================================
--
-- `resolvesᵇ-msgs` reads `id` + signal NAMES only (`matchesMsgᵇ` /
-- `matchesSigᵇ`), both preserved by `clearSendersMsg`, so the per-message
-- match is definitionally unchanged (`refl` head).

resolvesᵇ-msgs-clearSenders :
    ∀ (rvd : RawValueDesc) (ms : List DBCMessage)
  → resolvesᵇ-msgs rvd (map clearSendersMsg ms) ≡ resolvesᵇ-msgs rvd ms
resolvesᵇ-msgs-clearSenders _   []       = refl
resolvesᵇ-msgs-clearSenders rvd (m ∷ ms) =
  cong₂ _∨_ refl (resolvesᵇ-msgs-clearSenders rvd ms)

unresolvedRVDs-clearSenders-invariant :
    ∀ (rvds : List RawValueDesc) (ms : List DBCMessage)
  → unresolvedRVDs rvds (map clearSendersMsg ms) ≡ unresolvedRVDs rvds ms
unresolvedRVDs-clearSenders-invariant []         _  = refl
unresolvedRVDs-clearSenders-invariant (rvd ∷ rs) ms
  rewrite resolvesᵇ-msgs-clearSenders rvd ms
  with resolvesᵇ-msgs rvd ms
... | true  = unresolvedRVDs-clearSenders-invariant rs ms
... | false = cong (rvd ∷_) (unresolvedRVDs-clearSenders-invariant rs ms)

-- ============================================================================
-- STEP 1 — attachValueDescs over clearBoth recovers clearSenders
-- ============================================================================

attachValueDescs-on-clearBothMsgs-collected :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachValueDescs (collectFromMessages msgs) (map clearBothMsg msgs)
    ≡ map clearSendersMsg msgs
attachValueDescs-on-clearBothMsgs-collected msgs ids wfs =
  trans
    (cong (map (attachToMessage (collectFromMessages msgs))) (map-clearBoth msgs))
    (trans
      (map-attachToMessage-clearSendersMsg-commute
        (collectFromMessages msgs) (map clearVdsMsg msgs))
      (cong (map clearSendersMsg)
        (map-attachToMessage-on-clearVdsMsgs-collected msgs ids wfs)))

-- ============================================================================
-- COMPOSED BRIDGES — the forms `buildDBC` presents
-- ============================================================================

-- Messages field: nested senders ∘ value-descriptions attach over the
-- doubly-cleared parse output recovers the originals.
attachSenders-attachValueDescs-on-clearBothMsgs-collected :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs)
  → All MessageWF msgs
  → attachSenders (collectSenders msgs)
      (attachValueDescs (collectFromMessages msgs) (map clearBothMsg msgs))
    ≡ msgs
attachSenders-attachValueDescs-on-clearBothMsgs-collected msgs ids wfs =
  trans
    (cong (attachSenders (collectSenders msgs))
      (attachValueDescs-on-clearBothMsgs-collected msgs ids wfs))
    (attachSenders-on-clearSendersMsgs-collectSenders msgs ids)

-- unresolvedValueDescs field: the unconditional `≡ []` bridge lifted to the
-- doubly-cleared message list (senders are ignored by the resolution check).
unresolvedRVDs-on-clearBothMsgs-collectFromMessages :
    ∀ (msgs : List DBCMessage)
  → unresolvedRVDs (collectFromMessages msgs) (map clearBothMsg msgs) ≡ []
unresolvedRVDs-on-clearBothMsgs-collectFromMessages msgs =
  trans
    (cong (unresolvedRVDs (collectFromMessages msgs)) (map-clearBoth msgs))
    (trans
      (unresolvedRVDs-clearSenders-invariant
        (collectFromMessages msgs) (map clearVdsMsg msgs))
      (unresolvedRVDs-on-clearVdsMsgs-collectFromMessages msgs))
