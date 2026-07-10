-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- BO_TX_BU_ refinement: distribute parsed per-message sender lists
-- back into the `DBCMessage.senders` field.
--
-- The message-level analogue of `TextParser.ValueDescriptions` (the VAL_
-- refine pass).  Structurally simpler in two ways:
--
--   * No per-signal layer.  `senders` lives directly on the message, so the
--     collect/attach pair keys on `DBCMessage.id` alone — there is no inner
--     signal-name dimension (VAL_'s `collectFromSignals` / `attachToSignal`).
--
--   * `collectSenders` emits AT MOST ONE entry per message (a message with
--     an empty sender list contributes nothing), so the recursion is a
--     direct cons-list — no `++` of per-message contributions, hence none of
--     VAL_'s append-splitting prefix lemmas.
--
-- Three runtime entry points mirroring the VAL_ refine pass:
--
--   * `lookup-senders : CANId → List RawMsgSenders → Maybe (List Identifier)`
--     Linear scan; returns the first entry's sender list whose `canId`
--     matches.  Under msg-id uniqueness `collectSenders` produces at most one
--     entry per id, so "first match" is the only match.
--
--   * `attachSenders : List RawMsgSenders → List DBCMessage → List DBCMessage`
--     Walks the messages once, setting each message's `senders` from the
--     matching entry.  Total — silent no-op on unmatched messages.
--
--   * `collectSenders : List DBCMessage → List RawMsgSenders`
--     Inverse of `attachSenders`.  Emits one `mkRawMsgSenders m.id m.senders`
--     per message whose `senders` is non-empty; empty-sender messages
--     contribute nothing (matching the formatter, which emits no BO_TX_BU_
--     line for a message with no extra senders).
--
-- The proof side (`Properties.Aggregator.Refine.Senders`) shows
-- `attachSenders (collectSenders msgs) msgs ≡ msgs` under msg-id uniqueness,
-- and the lifted form needed by the universal aggregator
-- (`attachSenders (collectSenders msgs) (map clearSendersMsg msgs) ≡ msgs`).
--
-- API design discipline: `lookup-senders`'s match predicate and the
-- `prependSenders` collector case-split the sender list at function level
-- (not inline `with`) so external proofs reduce past them without triggering
-- the with-abstraction trap (per `feedback_expose_scrutinee_for_external_
-- rewrite` + `feedback_with_abstraction_traps`).
module Aletheia.DBC.TextParser.Senders where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (⌊_⌋)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (DBCMessage)

-- ============================================================================
-- RAW PAYLOAD — one BO_TX_BU_ line's `(canId, senders)` pair
-- ============================================================================

record RawMsgSenders : Set where
  constructor mkRawMsgSenders
  field
    canId   : CANId
    senders : List Identifier

-- ============================================================================
-- LOOKUP — `canId` lookup in a `List RawMsgSenders`
-- ============================================================================
--
-- Constructor pattern on `mkRawMsgSenders` keeps the function reducing past
-- with-abstraction in proof bodies; the `if ⌊ ⌋` reduces by case analysis
-- once the decidable resolves (proofs `with cid ≟-CANId rcid`).

lookup-senders : CANId → List RawMsgSenders → Maybe (List Identifier)
lookup-senders _   []                               = nothing
lookup-senders cid (mkRawMsgSenders rcid snds ∷ rs) =
  if ⌊ cid ≟-CANId rcid ⌋ then just snds else lookup-senders cid rs

-- ============================================================================
-- ATTACH — distribute a `List RawMsgSenders` into `DBCMessage.senders`
-- ============================================================================
--
-- `attachWithMaybeSenders` is the Maybe-elim helper.  Top-level (not
-- where-bound) so proof-side `cong (attachWithMaybeSenders m) eq` finds the
-- same identity.

attachWithMaybeSenders : DBCMessage → Maybe (List Identifier) → DBCMessage
attachWithMaybeSenders m nothing      = m
attachWithMaybeSenders m (just snds)  = record m { senders = snds }

attachToMessageSenders : List RawMsgSenders → DBCMessage → DBCMessage
attachToMessageSenders rms m =
  attachWithMaybeSenders m (lookup-senders (DBCMessage.id m) rms)

attachSenders : List RawMsgSenders → List DBCMessage → List DBCMessage
attachSenders rms = map (attachToMessageSenders rms)

-- ============================================================================
-- COLLECT — flatten messages with non-empty `senders` to `RawMsgSenders`s
-- ============================================================================
--
-- `prependSenders` case-splits on the sender list explicitly (not inline
-- `with` inside `collectSenders`) so external proofs can rewrite via
-- `cong (prependSenders cid) (snds-eq : m.senders ≡ ...)` without triggering
-- the with-abstraction trap.

prependSenders : CANId → List Identifier
               → List RawMsgSenders → List RawMsgSenders
prependSenders _   []         rest = rest
prependSenders cid (x ∷ snds) rest = mkRawMsgSenders cid (x ∷ snds) ∷ rest

collectSenders : List DBCMessage → List RawMsgSenders
collectSenders []       = []
collectSenders (m ∷ ms) =
  prependSenders (DBCMessage.id m) (DBCMessage.senders m) (collectSenders ms)
