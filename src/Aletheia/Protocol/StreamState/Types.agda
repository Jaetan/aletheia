-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Streaming protocol state types.
--
-- Purpose: Define state types for the streaming protocol state machine.
-- States: WaitingForDBC → ReadyToStream → Streaming.
-- Types: PropertyState, StreamState (sum type — phase is the constructor).
-- Role: Imported by StreamState (public API) and StreamState.Internals (proof-facing).
--
-- Design: StreamState is a sum type, not a record with a phase field.
-- Each constructor carries only the fields valid in that phase:
--   WaitingForDBC : no fields (waiting for ParseDBC command)
--   ReadyToStream : DBC + properties + cache (DBC parsed, configuring)
--   Streaming     : DBC + properties + prevFrame + cache (active LTL checking)
-- Invalid phase transitions are unrepresentable at the type level.
module Aletheia.Protocol.StreamState.Types where

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache)
open import Aletheia.LTL.Coalgebra using (LTLProc)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- Property with evaluation state for incremental checking.
-- Parameterised by `n`, the total number of properties in the active
-- StreamState's set; `index : Fin n` makes "no out-of-bounds property
-- identifier reaches the wire" structurally true (the wire-side ℕ used
-- by `PropertyResult.Violation`/`Satisfaction`/`Unresolved` is obtained
-- via `Data.Fin.toℕ` only at emission, never as a free input).  Closed
-- via R20 cluster R6-B7.4 — replaces the prior `index : ℕ` design which
-- left "raw ℕ identifier" as an open-shape concern across the streaming
-- pipeline.  Not on the hot path: this index is consulted once per
-- `PropertyResult` constructor call (after a verdict is reached), not on
-- the per-frame predicate dispatch (which keeps a `ℕ` index into the
-- atom table — see the in-source `DEFERRED REFACTOR` block in
-- `Aletheia.Protocol.StreamState.Internals`).
record PropertyState (n : ℕ) : Set where
  constructor mkPropertyState
  field
    index : Fin n
    formula : LTL SignalPredicate    -- Original formula (for display/JSON)
    atoms : List SignalPredicate     -- Collected atomic predicates (for PredTable)
    proc : LTLProc                   -- ℕ-indexed formula state (for stepL)

-- Stream state — phase is encoded in the constructor.
-- WaitingForDBC has no meaningful fields.
-- ReadyToStream and Streaming always carry a DBC (no Maybe).
-- prevFrame only exists in Streaming (unused in ReadyToStream).
-- The leading `(n : ℕ)` is the active property-set size; both phases
-- carry the same `n` so `Fin n` indices are stable across the
-- ReadyToStream → Streaming → ReadyToStream cycle that `handleEndStream`
-- performs without rebuilding the property list.
data StreamState : Set where
  WaitingForDBC : StreamState
  ReadyToStream : (n : ℕ) → DBC → List (PropertyState n) → SignalCache → StreamState
  Streaming     : (n : ℕ) → DBC → List (PropertyState n) → Maybe TimedFrame → SignalCache → StreamState

-- Extract DBC if loaded (ReadyToStream or Streaming).
-- Drop-in replacement for the old StreamState.dbc record accessor.
getDBC : StreamState → Maybe DBC
getDBC WaitingForDBC = nothing
getDBC (ReadyToStream _ dbc _ _) = just dbc
getDBC (Streaming _ dbc _ _ _) = just dbc

-- Initial empty state
initialState : StreamState
initialState = WaitingForDBC
