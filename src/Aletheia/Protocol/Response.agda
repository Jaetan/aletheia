-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- LTL property result types for the streaming protocol.
--
-- Purpose: Define PropertyResult and CounterexampleData for LTL checking.
-- Types: CounterexampleData (violation evidence), PropertyResult
--        (Violation/Satisfaction/Unresolved).
-- Role: Used by Protocol.StreamState, Protocol.Message, and Protocol.ResponseFormat.
module Aletheia.Protocol.Response where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Aletheia.Trace.Time using (Timestamp; μs)
open import Aletheia.LTL.Incremental using (LTLReason)

-- Counterexample data for LTL violations.
-- The reason is a closed `LTLReason` ADT — `Protocol.ResponseFormat` calls
-- `formatLTLReason` at the JSON boundary so user-visible strings remain
-- byte-stable while the core never traffics in display strings.
record CounterexampleData : Set where
  constructor mkCounterexampleData
  field
    timestamp : Timestamp μs  -- Timestamp (microseconds) of violating frame
    reason : LTLReason        -- Closed reason ADT (formatted at JSON boundary)

-- Property checking result for streaming protocol.
-- Emitted when a property is decided (early termination or at EndStream).
--
-- Three verdicts, aligned with the three-valued Kleene FinalVerdict in
-- LTL.Incremental (Holds / Fails / Unsure). Unresolved is produced at
-- end-of-stream when the coalgebra's finalizeL returns Unsure — most
-- commonly when an atomic predicate's signal was never observed on the
-- trace, so neither satisfaction nor violation can be proved. The
-- denotational semantics agrees this is Unknown, so reporting it as a
-- distinct verdict (rather than collapsing to Fails) is both more honest
-- and easier for users to debug than silently flipping to failure.
data PropertyResult : Set where
  -- Property violated (failed early or at EndStream)
  Violation    : ℕ → CounterexampleData → PropertyResult
  -- Property satisfied (succeeded early or at EndStream)
  Satisfaction : ℕ → PropertyResult
  -- Property inconclusive at EndStream (Kleene Unknown — reason ADT formatted
  -- at the JSON boundary, same convention as CounterexampleData.reason)
  Unresolved   : ℕ → LTLReason → PropertyResult

-- ============================================================================
-- WARNINGS
-- ============================================================================

-- Cache-miss-class warnings emitted at EndStream alongside the property
-- verdicts.  Closes the diagnostic-context gap: a property
-- whose atom's target signal never appears in trace returns `Unresolved`
-- (sound — three-valued Kleene Unknown) but the user previously had no way
-- to distinguish a cache-miss `Unresolved` from a genuine Kleene-undecidable
-- `Unresolved`.  Walking the property atoms at EndStream and emitting one
-- warning per uncached atom ratifies the existing outcome with diagnostic
-- context.
--
-- Wire shape: `Warning` is currently single-kind (`UncachedAtom`).  Future
-- warning classes go here as new `WarningKind` constructors; the wire
-- envelope is a `{kind: string, property_index: int, detail: string}` JSON
-- object so adding kinds is non-breaking for binding parsers (unknown kind
-- → unknown-warning stub, do-not-fail).
data WarningKind : Set where
  -- Atom's target signal was never extracted from any frame on this trace.
  UncachedAtom : WarningKind

-- A single EndStream warning carrying the kind, the property index (`Fin n`
-- via `toℕ` at emit, mirroring PropertyResult's wire boundary), and a
-- free-text detail string (typically the atom's signal name).
record Warning : Set where
  constructor mkWarning
  field
    kind          : WarningKind
    propertyIndex : ℕ
    detail        : String
