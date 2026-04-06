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

open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache)
open import Aletheia.LTL.Coalgebra using (LTLProc)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- Property with evaluation state for incremental checking
record PropertyState : Set where
  constructor mkPropertyState
  field
    index : ℕ
    formula : LTL SignalPredicate    -- Original formula (for display/JSON)
    atoms : List SignalPredicate     -- Collected atomic predicates (for PredTable)
    proc : LTLProc                   -- ℕ-indexed formula state (for stepL)

-- Stream state — phase is encoded in the constructor.
-- WaitingForDBC has no meaningful fields.
-- ReadyToStream and Streaming always carry a DBC (no Maybe).
-- prevFrame only exists in Streaming (unused in ReadyToStream).
data StreamState : Set where
  WaitingForDBC : StreamState
  ReadyToStream : DBC → List PropertyState → SignalCache → StreamState
  Streaming     : DBC → List PropertyState → Maybe TimedFrame → SignalCache → StreamState

-- Extract DBC if loaded (ReadyToStream or Streaming).
-- Drop-in replacement for the old StreamState.dbc record accessor.
getDBC : StreamState → Maybe DBC
getDBC WaitingForDBC = nothing
getDBC (ReadyToStream dbc _ _) = just dbc
getDBC (Streaming dbc _ _ _) = just dbc

-- Initial empty state
initialState : StreamState
initialState = WaitingForDBC
