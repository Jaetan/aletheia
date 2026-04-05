{-# OPTIONS --safe --without-K #-}

-- Streaming protocol state types.
--
-- Purpose: Define state types for the streaming protocol state machine.
-- States: WaitingForDBC → ReadyToStream → Streaming.
-- Types: StreamPhase, PropertyState, StreamState.
-- Role: Imported by StreamState (public API) and StreamState.Internals (proof-facing).
module Aletheia.Protocol.StreamState.Types where

open import Data.List using (List; [])
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache)
open import Aletheia.LTL.Coalgebra using (LTLProc)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- State machine for streaming protocol
data StreamPhase : Set where
  WaitingForDBC : StreamPhase      -- Initial state, waiting for ParseDBC
  ReadyToStream : StreamPhase      -- DBC parsed, waiting for SetProperties or StartStream
  Streaming : StreamPhase          -- Active streaming mode

-- Property with evaluation state for incremental checking
record PropertyState : Set where
  constructor mkPropertyState
  field
    index : ℕ
    formula : LTL SignalPredicate    -- Original formula (for display/JSON)
    atoms : List SignalPredicate     -- Collected atomic predicates (for PredTable)
    proc : LTLProc                   -- ℕ-indexed formula state (for stepL)

-- Complete stream state
record StreamState : Set where
  constructor mkStreamState
  field
    phase : StreamPhase
    dbc : Maybe DBC
    properties : List PropertyState    -- Properties with incremental eval state
    prevFrame : Maybe TimedFrame       -- Previous frame for ChangedBy predicate
    signalCache : SignalCache          -- Last-known signal values for three-valued semantics

-- Initial empty state
initialState : StreamState
initialState = mkStreamState WaitingForDBC nothing [] nothing emptyCache
