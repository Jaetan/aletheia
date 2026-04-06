{-# OPTIONS --safe --without-K #-}

-- Streaming protocol state machine: public API.
--
-- Purpose: Re-export state types and provide the public frame processing API.
-- States: WaitingForDBC → ReadyToStream → Streaming.
-- Exports: State types (via StreamState.Types), formula indexing helpers
--   (via StreamState.Internals), and frame processing (handleDataFrame).
-- Role: Core state machine used by Handlers and Main.
--
-- Internal helpers (classifyStepResult, stepProperty, mkPredTable, etc.)
-- live in StreamState.Internals for proof access without polluting the public API.
-- Command handlers live in Protocol/Handlers.agda (concern separation).
module Aletheia.Protocol.StreamState where

open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.LTL.SignalPredicate using (SignalCache)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Trace.CANTrace using (TimedFrame; TraceEvent; Data; Error; Remote)
open import Aletheia.Protocol.Iteration using (iterate)
open import Aletheia.Error as Err using (Error; HandlerErr; WithContext; HandlerError; NoDBC; StreamNotStarted)

-- ============================================================================
-- RE-EXPORTS: Types (public)
-- ============================================================================

open import Aletheia.Protocol.StreamState.Types public

-- ============================================================================
-- RE-EXPORTS: Selected internals needed by Handlers (public subset)
-- ============================================================================

-- Handlers needs collectAtoms + indexFormula for property setup.
-- Proof-facing internals (classifyStepResult, mkPredTable, etc.) are
-- available via Aletheia.Protocol.StreamState.Internals.
open import Aletheia.Protocol.StreamState.Internals public
  using (collectAtoms; indexFormula)

-- Private import for use in handleDataFrame below
open import Aletheia.Protocol.StreamState.Internals
  using (updateCacheFromFrame; stepProperty; dispatchIterResult)

-- ============================================================================
-- FRAME PROCESSING (LTL Checking) — public API
-- ============================================================================

-- Process incoming CAN frame with incremental LTL property checking.
--
-- In Streaming phase: updates signal cache, iterates stepProperty over all
-- properties (calling stepL for each), dispatches result to Ack or Violation.
--
-- O(1) Memory: Properties maintain fixed-size LTLProc state (no trace accumulation).
-- Violation Reporting: First violation halts iteration with counterexample evidence.
handleDataFrame : StreamState → TimedFrame → StreamState × Response
handleDataFrame WaitingForDBC tf =
  (WaitingForDBC , Response.Error (WithContext "DataFrame" (HandlerErr NoDBC)))
handleDataFrame state@(ReadyToStream _ _ _) tf =
  (state , Response.Error (WithContext "DataFrame" (HandlerErr StreamNotStarted)))
handleDataFrame (Streaming dbc props prev cache) tf =
  let updatedCache = updateCacheFromFrame dbc cache (TimedFrame.timestamp tf) (TimedFrame.frame tf)
  in dispatchIterResult dbc (iterate (stepProperty dbc cache tf) props) tf updatedCache

-- Dispatch a trace event: data frames go through handleDataFrame,
-- error and remote frames are acknowledged without LTL evaluation
-- (they carry no payload for signal extraction).
handleTraceEvent : StreamState → TraceEvent → StreamState × Response
handleTraceEvent state (Data tf)     = handleDataFrame state tf
handleTraceEvent state (Error _)     = (state , Response.Ack)
handleTraceEvent state (Remote _ _)  = (state , Response.Ack)
