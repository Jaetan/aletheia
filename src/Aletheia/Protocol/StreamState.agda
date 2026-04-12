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

open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.LTL.SignalPredicate using (SignalCache)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Trace.CANTrace using (TimedFrame; TraceEvent; Data; Error; Remote; timestamp; timestampℕ)
open import Aletheia.Protocol.Iteration using (iterate)
open import Aletheia.Error as Err using (Error; HandlerErr; WithContext; HandlerError; NoDBC; StreamNotStarted; NonMonotonicTimestamp)

-- ============================================================================
-- RE-EXPORTS: Types (public)
-- ============================================================================

open import Aletheia.Protocol.StreamState.Types public

-- Private import for use in handleDataFrame below
open import Aletheia.Protocol.StreamState.Internals
  using (updateCacheFromFrame; stepProperty; dispatchIterResult)

-- ============================================================================
-- FRAME PROCESSING (LTL Checking) — public API
-- ============================================================================

-- Check timestamp monotonicity against the previous frame.
-- Returns just(error) on regression (current < previous), nothing otherwise.
-- First frame (prev = nothing) always accepted.
checkMonotonic : Maybe TimedFrame → TimedFrame → Maybe HandlerError
checkMonotonic nothing _ = nothing
checkMonotonic (just p) tf with timestampℕ tf <ᵇ timestampℕ p
... | false = nothing
... | true  = just (NonMonotonicTimestamp (timestampℕ tf) (timestampℕ p))

-- Process incoming CAN frame with incremental LTL property checking.
--
-- In Streaming phase: enforces timestamp monotonicity against the previous
-- accepted frame, then updates signal cache, iterates stepProperty over all
-- properties (calling stepL for each), dispatches result to Ack or Violation.
--
-- Monotonicity enforcement: metric LTL operators (MetricEventually, MetricAlways)
-- compute elapsed time via natural subtraction (∸), which clamps at 0 on backward
-- timestamps and silently produces wrong verdicts. Backward timestamps are
-- rejected here with a NonMonotonicTimestamp HandlerError; the state's `prev`
-- field is left unchanged so the next frame is checked against the same anchor.
--
-- O(1) Memory: Properties maintain fixed-size LTLProc state (no trace accumulation).
-- Violation Reporting: First violation halts iteration with counterexample evidence.
handleDataFrame : StreamState → TimedFrame → StreamState × Response
handleDataFrame WaitingForDBC tf =
  (WaitingForDBC , Response.Error (WithContext "DataFrame" (HandlerErr NoDBC)))
handleDataFrame state@(ReadyToStream _ _ _) tf =
  (state , Response.Error (WithContext "DataFrame" (HandlerErr StreamNotStarted)))
handleDataFrame state@(Streaming dbc props prev cache) tf with checkMonotonic prev tf
... | just err =
  (state , Response.Error (WithContext "DataFrame" (HandlerErr err)))
... | nothing =
  let updatedCache = updateCacheFromFrame dbc cache (timestampℕ tf) (TimedFrame.frame tf)
  in dispatchIterResult dbc (iterate (stepProperty dbc cache tf) props) tf updatedCache

-- Dispatch a trace event: data frames go through handleDataFrame,
-- error and remote frames are acknowledged without LTL evaluation
-- (they carry no payload for signal extraction).
handleTraceEvent : StreamState → TraceEvent → StreamState × Response
handleTraceEvent state (Data tf)     = handleDataFrame state tf
handleTraceEvent state (Error _)     = (state , Response.Ack)
handleTraceEvent state (Remote _ _)  = (state , Response.Ack)
