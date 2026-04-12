{-# OPTIONS --safe --without-K --no-main #-}

-- Binary entry points (no JSON parsing on input and/or output).
--
-- Purpose: Direct binary frame processing, bypassing JSON parsing/serialization.
-- Called from AletheiaFFI.hs with pre-marshalled arguments.
--
-- Two categories:
--   *Direct  — binary input, JSON output (formatJSON on response)
--   *Bin     — binary input, binary output (raw bytes / IndexedExtractionResults)
--
-- Wire format (canonical documentation — AletheiaFFI.hs references this):
--
-- processBuildFrameBin / processUpdateFrameBin:
--   Success: raw frame bytes (Vec Byte n) written to caller-provided buffer.
--   Error:   error string via outErr pointer; return code 1.
--
-- processExtractBin:
--   Success: Haskell-allocated buffer (free with aletheia_free_buf).
--   Layout:
--     Header:  3 × u16 (nValues, nErrors, nAbsent)
--     Values:  nValues × (signal_index:u16, numerator:i64, denominator:i64) = 18 bytes each
--     Errors:  nErrors × (signal_index:u16, error_code:u8) = 3 bytes each
--              Error codes: 0=not_in_dbc, 1=out_of_bounds, 2=extraction_failed
--     Absent:  nAbsent × (signal_index:u16) = 2 bytes each
--   Error:   error string via outErr pointer; return code 1.
--
-- Byte order: native (platform-dependent; little-endian on x86_64/aarch64).
-- Multi-byte integers (u16, i64) use the host's native byte order via Haskell's
-- Storable poke. All three language bindings run on the same host, so this is safe.
--
-- Timestamp monotonicity enforcement:
--   handleDataFrame rejects backward timestamps with a NonMonotonicTimestamp
--   HandlerError (see Protocol/StreamState.agda:checkMonotonic). This is the
--   single source of truth across all bindings; metric LTL operators
--   (MetricEventually, MetricAlways) compute elapsed time via natural
--   subtraction (∸) which would otherwise clamp to 0 on backward timestamps
--   and silently produce wrong verdicts. See FrameProcessor/Properties.agda
--   PROPERTY 28 for the correctness proofs.
module Aletheia.Main.Binary where

open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Maybe using (nothing; just)
open import Data.Sum using (_⊎_; inj₁; inj₂; map)

open import Aletheia.Protocol.JSON using (formatJSON)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.StreamState using (StreamState; getDBC; handleDataFrame; handleTraceEvent)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.Protocol.Handlers using
  ( handleStartStream; handleEndStream; handleFormatDBC
  ; handleExtractAllSignals
  ; handleBuildFrameByIndex; handleUpdateFrameByIndex
  )
open import Aletheia.Trace.CANTrace using (TimedFrame; TraceEvent)
open import Aletheia.CAN.Frame using (CANId; CANFrame; Byte)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrameByIndex; updateFrameByIndex)
open import Aletheia.CAN.BatchExtraction using (IndexedExtractionResults; extractAllSignalsIndexed)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.Prelude using (mapₑ)
open import Aletheia.Error using
  ( NoDBC
  ; formatFrameError; formatHandlerError
  )
import Aletheia.Protocol.Message as Msg

-- Apply formatJSON ∘ formatResponse to the second component of a state-response pair.
-- Shared with Main/JSON.agda to avoid duplication.
wrapJSON : StreamState × Msg.Response → StreamState × String
wrapJSON (s , r) = (s , formatJSON (formatResponse r))

-- ============================================================================
-- DIRECT ENTRY POINTS (binary input, JSON output)
-- ============================================================================

-- Binary entry point: process a pre-parsed data frame.
processFrameDirect : StreamState → TimedFrame → StreamState × String
{-# NOINLINE processFrameDirect #-}
processFrameDirect state tf = wrapJSON (handleDataFrame state tf)

-- Binary entry point: process a trace event (data, error, or remote frame).
processEventDirect : StreamState → TraceEvent → StreamState × String
{-# NOINLINE processEventDirect #-}
processEventDirect state ev = wrapJSON (handleTraceEvent state ev)

-- Start streaming mode (no input data)
processStartStreamDirect : StreamState → StreamState × String
{-# NOINLINE processStartStreamDirect #-}
processStartStreamDirect state = wrapJSON (handleStartStream state)

-- End streaming mode and finalize properties (no input data)
processEndStreamDirect : StreamState → StreamState × String
{-# NOINLINE processEndStreamDirect #-}
processEndStreamDirect state = wrapJSON (handleEndStream state)

-- Format currently-loaded DBC as JSON (no input data)
processFormatDBCDirect : StreamState → StreamState × String
{-# NOINLINE processFormatDBCDirect #-}
processFormatDBCDirect state = wrapJSON (handleFormatDBC state)

-- Extract all signals from a binary CAN frame (no JSON input parsing)
processExtractDirect : StreamState → CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamState × String
{-# NOINLINE processExtractDirect #-}
processExtractDirect state canId dlc payload =
  wrapJSON (handleExtractAllSignals canId dlc payload state)

-- Build CAN frame from signal index-value pairs (no JSON/string parsing)
processBuildFrameDirect : StreamState → CANId → (dlc : DLC) → List (ℕ × ℚ) → StreamState × String
{-# NOINLINE processBuildFrameDirect #-}
processBuildFrameDirect state canId dlc signals =
  wrapJSON (handleBuildFrameByIndex canId dlc signals state)

-- Update CAN frame signals by index (no JSON/string parsing)
processUpdateFrameDirect : StreamState → CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List (ℕ × ℚ) → StreamState × String
{-# NOINLINE processUpdateFrameDirect #-}
processUpdateFrameDirect state canId dlc payload signals =
  wrapJSON (handleUpdateFrameByIndex canId dlc payload signals state)

-- ============================================================================
-- BINARY OUTPUT ENTRY POINTS (binary input, binary output)
-- ============================================================================

-- Common pattern: check for loaded DBC, return error string on missing.
private
  withDBCBin : ∀ {A : Set} → StreamState → (DBC → String ⊎ A) → StreamState × (String ⊎ A)
  withDBCBin state f with getDBC state
  ... | nothing  = (state , inj₁ (formatHandlerError NoDBC))
  ... | just dbc = (state , f dbc)

-- Build CAN frame, returning raw bytes instead of JSON-formatted Response.
processBuildFrameBin : StreamState → CANId → (dlc : DLC) → List (ℕ × ℚ) → StreamState × (String ⊎ Vec Byte (dlcBytes dlc))
{-# NOINLINE processBuildFrameBin #-}
processBuildFrameBin state canId dlc signals =
  withDBCBin state λ dbc → mapₑ formatFrameError (buildFrameByIndex dbc canId dlc signals)

-- Update CAN frame, returning raw bytes instead of JSON-formatted Response.
processUpdateFrameBin : StreamState → CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List (ℕ × ℚ) → StreamState × (String ⊎ Vec Byte (dlcBytes dlc))
{-# NOINLINE processUpdateFrameBin #-}
processUpdateFrameBin state canId dlc payload signals =
  withDBCBin state λ dbc → map formatFrameError CANFrame.payload
    (updateFrameByIndex dbc canId (record { id = canId ; dlc = dlc ; payload = payload }) signals)

-- Extract signals returning indexed results (no strings on success path).
processExtractBin : StreamState → CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamState × (String ⊎ IndexedExtractionResults)
{-# NOINLINE processExtractBin #-}
processExtractBin state canId dlc payload =
  withDBCBin state λ dbc → mapₑ formatFrameError (extractAllSignalsIndexed dbc (record { id = canId ; dlc = dlc ; payload = payload }))
