{-# OPTIONS --safe --without-K --no-main #-}

-- Main entry point for Aletheia (JSON streaming protocol).
--
-- Purpose: Process line-delimited JSON requests and emit JSON responses.
-- Protocol: parse_dbc → set_properties → start_stream → data_frames* → end_stream,
--   plus build_frame, extract_all_signals, update_frame, validate_dbc, format_dbc
-- State Machine: WaitingForDBC → ReadyToStream → Streaming
--
-- Compilation: Compiled to Haskell via MAlonzo, called from AletheiaFFI.hs.
-- Integration: Python loads libaletheia-ffi.so via ctypes (direct FFI, no subprocess).
--
-- Exports: processJSONLine (JSON commands), processFrameDirect (binary data frames).
-- State machine logic delegated to Protocol.StreamState.
--
-- Key design: ALL logic lives in Agda (parsing, validation, state, LTL checking).
-- Haskell FFI shim (AletheiaFFI.hs) only handles C-callable exports and state management.
module Aletheia.Main where

open import Data.String using (String; toList; _≟_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (proj₁; _×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; formatJSON; lookupString)
open import Aletheia.Protocol.Routing using (parseCommand)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.StreamState using (StreamState; initialState; getDBC; handleDataFrame; handleTraceEvent)
open import Aletheia.Protocol.Handlers using
  ( processStreamCommand
  ; handleStartStream; handleEndStream; handleFormatDBC
  ; handleExtractAllSignals
  ; handleBuildFrameByIndex; handleUpdateFrameByIndex
  )
open import Aletheia.Trace.CANTrace using (TimedFrame; TraceEvent)
open import Aletheia.CAN.Frame using (CANId; CANFrame; Byte)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrameByIndex; updateFrameByIndex)
open import Aletheia.CAN.BatchExtraction using (IndexedExtractionResults; extractAllSignalsIndexed)
open import Aletheia.CAN.DLC using (DLC; mkDLC; dlcToBytes)
open import Aletheia.Prelude using (ifᵀ_then_else_; mapₑ)
open import Aletheia.Error as Err using
  ( Error; RouteErr; DispatchErr; HandlerErr; WithContext
  ; DispatchError; MissingTypeField; UnknownMessageType; InvalidJSON; RequestNotObject
  ; HandlerError; InvalidDLCCode
  ; formatFrameError
  )
import Aletheia.Protocol.Message as Msg

-- Apply formatJSON ∘ formatResponse to the second component of a state-response pair
wrapJSON : StreamState × Msg.Response → StreamState × String
wrapJSON (s , r) = (s , formatJSON (formatResponse r))

-- ============================================================================
-- JSON Streaming Protocol (helpers extracted for proof access)
-- ============================================================================

-- Try to parse and execute a command from JSON fields
tryParseCommand : StreamState → List (String × JSON) → StreamState × String
tryParseCommand state obj with parseCommand obj
... | inj₁ routeErr = wrapJSON (state , Msg.Response.Error (RouteErr routeErr))
... | inj₂ cmd = wrapJSON (processStreamCommand cmd state)

-- Dispatch by message type field
dispatchCommand : StreamState → List (String × JSON) → StreamState × String
dispatchCommand state obj with lookupString "type" obj
... | nothing = wrapJSON (state , Msg.Response.Error (DispatchErr MissingTypeField))
... | just msgType =
  if ⌊ msgType ≟ "command" ⌋
  then tryParseCommand state obj
  else wrapJSON (state , Msg.Response.Error (DispatchErr (UnknownMessageType msgType)))

-- Handle parsed JSON result
handleParsedJSON : StreamState → Maybe JSON → StreamState × String
handleParsedJSON state nothing = wrapJSON (state , Msg.Response.Error (DispatchErr InvalidJSON))
handleParsedJSON state (just (JObject obj)) = dispatchCommand state obj
handleParsedJSON state (just _) = wrapJSON (state , Msg.Response.Error (DispatchErr RequestNotObject))

-- Process a single JSON line and update stream state.
-- NOINLINE: Required for MAlonzo FFI (ensures symbol is exported to Haskell).
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine = handleParsedJSON state (map proj₁ (runParser parseJSON (toList jsonLine)))

-- ============================================================================
-- BINARY FRAME ENTRY POINT (No JSON parsing)
-- ============================================================================

-- Binary entry point: process a pre-parsed data frame.
-- Called by aletheia_send_frame via AletheiaFFI.hs.
-- No JSON parsing — frame components passed directly by the Haskell shim.
--
-- This calls handleDataFrame directly, then formats the response.
-- The proof obligation (refl) is in Protocol/FrameProcessor/Properties.agda.
processFrameDirect : StreamState → TimedFrame → StreamState × String
{-# NOINLINE processFrameDirect #-}
processFrameDirect state tf = wrapJSON (handleDataFrame state tf)

-- Binary entry point: process a trace event (data, error, or remote frame).
-- Called by aletheia_send_event via AletheiaFFI.hs.
-- Data events delegate to handleDataFrame; error/remote events are acknowledged.
processEventDirect : StreamState → TraceEvent → StreamState × String
{-# NOINLINE processEventDirect #-}
processEventDirect state ev = wrapJSON (handleTraceEvent state ev)

-- ============================================================================
-- DIRECT ENTRY POINTS (No JSON parsing on input)
-- ============================================================================

-- These bypass processJSONLine's JSON parsing and command routing.
-- Called directly from AletheiaFFI.hs with pre-marshalled arguments.

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
processExtractDirect : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamState × String
{-# NOINLINE processExtractDirect #-}
processExtractDirect state canId dlc payload =
  ifᵀ (dlc <ᵇ 16) then
    (λ p → wrapJSON (handleExtractAllSignals canId (mkDLC dlc p) payload state))
  else (state , formatJSON (formatResponse (Msg.Error (HandlerErr InvalidDLCCode))))

-- Build CAN frame from signal index-value pairs (no JSON/string parsing)
processBuildFrameDirect : StreamState → CANId → (dlc : ℕ) → List (ℕ × ℚ) → StreamState × String
{-# NOINLINE processBuildFrameDirect #-}
processBuildFrameDirect state canId dlc signals =
  ifᵀ (dlc <ᵇ 16) then
    (λ p → wrapJSON (handleBuildFrameByIndex canId (mkDLC dlc p) signals state))
  else (state , formatJSON (formatResponse (Msg.Error (HandlerErr InvalidDLCCode))))

-- Update CAN frame signals by index (no JSON/string parsing)
processUpdateFrameDirect : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List (ℕ × ℚ) → StreamState × String
{-# NOINLINE processUpdateFrameDirect #-}
processUpdateFrameDirect state canId dlc payload signals =
  ifᵀ (dlc <ᵇ 16) then
    (λ p → wrapJSON (handleUpdateFrameByIndex canId (mkDLC dlc p) payload signals state))
  else (state , formatJSON (formatResponse (Msg.Error (HandlerErr InvalidDLCCode))))

-- ============================================================================
-- BINARY OUTPUT ENTRY POINTS (No JSON serialization on output)
-- ============================================================================
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
-- CALLER CONTRACT — Timestamp monotonicity:
--   processFrameDirect and processExtractDirect assume monotonically
--   non-decreasing timestamps. Metric LTL operators (MetricEventually,
--   MetricAlways) compute elapsed time via natural subtraction (∸), which
--   clamps to 0 on backward timestamps — silently producing wrong verdicts.
--   All three language bindings (Python, C++, Go) enforce monotonicity at
--   the client level before calling these entry points.

-- Build CAN frame, returning raw bytes instead of JSON-formatted Response.
-- Called by aletheia_build_frame_bin via AletheiaFFI.hs.
-- Bypasses formatResponse/formatJSON entirely — zero string allocation on success.
processBuildFrameBin : StreamState → CANId → (dlc : ℕ) → List (ℕ × ℚ) → StreamState × (String ⊎ Vec Byte (dlcToBytes dlc))
{-# NOINLINE processBuildFrameBin #-}
processBuildFrameBin state canId dlc signals with getDBC state
... | nothing  = (state , inj₁ "DBC not loaded")
... | just dbc = (state , mapₑ formatFrameError (buildFrameByIndex dbc canId dlc signals))

-- Update CAN frame, returning raw bytes instead of JSON-formatted Response.
-- Called by aletheia_update_frame_bin via AletheiaFFI.hs.
processUpdateFrameBin : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List (ℕ × ℚ) → StreamState × (String ⊎ Vec Byte (dlcToBytes dlc))
{-# NOINLINE processUpdateFrameBin #-}
processUpdateFrameBin state canId dlc payload signals with getDBC state
... | nothing  = (state , inj₁ "DBC not loaded")
... | just dbc with updateFrameByIndex dbc canId (record { id = canId ; dlc = dlc ; payload = payload }) signals
...   | inj₁ err   = (state , inj₁ (formatFrameError err))
...   | inj₂ frame = (state , inj₂ (CANFrame.payload frame))

-- Extract signals returning indexed results (no strings on success path).
-- Called by aletheia_extract_signals_bin via AletheiaFFI.hs.
processExtractBin : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamState × (String ⊎ IndexedExtractionResults)
{-# NOINLINE processExtractBin #-}
processExtractBin state canId dlc payload with getDBC state
... | nothing  = (state , inj₁ "DBC not loaded")
... | just dbc = (state , mapₑ formatFrameError (extractAllSignalsIndexed dbc (record { id = canId ; dlc = dlc ; payload = payload })))

