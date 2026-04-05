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

open import Data.String using (String; toList; _≟_) renaming (_++_ to _++ₛ_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (proj₁; _×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; formatJSON; lookupString)
open import Aletheia.Protocol.Routing using (parseCommand)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.StreamState using (StreamState; initialState; handleDataFrame; handleTraceEvent)
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
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.Prelude using (errNoDBC)
import Aletheia.Protocol.Message as Msg

-- ============================================================================
-- Phase 2B: JSON Streaming Protocol
-- ============================================================================

-- Process a single JSON line and update stream state
--
-- Algorithm:
--   1. Parse JSON string → Maybe JSON
--   2. Validate JSON is an object with "type" field
--   3. Route by type: "command" → command handler
--   4. Update state machine and generate response
--   5. Format response as JSON string
--
-- Error Handling:
--   - Graceful degradation: invalid input → error response, state unchanged
--   - Descriptive error messages at each parsing stage (JSON parse, type field, routing)
--   - parseCommand returns error messages for detailed context
--
-- State Threading:
--   - State flows through: handleParsedJSON → routing → handler → response
--   - On error: original state returned unchanged
--   - On success: new state from handler (DBC parse, properties set, stream update)
--
-- NOINLINE Pragma:
--   - Required for MAlonzo FFI: ensures symbol is exported to Haskell
--   - Without this, Agda might inline the function and break FFI linkage
--   - Haskell shim calls this by mangled name (detected at build time)
--
-- Returns: (new state, JSON response string)
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine = handleParsedJSON (map proj₁ (runParser parseJSON (toList jsonLine)))
  where
    -- Try to parse command with detailed tracing
    tryParseCommand : List (String × JSON) → StreamState × String
    tryParseCommand obj with parseCommand obj
    ... | inj₁ errMsg = (state , formatJSON (formatResponse (Msg.Response.Error errMsg)))
    ... | inj₂ cmd =
          let (newState , response) = processStreamCommand cmd state
          in (newState , formatJSON (formatResponse response))

    -- Dispatch by message type
    dispatchMessage : JSON → StreamState × String
    dispatchMessage (JObject obj) =
      let typeField = lookupString "type" obj
      in case_type typeField obj
      where
        case_type : Maybe String → List (String × JSON) → StreamState × String
        case_type nothing obj = (state , formatJSON (formatResponse (Msg.Response.Error "Missing 'type' field in request")))
        case_type (just msgType) obj =
          if ⌊ msgType ≟ "command" ⌋
          then tryParseCommand obj
          else (state , formatJSON (formatResponse (Msg.Response.Error ("Unknown message type: " ++ₛ msgType))))
    dispatchMessage json = (state , formatJSON (formatResponse (Msg.Response.Error "Request must be a JSON object")))

    handleParsedJSON : Maybe JSON → StreamState × String
    handleParsedJSON nothing = (state , formatJSON (formatResponse (Msg.Response.Error "Invalid JSON")))
    handleParsedJSON (just (JObject obj)) = dispatchMessage (JObject obj)
    handleParsedJSON (just _) = (state , formatJSON (formatResponse (Msg.Response.Error "Request must be a JSON object")))

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
processFrameDirect state tf =
  let (newState , response) = handleDataFrame state tf
  in (newState , formatJSON (formatResponse response))

-- Binary entry point: process a trace event (data, error, or remote frame).
-- Called by aletheia_send_event via AletheiaFFI.hs.
-- Data events delegate to handleDataFrame; error/remote events are acknowledged.
processEventDirect : StreamState → TraceEvent → StreamState × String
{-# NOINLINE processEventDirect #-}
processEventDirect state ev =
  let (newState , response) = handleTraceEvent state ev
  in (newState , formatJSON (formatResponse response))

-- ============================================================================
-- DIRECT ENTRY POINTS (No JSON parsing on input)
-- ============================================================================

-- These bypass processJSONLine's JSON parsing and command routing.
-- Called directly from AletheiaFFI.hs with pre-marshalled arguments.

-- Start streaming mode (no input data)
processStartStreamDirect : StreamState → StreamState × String
{-# NOINLINE processStartStreamDirect #-}
processStartStreamDirect state =
  let (newState , response) = handleStartStream state
  in (newState , formatJSON (formatResponse response))

-- End streaming mode and finalize properties (no input data)
processEndStreamDirect : StreamState → StreamState × String
{-# NOINLINE processEndStreamDirect #-}
processEndStreamDirect state =
  let (newState , response) = handleEndStream state
  in (newState , formatJSON (formatResponse response))

-- Format currently-loaded DBC as JSON (no input data)
processFormatDBCDirect : StreamState → StreamState × String
{-# NOINLINE processFormatDBCDirect #-}
processFormatDBCDirect state =
  let (newState , response) = handleFormatDBC state
  in (newState , formatJSON (formatResponse response))

-- Extract all signals from a binary CAN frame (no JSON input parsing)
processExtractDirect : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamState × String
{-# NOINLINE processExtractDirect #-}
processExtractDirect state canId dlc payload =
  let (newState , response) = handleExtractAllSignals canId dlc payload state
  in (newState , formatJSON (formatResponse response))

-- Build CAN frame from signal index-value pairs (no JSON/string parsing)
processBuildFrameDirect : StreamState → CANId → (dlc : ℕ) → List (ℕ × ℚ) → StreamState × String
{-# NOINLINE processBuildFrameDirect #-}
processBuildFrameDirect state canId dlc signals =
  let (newState , response) = handleBuildFrameByIndex canId dlc signals state
  in (newState , formatJSON (formatResponse response))

-- Update CAN frame signals by index (no JSON/string parsing)
processUpdateFrameDirect : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List (ℕ × ℚ) → StreamState × String
{-# NOINLINE processUpdateFrameDirect #-}
processUpdateFrameDirect state canId dlc payload signals =
  let (newState , response) = handleUpdateFrameByIndex canId dlc payload signals state
  in (newState , formatJSON (formatResponse response))

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
processBuildFrameBin state canId dlc signals with StreamState.dbc state
... | nothing  = (state , inj₁ errNoDBC)
... | just dbc = (state , buildFrameByIndex dbc canId dlc signals)

-- Update CAN frame, returning raw bytes instead of JSON-formatted Response.
-- Called by aletheia_update_frame_bin via AletheiaFFI.hs.
processUpdateFrameBin : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List (ℕ × ℚ) → StreamState × (String ⊎ Vec Byte (dlcToBytes dlc))
{-# NOINLINE processUpdateFrameBin #-}
processUpdateFrameBin state canId dlc payload signals with StreamState.dbc state
... | nothing  = (state , inj₁ errNoDBC)
... | just dbc with updateFrameByIndex dbc canId (record { id = canId ; dlc = dlc ; payload = payload }) signals
...   | inj₁ err   = (state , inj₁ err)
...   | inj₂ frame = (state , inj₂ (CANFrame.payload frame))

-- Extract signals returning indexed results (no strings on success path).
-- Called by aletheia_extract_signals_bin via AletheiaFFI.hs.
processExtractBin : StreamState → CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamState × (String ⊎ IndexedExtractionResults)
{-# NOINLINE processExtractBin #-}
processExtractBin state canId dlc payload with StreamState.dbc state
... | nothing  = (state , inj₁ errNoDBC)
... | just dbc = (state , extractAllSignalsIndexed dbc (record { id = canId ; dlc = dlc ; payload = payload }))

