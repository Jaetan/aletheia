-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K --no-main #-}

-- Binary entry points (no JSON parsing on input and/or output).
--
-- Purpose: Direct binary frame processing, bypassing JSON parsing/serialization.
--
-- The `*Raw` entries are the ones AletheiaFFI.hs calls.  They take frames and
-- signal values as the C caller handed them in, as builtins only (ℕ, ℤ,
-- Bool, List, Maybe), so the shim applies no kernel constructor; they parse
-- them with `CAN.Frame.Parse`, refusing with the typed `ParseError`, and pass
-- the parsed values to the typed entries, which the protocol properties are
-- stated over.
--
-- Two categories:
--   *Direct  — binary input, JSON output (formatJSON on response)
--   *Bin     — binary input, binary output (raw bytes / IndexedExtractionResults)
--
-- Wire format (canonical documentation — AletheiaFFI.hs references this):
--
-- processBuildFrameRaw / processUpdateFrameRaw:
--   Success: the frame's bytes, written to the caller-provided buffer.
--   Error:   the JSON error envelope (`formatErrorEnvelope`) via the buffer's
--            error pointer; return code 1.
--
-- processExtractBinRaw:
--   Success: Haskell-allocated buffer (free with aletheia_free_buf).
--   Layout (offsets-table variant — every segment start is O(1) arithmetic
--   from the header; reason i is an O(1) slice):
--     Header:  3 × u16 (nValues, nErrors, nAbsent) + u32 reasonBytes
--     Values:  nValues × (signal_index:u16, numerator:i64, denominator:i64) = 18 bytes each
--     Errors:  nErrors × (signal_index:u16, error_code:u8) = 3 bytes each
--              Error codes: the u8 values pinned by extractionErrorCodeToℕ
--              (CAN/BatchExtraction.agda — one distinct code per
--              distinguishable error; injectivity machine-checked in
--              Batch.Properties.ReasonParity).
--     Offsets: (nErrors + 1) × u32 — cumulative byte offsets into Reasons;
--              off[0] = 0, monotone non-decreasing, off[nErrors] = reasonBytes.
--              Decoders MUST verify all three before slicing.
--     Reasons: reasonBytes of UTF-8; error i's reason = bytes [off[i], off[i+1]).
--              Same strings the JSON path formats (shared resultToString;
--              machine-checked reason-parity).
--     Absent:  nAbsent × (signal_index:u16) = 2 bytes each
--   Error:   the JSON error envelope via the buffer's error pointer; return
--            code 1.
--
-- Byte order: native (platform-dependent; little-endian on x86_64/aarch64).
-- Multi-byte integers (u16, i64) use the host's native byte order via Haskell's
-- Storable poke. Every binding runs on the same host, so this is safe.
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

open import Data.Bool using (Bool)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec; toList)
open import Data.Maybe using (Maybe)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to bimapₑ)
open import Function.Base using (id)

open import Aletheia.Protocol.JSON using (formatJSON)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.StreamState using (StreamState; WaitingForDBC; ReadyToStream; Streaming; handleDataFrame; handleTraceEvent)
open import Aletheia.DBC.Validity using (ValidDBC)
open import Aletheia.Protocol.Handlers using
  ( handleStartStream; handleEndStream; handleFormatDBC
  ; handleExtractAllSignals
  )
open import Aletheia.Trace.CANTrace using (TimedFrame; TraceEvent; Error; Remote)
open import Aletheia.Trace.Time using (mkTs)
open import Aletheia.CAN.Frame using (CANId; CANFrame; Byte)
open import Aletheia.CAN.Frame.Parse using (parseCANId; parseDLC; parseCANFrame; parseTimedFrame; parseSignalValues)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrameByIndex; updateFrameByIndex)
open import Aletheia.CAN.BatchExtraction using (IndexedExtractionResults; extractAllSignalsIndexed)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.Prelude using (mapₑ)
open import Aletheia.Error using (NoDBC; HandlerErr; FrameErr; ParseErr) renaming (Error to Err)
import Aletheia.Protocol.Message as Msg

-- Apply formatJSON ∘ formatResponse to the second component of a state-response pair.
-- Shared with Main/JSON.agda to avoid duplication.
wrapJSON : StreamState × Msg.Response → StreamState × String
wrapJSON (s , r) = (s , formatJSON (formatResponse r))

-- The JSON error envelope a binary-output entry hands back on refusal: the
-- same `{"status": "error", "code": …}` shape every JSON entry answers with.
formatErrorEnvelope : Err → String
formatErrorEnvelope e = formatJSON (formatResponse (Msg.Response.Error e))

-- ============================================================================
-- DIRECT ENTRY POINTS (binary input, JSON output)
-- ============================================================================

-- Process a parsed data frame.
processFrameDirect : StreamState → TimedFrame → StreamState × String
{-# NOINLINE processFrameDirect #-}
processFrameDirect state tf = wrapJSON (handleDataFrame state tf)

-- Process a trace event (data, error, or remote frame).
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

-- Extract all signals from a parsed frame.
processExtractDirect : ∀ {n} → StreamState → CANFrame n → StreamState × String
{-# NOINLINE processExtractDirect #-}
processExtractDirect state frame = wrapJSON (handleExtractAllSignals frame state)

-- ============================================================================
-- BINARY OUTPUT ENTRY POINTS (binary input, binary output)
-- ============================================================================

private
  -- Hand the loaded, validated DBC to `f`; refuse with `NoDBC` when there is
  -- none.
  withDBCBin : ∀ {A : Set} → StreamState → (ValidDBC → Err ⊎ A) → StreamState × (Err ⊎ A)
  withDBCBin state@WaitingForDBC              _ = (state , inj₁ (HandlerErr NoDBC))
  withDBCBin state@(ReadyToStream _ vdbc _ _) f = (state , f vdbc)
  withDBCBin state@(Streaming _ vdbc _ _ _)   f = (state , f vdbc)

-- Build a frame from signal values, returning its bytes.
processBuildFrameBin : StreamState → CANId → (dlc : DLC) → List (ℕ × ℚ) → StreamState × (Err ⊎ Vec Byte (dlcBytes dlc))
{-# NOINLINE processBuildFrameBin #-}
processBuildFrameBin state canId dlc signals =
  withDBCBin state λ vdbc → mapₑ FrameErr (buildFrameByIndex vdbc canId dlc signals)

-- Update a frame's signals, returning its bytes.
processUpdateFrameBin : ∀ {n} → StreamState → CANFrame n → List (ℕ × ℚ) → StreamState × (Err ⊎ Vec Byte n)
{-# NOINLINE processUpdateFrameBin #-}
processUpdateFrameBin state frame signals =
  withDBCBin state λ vdbc → bimapₑ FrameErr CANFrame.payload
    (updateFrameByIndex vdbc (CANFrame.id frame) frame signals)

-- Extract signals returning indexed results (no strings on success path).
processExtractBin : ∀ {n} → StreamState → CANFrame n → StreamState × (Err ⊎ IndexedExtractionResults)
{-# NOINLINE processExtractBin #-}
processExtractBin state frame =
  withDBCBin state λ vdbc → mapₑ FrameErr (extractAllSignalsIndexed (ValidDBC.dbc vdbc) frame)

-- ============================================================================
-- RAW ENTRY POINTS (what AletheiaFFI.hs calls: builtins in, parsed here)
-- ============================================================================

-- A data frame as the caller handed it in: timestamp, identifier and its
-- extended flag, DLC code, payload bytes, and the CAN-FD BRS / ESI bits.
processFrameRaw : StreamState → (timestamp raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ) (brs esi : Maybe Bool)
                → StreamState × String
{-# NOINLINE processFrameRaw #-}
processFrameRaw state ts raw ext code bytes brs esi with parseTimedFrame ts raw ext code bytes brs esi
... | inj₁ e  = wrapJSON (state , Msg.Response.Error (ParseErr e))
... | inj₂ tf = processFrameDirect state tf

-- An error frame: its timestamp only.
processErrorFrameRaw : StreamState → (timestamp : ℕ) → StreamState × String
{-# NOINLINE processErrorFrameRaw #-}
processErrorFrameRaw state ts = processEventDirect state (Error (mkTs ts))

-- A remote frame: timestamp and identifier.
processRemoteFrameRaw : StreamState → (timestamp raw : ℕ) (extended : Bool) → StreamState × String
{-# NOINLINE processRemoteFrameRaw #-}
processRemoteFrameRaw state ts raw ext with parseCANId raw ext
... | inj₁ e     = wrapJSON (state , Msg.Response.Error (ParseErr e))
... | inj₂ canId = processEventDirect state (Remote (mkTs ts) canId)

-- Extract every signal of a frame, answering in JSON.
processExtractRaw : StreamState → (raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ) → StreamState × String
{-# NOINLINE processExtractRaw #-}
processExtractRaw state raw ext code bytes with parseCANFrame raw ext code bytes
... | inj₁ e           = wrapJSON (state , Msg.Response.Error (ParseErr e))
... | inj₂ (_ , frame) = processExtractDirect state frame

private
  -- The bytes of a binary-output result, as the builtin list the shim reads.
  asList : ∀ {n} → StreamState × (Err ⊎ Vec Byte n) → StreamState × (Err ⊎ List Byte)
  asList (state , result) = (state , bimapₑ id toList result)

-- Build a frame from signal values given as parallel arrays.  The
-- identifier, the DLC and the values are refused in that order.
processBuildFrameRaw : StreamState → (raw : ℕ) (extended : Bool) (code : ℕ)
                     → (indices : List ℕ) (numerators denominators : List ℤ)
                     → StreamState × (Err ⊎ List Byte)
{-# NOINLINE processBuildFrameRaw #-}
processBuildFrameRaw state raw ext code is ns ds with parseCANId raw ext
... | inj₁ e = (state , inj₁ (ParseErr e))
... | inj₂ canId with parseDLC code
...   | inj₁ e = (state , inj₁ (ParseErr e))
...   | inj₂ dlc with parseSignalValues is ns ds
...     | inj₁ e    = (state , inj₁ (ParseErr e))
...     | inj₂ sigs = asList (processBuildFrameBin state canId dlc sigs)

-- Update a frame's signals, the frame and the values given raw; the frame
-- is refused before the values.
processUpdateFrameRaw : StreamState → (raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ)
                      → (indices : List ℕ) (numerators denominators : List ℤ)
                      → StreamState × (Err ⊎ List Byte)
{-# NOINLINE processUpdateFrameRaw #-}
processUpdateFrameRaw state raw ext code bytes is ns ds with parseCANFrame raw ext code bytes
... | inj₁ e = (state , inj₁ (ParseErr e))
... | inj₂ (_ , frame) with parseSignalValues is ns ds
...   | inj₁ e    = (state , inj₁ (ParseErr e))
...   | inj₂ sigs = asList (processUpdateFrameBin state frame sigs)

-- Extract signals with binary output, the frame given raw.
processExtractBinRaw : StreamState → (raw : ℕ) (extended : Bool) (code : ℕ) (bytes : List ℕ)
                     → StreamState × (Err ⊎ IndexedExtractionResults)
{-# NOINLINE processExtractBinRaw #-}
processExtractBinRaw state raw ext code bytes with parseCANFrame raw ext code bytes
... | inj₁ e           = (state , inj₁ (ParseErr e))
... | inj₂ (_ , frame) = processExtractBin state frame
