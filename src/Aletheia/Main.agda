{-# OPTIONS --safe --without-K --no-main #-}

-- Main entry point for Aletheia (JSON streaming protocol + binary APIs).
--
-- Purpose: Curated public facade re-exporting the types, state-machine,
--   command dispatch, frame/error types, and FFI entry points that external
--   callers (Haskell REPL, tests, AletheiaFFI.hs) need.
--
-- State Machine: WaitingForDBC → ReadyToStream → Streaming
--
-- Compilation: Compiled to Haskell via MAlonzo; the FFI shim
-- (AletheiaFFI.hs) calls processJSONLine and the processXxxDirect/Bin
-- entries directly from the Main.JSON and Main.Binary sub-modules. This
-- facade does not add FFI symbols of its own — it exists for
-- discoverability. Bindings (Python/C++/Go) load libaletheia-ffi.so via
-- ctypes/dlopen (direct FFI).
--
-- Sub-modules:
--   Main.JSON   — processJSONLine and (private) JSON dispatch helpers
--   Main.Binary — all binary entry points (*Direct for JSON output,
--                 *Bin for binary output)
--
-- Key design: ALL logic lives in Agda (parsing, validation, state, LTL
-- checking). Haskell FFI shim (AletheiaFFI.hs) only handles C-callable
-- exports and state management.
--
-- Name clashes: The constructor `Response.Error` (from
-- `Aletheia.Protocol.Message`) and the constructor `TraceEvent.Error`
-- (from `Aletheia.Trace.CANTrace`) both clash with the `Error` type from
-- `Aletheia.Error`. They are re-exported under renamed names
-- (`ResponseError` and `TraceError`) to keep all three names in scope
-- simultaneously from this facade.
module Aletheia.Main where

-- ============================================================================
-- FFI ENTRY POINTS
-- ============================================================================
-- Called directly from AletheiaFFI.hs via MAlonzo (the shim imports
-- MAlonzo.Code.Aletheia.Main.JSON and MAlonzo.Code.Aletheia.Main.Binary
-- rather than this facade, so these re-exports are for discoverability).

open import Aletheia.Main.JSON public
  using (processJSONLine)

open import Aletheia.Main.Binary public
  using ( processFrameDirect
        ; processEventDirect
        ; processStartStreamDirect
        ; processEndStreamDirect
        ; processFormatDBCDirect
        ; processExtractDirect
        ; processBuildFrameDirect
        ; processUpdateFrameDirect
        ; processBuildFrameBin
        ; processUpdateFrameBin
        ; processExtractBin
        )

-- ============================================================================
-- STATE MACHINE
-- ============================================================================
-- Stream state type, phase constructors, initial state, and the public
-- frame/trace-event handlers. `checkMonotonic` is exported so tests and
-- proof clients can reference the monotonicity predicate directly.

open import Aletheia.Protocol.StreamState public
  using ( StreamState
        ; WaitingForDBC
        ; ReadyToStream
        ; Streaming
        ; initialState
        ; getDBC
        ; checkMonotonic
        ; handleDataFrame
        ; handleTraceEvent
        )

-- ============================================================================
-- COMMAND DISPATCH
-- ============================================================================
-- High-level streaming protocol: StreamCommand sum, Response sum, and
-- the command dispatcher. Response.Error is renamed to `ResponseError`
-- to avoid clashing with Aletheia.Error.Error.

open import Aletheia.Protocol.Message public
  using ( StreamCommand
        ; ParseDBC
        ; SetProperties
        ; StartStream
        ; BuildFrame
        ; ExtractAllSignals
        ; UpdateFrame
        ; EndStream
        ; ValidateDBC
        ; FormatDBC
        ; Response
        ; Success
        ; ByteArray
        ; ExtractionResultsResponse
        ; PropertyResponse
        ; Ack
        ; Complete
        ; ValidationResponse
        ; DBCResponse
        )
  renaming (Error to ResponseError)

open import Aletheia.Protocol.Handlers public
  using (processStreamCommand)

-- ============================================================================
-- FRAME, TRACE, AND DLC TYPES
-- ============================================================================
-- Types that appear in the signatures of the FFI entry points above.
-- TraceEvent.Error is renamed to `TraceError` to avoid clashing with
-- Aletheia.Error.Error.

open import Aletheia.CAN.Frame public
  using ( Byte
        ; CANId
        ; Standard
        ; Extended
        ; CANFrame
        )

open import Aletheia.CAN.DLC public
  using ( DLC
        ; mkDLC
        ; dlcBytes
        ; dlcToBytes
        ; bytesToDlc
        ; maxDLC-2B
        ; maxDLC-FD
        )

open import Aletheia.Trace.CANTrace public
  using ( TimedFrame
        ; TraceEvent
        ; Data
        ; Remote
        ; timestampℕ
        ; eventTimestamp
        )
  renaming (Error to TraceError)

open import Aletheia.Trace.Time public
  using ( Timestamp
        ; tsValue
        ; TimeUnit
        ; μs
        )

-- ============================================================================
-- ERROR TYPES AND INSPECTION
-- ============================================================================
-- Top-level `Error` sum plus the per-domain error ADTs and the
-- `formatError` / `errorCode` inspection helpers that tests and callers
-- use to classify failures.

open import Aletheia.Error public
  using ( Error
        ; ParseErr
        ; FrameErr
        ; ExtractionErr
        ; RouteErr
        ; HandlerErr
        ; DispatchErr
        ; WithContext
        ; ParseError
        ; FrameError
        ; ExtractionError
        ; RouteError
        ; HandlerError
        ; DispatchError
        ; formatError
        ; errorCode
        ; formatParseError
        ; formatFrameError
        ; formatExtractionError
        ; formatRouteError
        ; formatHandlerError
        ; formatDispatchError
        )

-- ============================================================================
-- JSON AND RESPONSE FORMATTING
-- ============================================================================
-- JSON datatype and the formatter that turns a Response into
-- wire-format JSON. Exposed so that callers that build Responses
-- directly (Haskell REPL, tests) can render them the same way the FFI
-- shim does.

open import Aletheia.Protocol.JSON public
  using ( JSON
        ; parseJSON
        ; formatJSON
        )

open import Aletheia.Protocol.ResponseFormat public
  using (formatResponse)
