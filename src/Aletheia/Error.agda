{-# OPTIONS --safe --without-K #-}

-- Typed error ADTs replacing String ⊎ A throughout the codebase.
--
-- Purpose: Provide exhaustive, pattern-matchable error types for all
-- error-producing operations. Each domain (parse, frame, route, handler,
-- dispatch) has its own ADT. The top-level Error sum wraps them all.
--
-- Role: Imported by JSONParser (ParseError), BatchFrameBuilding (FrameError),
-- Routing (RouteError), Handlers/StreamState (HandlerError), Main (DispatchError).
-- ResponseFormat uses errorCode/formatError for JSON serialization.
module Aletheia.Error where

open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Nat using (ℕ; _∸_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)

-- ============================================================================
-- PARSE ERRORS (DBC/JSONParser.agda)
-- ============================================================================

data ParseError : Set where
  MissingField            : String → ParseError
  InvalidByteOrder        : String → ParseError
  InvalidPresence         : String → ParseError
  MissingSigned           : ParseError
  InvalidSigned           : String → ParseError
  NotAnObject             : String → ℕ → ParseError
  ExtCANIdOutOfRange      : ℕ → ParseError
  StdCANIdOutOfRange      : ℕ → ParseError
  DefaultCANIdOutOfRange  : ℕ → ParseError
  InvalidDLCBytes         : ℕ → ParseError
  RootNotObject           : ParseError
  MissingSignalName       : ParseError
  -- Physical-validity errors (BigEndian signals only):
  -- enforced by JSONParser so parseDBCWithErrors yields WellFormedDBCRT,
  -- closing the parse-format-parse weak inverse without a hypothesis.
  SignalBitLengthZero     : ParseError                -- bitLength must be ≥ 1
  SignalOverflowsFrame    : ℕ → ℕ → ℕ → ParseError    -- startBit, bitLength, frameBytes
  SignalMSBBelowBitLength : ℕ → ℕ → ParseError        -- startBit, bitLength
  InContext               : String → ParseError → ParseError

formatParseError : ParseError → String
formatParseError (MissingField f) =
  "missing '" ++ₛ f ++ₛ "' field"
formatParseError (InvalidByteOrder s) =
  "invalid byte order '" ++ₛ s ++ₛ "' (expected 'little_endian' or 'big_endian')"
formatParseError (InvalidPresence s) =
  "invalid presence value '" ++ₛ s ++ₛ "'"
formatParseError MissingSigned =
  "missing 'signed' field"
formatParseError (InvalidSigned s) =
  "invalid signed value '" ++ₛ s ++ₛ "' (expected 'signed' or 'unsigned')"
formatParseError (NotAnObject kind idx) =
  kind ++ₛ " at index " ++ₛ showℕ idx ++ₛ " is not a JSON object"
formatParseError (ExtCANIdOutOfRange n) =
  "extended CAN ID " ++ₛ showℕ n ++ₛ " out of range (max " ++ₛ showℕ (extended-can-id-max ∸ 1) ++ₛ ")"
formatParseError (StdCANIdOutOfRange n) =
  "standard CAN ID " ++ₛ showℕ n ++ₛ " out of range (max " ++ₛ showℕ (standard-can-id-max ∸ 1) ++ₛ ")"
formatParseError (DefaultCANIdOutOfRange n) =
  "CAN ID " ++ₛ showℕ n ++ₛ " out of range for standard ID (max " ++ₛ showℕ (standard-can-id-max ∸ 1) ++ₛ ")"
formatParseError (InvalidDLCBytes n) =
  "DLC " ++ₛ showℕ n ++ₛ " is not a valid CAN byte count"
formatParseError RootNotObject =
  "root must be a JSON object"
formatParseError MissingSignalName =
  "missing signal 'name' field"
formatParseError SignalBitLengthZero =
  "signal bit length must be ≥ 1"
formatParseError (SignalOverflowsFrame sb bl fb) =
  "signal at startBit " ++ₛ showℕ sb ++ₛ " with length " ++ₛ showℕ bl
    ++ₛ " overflows frame (" ++ₛ showℕ fb ++ₛ " bytes)"
formatParseError (SignalMSBBelowBitLength sb bl) =
  "bigEndian signal MSB position " ++ₛ showℕ sb
    ++ₛ " below bitLength " ++ₛ showℕ bl ++ₛ " ∸ 1"
formatParseError (InContext ctx inner) =
  ctx ++ₛ ": " ++ₛ formatParseError inner

parseErrorCode : ParseError → String
parseErrorCode (MissingField _)           = "parse_missing_field"
parseErrorCode (InvalidByteOrder _)       = "parse_invalid_byte_order"
parseErrorCode (InvalidPresence _)        = "parse_invalid_presence"
parseErrorCode MissingSigned              = "parse_missing_signed"
parseErrorCode (InvalidSigned _)          = "parse_invalid_signed"
parseErrorCode (NotAnObject _ _)          = "parse_not_an_object"
parseErrorCode (ExtCANIdOutOfRange _)     = "parse_ext_can_id_out_of_range"
parseErrorCode (StdCANIdOutOfRange _)     = "parse_std_can_id_out_of_range"
parseErrorCode (DefaultCANIdOutOfRange _) = "parse_default_can_id_out_of_range"
parseErrorCode (InvalidDLCBytes _)        = "parse_invalid_dlc_bytes"
parseErrorCode RootNotObject              = "parse_root_not_object"
parseErrorCode MissingSignalName          = "parse_missing_signal_name"
parseErrorCode SignalBitLengthZero        = "parse_signal_bit_length_zero"
parseErrorCode (SignalOverflowsFrame _ _ _) = "parse_signal_overflows_frame"
parseErrorCode (SignalMSBBelowBitLength _ _) = "parse_signal_msb_below_bit_length"
parseErrorCode (InContext _ inner)         = parseErrorCode inner

-- ============================================================================
-- EXTRACTION ERRORS (CAN/SignalExtraction.agda)
-- ============================================================================

data ExtractionError : Set where
  MuxValueMismatch       : ExtractionError
  MuxSignalNotFound      : String → ExtractionError  -- multiplexor signal name
  MuxChainCycle          : ExtractionError
  MuxExtractionFailed    : String → ExtractionError  -- multiplexor signal name
  -- Bit-level extraction or scaling failed (catch-all for ExtractionResult.ExtractionFailed).
  -- Routed through the typed Error sum rather than carrying a raw String at the
  -- ExtractionResult layer, so all errors share a single ADT.
  BitExtractionFailed    : String → ExtractionError

formatExtractionError : ExtractionError → String
formatExtractionError MuxValueMismatch         = "multiplexor value mismatch"
formatExtractionError (MuxSignalNotFound name)  =
  "multiplexor signal '" ++ₛ name ++ₛ "' not found in message"
formatExtractionError MuxChainCycle             = "multiplexor chain depth exceeded (cycle?)"
formatExtractionError (MuxExtractionFailed name) =
  "failed to extract multiplexor signal '" ++ₛ name ++ₛ "'"
formatExtractionError (BitExtractionFailed reason) =
  "bit extraction failed: " ++ₛ reason

extractionErrorCode : ExtractionError → String
extractionErrorCode MuxValueMismatch         = "extraction_mux_value_mismatch"
extractionErrorCode (MuxSignalNotFound _)    = "extraction_mux_signal_not_found"
extractionErrorCode MuxChainCycle            = "extraction_mux_chain_cycle"
extractionErrorCode (MuxExtractionFailed _)  = "extraction_mux_extraction_failed"
extractionErrorCode (BitExtractionFailed _)  = "extraction_bit_extraction_failed"

-- ============================================================================
-- FRAME BUILDING ERRORS (CAN/BatchFrameBuilding.agda)
-- ============================================================================

data FrameError : Set where
  SignalNotFound         : String → FrameError
  SignalIndexOOB         : ℕ → FrameError
  InjectionFailed        : String → FrameError
  SignalsOverlap         : FrameError
  CANIdNotFound          : FrameError
  CANIdMismatch          : FrameError
  SignalValueOutOfBounds : String → FrameError  -- pre-formatted "v not in [min, max]"

formatFrameError : FrameError → String
formatFrameError (SignalNotFound name)          = "signal not found in message: " ++ₛ name
formatFrameError (SignalIndexOOB idx)           = "signal index " ++ₛ showℕ idx ++ₛ " out of range"
formatFrameError (InjectionFailed n)            = "injection failed for signal: " ++ₛ n
formatFrameError SignalsOverlap                 = "signals overlap"
formatFrameError CANIdNotFound                  = "CAN ID not found in DBC"
formatFrameError CANIdMismatch                  = "CAN ID does not match frame"
formatFrameError (SignalValueOutOfBounds desc)  = "value out of bounds: " ++ₛ desc

frameErrorCode : FrameError → String
frameErrorCode (SignalNotFound _)          = "frame_signal_not_found"
frameErrorCode (SignalIndexOOB _)          = "frame_signal_index_oob"
frameErrorCode (InjectionFailed _)         = "frame_injection_failed"
frameErrorCode SignalsOverlap              = "frame_signals_overlap"
frameErrorCode CANIdNotFound               = "frame_can_id_not_found"
frameErrorCode CANIdMismatch               = "frame_can_id_mismatch"
frameErrorCode (SignalValueOutOfBounds _)  = "frame_signal_value_out_of_bounds"

-- ============================================================================
-- ROUTE/COMMAND ERRORS (Protocol/Routing.agda)
-- ============================================================================

data RouteError : Set where
  RouteMissingField    : String → String → RouteError
  RouteMissingArray    : String → String → RouteError
  UnknownCommand       : String → RouteError
  MissingCommandField  : RouteError
  DLCExceedsMax        : String → RouteError
  ByteArrayParseFailed : String → RouteError
  ByteCountMismatch    : String → RouteError
  MissingDBCField      : String → RouteError
  MissingPropsField    : RouteError
  WrappedParseError    : ParseError → RouteError

formatRouteError : RouteError → String
formatRouteError (RouteMissingField cmd f) =
  cmd ++ₛ ": missing '" ++ₛ f ++ₛ "' field"
formatRouteError (RouteMissingArray cmd f) =
  cmd ++ₛ ": missing '" ++ₛ f ++ₛ "' array"
formatRouteError (UnknownCommand s) =
  "unknown command: " ++ₛ s
formatRouteError MissingCommandField =
  "missing 'command' field"
formatRouteError (DLCExceedsMax ctx) =
  ctx ++ₛ ": DLC exceeds maximum value"
formatRouteError (ByteArrayParseFailed c) =
  c ++ₛ ": failed to parse byte array"
formatRouteError (ByteCountMismatch c) =
  c ++ₛ ": byte count does not match DLC"
formatRouteError (MissingDBCField cmd) =
  cmd ++ₛ ": missing 'dbc' field"
formatRouteError MissingPropsField =
  "missing 'properties' field"
formatRouteError (WrappedParseError pe) =
  "parse error: " ++ₛ formatParseError pe

routeErrorCode : RouteError → String
routeErrorCode (RouteMissingField _ _) = "route_missing_field"
routeErrorCode (RouteMissingArray _ _) = "route_missing_array"
routeErrorCode (UnknownCommand _)      = "route_unknown_command"
routeErrorCode MissingCommandField     = "route_missing_command_field"
routeErrorCode (DLCExceedsMax _)       = "route_dlc_exceeds_max"
routeErrorCode (ByteArrayParseFailed _) = "route_byte_array_parse_failed"
routeErrorCode (ByteCountMismatch _)   = "route_byte_count_mismatch"
routeErrorCode (MissingDBCField _)     = "route_missing_dbc_field"
routeErrorCode MissingPropsField       = "route_missing_props_field"
routeErrorCode (WrappedParseError pe)  = parseErrorCode pe

-- ============================================================================
-- HANDLER/STATE ERRORS (Protocol/Handlers.agda, StreamState.agda)
-- ============================================================================

data HandlerError : Set where
  NoDBC                  : HandlerError
  AlreadyStreaming       : HandlerError
  NotStreaming           : HandlerError
  StreamNotStarted       : HandlerError
  StreamActive           : HandlerError
  SignalListParseFailed  : HandlerError
  PropertyParseFailed    : ℕ → HandlerError
  InvalidDLCCode         : HandlerError
  ValidationFailed       : String → HandlerError
  -- Non-monotonic timestamp: current < previous (carries both for diagnostics).
  -- Metric LTL operators (MetricEventually, MetricAlways) compute elapsed time
  -- via natural subtraction (∸), which clamps at 0 on backward timestamps and
  -- silently produces wrong verdicts. handleDataFrame refuses such frames.
  NonMonotonicTimestamp  : ℕ → ℕ → HandlerError
  WrappedParse           : ParseError → HandlerError
  WrappedFrame           : FrameError → HandlerError

formatHandlerError : HandlerError → String
formatHandlerError NoDBC                 = "DBC not loaded"
formatHandlerError AlreadyStreaming      = "stream already active"
formatHandlerError NotStreaming          = "stream not active"
formatHandlerError StreamNotStarted      = "stream not started"
formatHandlerError StreamActive          = "stream still active"
formatHandlerError SignalListParseFailed = "signal list parse failure"
formatHandlerError (PropertyParseFailed idx) =
  "property parse failure at index " ++ₛ showℕ idx
formatHandlerError InvalidDLCCode        = "invalid DLC code"
formatHandlerError (ValidationFailed msg) = msg
formatHandlerError (NonMonotonicTimestamp curr prev) =
  "non-monotonic timestamp: " ++ₛ showℕ curr ++ₛ " μs < previous " ++ₛ showℕ prev ++ₛ
  " μs (metric LTL operators require monotonic timestamps)"
formatHandlerError (WrappedParse pe)     = "parse error: " ++ₛ formatParseError pe
formatHandlerError (WrappedFrame fe)     = "frame error: " ++ₛ formatFrameError fe

handlerErrorCode : HandlerError → String
handlerErrorCode NoDBC                 = "handler_no_dbc"
handlerErrorCode AlreadyStreaming      = "handler_already_streaming"
handlerErrorCode NotStreaming          = "handler_not_streaming"
handlerErrorCode StreamNotStarted      = "handler_stream_not_started"
handlerErrorCode StreamActive          = "handler_stream_active"
handlerErrorCode SignalListParseFailed = "handler_signal_list_parse_failed"
handlerErrorCode (PropertyParseFailed _) = "handler_property_parse_failed"
handlerErrorCode InvalidDLCCode        = "handler_invalid_dlc_code"
handlerErrorCode (ValidationFailed _)  = "handler_validation_failed"
handlerErrorCode (NonMonotonicTimestamp _ _) = "handler_non_monotonic_timestamp"
handlerErrorCode (WrappedParse pe)     = parseErrorCode pe
handlerErrorCode (WrappedFrame fe)     = frameErrorCode fe

-- ============================================================================
-- DISPATCH ERRORS (Main.agda)
-- ============================================================================

data DispatchError : Set where
  MissingTypeField   : DispatchError
  UnknownMessageType : String → DispatchError
  InvalidJSON        : DispatchError
  RequestNotObject   : DispatchError

formatDispatchError : DispatchError → String
formatDispatchError MissingTypeField       = "missing 'type' field in request"
formatDispatchError (UnknownMessageType s) = "unknown message type: " ++ₛ s
formatDispatchError InvalidJSON            = "invalid JSON"
formatDispatchError RequestNotObject       = "request must be a JSON object"

dispatchErrorCode : DispatchError → String
dispatchErrorCode MissingTypeField       = "dispatch_missing_type_field"
dispatchErrorCode (UnknownMessageType _) = "dispatch_unknown_message_type"
dispatchErrorCode InvalidJSON            = "dispatch_invalid_json"
dispatchErrorCode RequestNotObject       = "dispatch_request_not_object"

-- ============================================================================
-- TOP-LEVEL ERROR SUM
-- ============================================================================

data Error : Set where
  ParseErr       : ParseError → Error
  FrameErr       : FrameError → Error
  ExtractionErr  : ExtractionError → Error
  RouteErr       : RouteError → Error
  HandlerErr     : HandlerError → Error
  DispatchErr    : DispatchError → Error
  WithContext    : String → Error → Error

formatError : Error → String
formatError (ParseErr pe)         = formatParseError pe
formatError (FrameErr fe)         = formatFrameError fe
formatError (ExtractionErr ee)    = formatExtractionError ee
formatError (RouteErr re)         = formatRouteError re
formatError (HandlerErr he)       = formatHandlerError he
formatError (DispatchErr de)      = formatDispatchError de
formatError (WithContext ctx inner) = ctx ++ₛ ": " ++ₛ formatError inner

errorCode : Error → String
errorCode (ParseErr pe)    = parseErrorCode pe
errorCode (FrameErr fe)    = frameErrorCode fe
errorCode (ExtractionErr ee) = extractionErrorCode ee
errorCode (RouteErr re)    = routeErrorCode re
errorCode (HandlerErr he)  = handlerErrorCode he
errorCode (DispatchErr de) = dispatchErrorCode de
errorCode (WithContext _ inner) = errorCode inner
