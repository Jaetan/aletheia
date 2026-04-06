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
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List)
open import Aletheia.DBC.Types using (ValidationIssue)
open import Aletheia.DBC.Validator using (formatIssuesText; errorIssues)

-- ============================================================================
-- PARSE ERRORS (DBC/JSONParser.agda)
-- ============================================================================

data ParseError : Set where
  MissingField           : String → ParseError
  InvalidByteOrder       : String → ParseError
  InvalidPresence        : String → ParseError
  MissingSigned          : ParseError
  InvalidSigned          : String → ParseError
  NotAnObject            : String → ℕ → ParseError
  ExtCANIdOutOfRange     : ℕ → ParseError
  StdCANIdOutOfRange     : ℕ → ParseError
  DefaultCANIdOutOfRange : ℕ → ParseError
  InvalidDLCBytes        : ℕ → ParseError
  RootNotObject          : ParseError
  MissingSignalName      : ParseError
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
  "extended CAN ID " ++ₛ showℕ n ++ₛ " out of range (max 536870911)"
formatParseError (StdCANIdOutOfRange n) =
  "standard CAN ID " ++ₛ showℕ n ++ₛ " out of range (max 2047)"
formatParseError (DefaultCANIdOutOfRange n) =
  "CAN ID " ++ₛ showℕ n ++ₛ " out of range for standard ID (max 2047)"
formatParseError (InvalidDLCBytes n) =
  "DLC " ++ₛ showℕ n ++ₛ " is not a valid CAN byte count"
formatParseError RootNotObject =
  "ParseDBC: root must be a JSON object"
formatParseError MissingSignalName =
  "missing signal 'name' field"
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
parseErrorCode (InContext _ inner)         = parseErrorCode inner

-- ============================================================================
-- FRAME BUILDING ERRORS (CAN/BatchFrameBuilding.agda)
-- ============================================================================

data FrameError : Set where
  SignalNotFound  : String → FrameError
  SignalIndexOOB  : ℕ → FrameError
  InjectionFailed : String → FrameError
  SignalsOverlap  : FrameError
  CANIdNotFound   : FrameError
  CANIdMismatch   : FrameError

formatFrameError : FrameError → String
formatFrameError (SignalNotFound name) = "signal not found in message: " ++ₛ name
formatFrameError (SignalIndexOOB idx)  = "signal index " ++ₛ showℕ idx ++ₛ " out of range"
formatFrameError (InjectionFailed n)   = "injection failed for signal: " ++ₛ n
formatFrameError SignalsOverlap        = "signals overlap"
formatFrameError CANIdNotFound         = "CAN ID not found in DBC"
formatFrameError CANIdMismatch         = "CAN ID does not match frame"

frameErrorCode : FrameError → String
frameErrorCode (SignalNotFound _)  = "frame_signal_not_found"
frameErrorCode (SignalIndexOOB _)  = "frame_signal_index_oob"
frameErrorCode (InjectionFailed _) = "frame_injection_failed"
frameErrorCode SignalsOverlap      = "frame_signals_overlap"
frameErrorCode CANIdNotFound       = "frame_can_id_not_found"
frameErrorCode CANIdMismatch       = "frame_can_id_mismatch"

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
  "Unknown command: " ++ₛ s
formatRouteError MissingCommandField =
  "ParseCommand: missing 'command' field"
formatRouteError (DLCExceedsMax ctx) =
  ctx ++ₛ ": DLC exceeds maximum value"
formatRouteError (ByteArrayParseFailed c) =
  c ++ₛ ": failed to parse byte array"
formatRouteError (ByteCountMismatch c) =
  c ++ₛ ": byte count doesn't match DLC"
formatRouteError (MissingDBCField cmd) =
  cmd ++ₛ ": missing 'dbc' field"
formatRouteError MissingPropsField =
  "SetProperties: missing 'properties' field"
formatRouteError (WrappedParseError pe) =
  formatParseError pe

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
  NoDBC                 : HandlerError
  AlreadyStreaming      : HandlerError
  NotStreaming          : HandlerError
  StreamNotStarted      : HandlerError
  StreamActive          : HandlerError
  SignalListParseFailed : HandlerError
  PropertyParseFailed   : ℕ → HandlerError
  InvalidDLCCode        : HandlerError
  ValidationFailed      : List ValidationIssue → HandlerError
  WrappedParse          : ParseError → HandlerError
  WrappedFrame          : FrameError → HandlerError

formatHandlerError : HandlerError → String
formatHandlerError NoDBC                 = "DBC not loaded"
formatHandlerError AlreadyStreaming      = "already streaming"
formatHandlerError NotStreaming          = "not currently streaming"
formatHandlerError StreamNotStarted      = "stream not started"
formatHandlerError StreamActive          = "stream is active"
formatHandlerError SignalListParseFailed = "failed to parse signal list"
formatHandlerError (PropertyParseFailed idx) =
  "failed to parse property " ++ₛ showℕ idx
formatHandlerError InvalidDLCCode        = "invalid DLC code"
formatHandlerError (ValidationFailed issues) =
  "validation failed: " ++ₛ formatIssuesText (errorIssues issues)
formatHandlerError (WrappedParse pe)     = "parse error: " ++ₛ formatParseError pe
formatHandlerError (WrappedFrame fe)     = formatFrameError fe

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
formatDispatchError MissingTypeField       = "Dispatch: missing 'type' field in request"
formatDispatchError (UnknownMessageType s) = "Dispatch: unknown message type: " ++ₛ s
formatDispatchError InvalidJSON            = "Dispatch: invalid JSON"
formatDispatchError RequestNotObject       = "Dispatch: request must be a JSON object"

dispatchErrorCode : DispatchError → String
dispatchErrorCode MissingTypeField       = "dispatch_missing_type_field"
dispatchErrorCode (UnknownMessageType _) = "dispatch_unknown_message_type"
dispatchErrorCode InvalidJSON            = "dispatch_invalid_json"
dispatchErrorCode RequestNotObject       = "dispatch_request_not_object"

-- ============================================================================
-- TOP-LEVEL ERROR SUM
-- ============================================================================

data Error : Set where
  ParseErr    : ParseError → Error
  FrameErr    : FrameError → Error
  RouteErr    : RouteError → Error
  HandlerErr  : HandlerError → Error
  DispatchErr : DispatchError → Error
  WithContext  : String → Error → Error

formatError : Error → String
formatError (ParseErr pe)         = formatParseError pe
formatError (FrameErr fe)         = formatFrameError fe
formatError (RouteErr re)         = formatRouteError re
formatError (HandlerErr he)       = formatHandlerError he
formatError (DispatchErr de)      = formatDispatchError de
formatError (WithContext ctx inner) = ctx ++ₛ ": " ++ₛ formatError inner

errorCode : Error → String
errorCode (ParseErr pe)    = parseErrorCode pe
errorCode (FrameErr fe)    = frameErrorCode fe
errorCode (RouteErr (WrappedParseError pe)) = parseErrorCode pe
errorCode (RouteErr re)    = routeErrorCode re
errorCode (HandlerErr (WrappedParse pe)) = parseErrorCode pe
errorCode (HandlerErr (WrappedFrame fe)) = frameErrorCode fe
errorCode (HandlerErr he)  = handlerErrorCode he
errorCode (DispatchErr de) = dispatchErrorCode de
errorCode (WithContext _ inner) = errorCode inner
