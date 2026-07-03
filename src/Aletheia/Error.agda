-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
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
open import Data.List using (List)
open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)
open import Aletheia.CAN.DLC using (maxDLC-FD)
open import Aletheia.DBC.Types using (ValidationIssue)
open import Aletheia.DBC.Validator.Formatting using (formatIssuesText; errorIssues)
open import Aletheia.Parser.Combinators using (Position)
open import Aletheia.Limits using (BoundKind; boundKindLabel)

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
  -- Unknown discriminator in a kind-tagged wire object. First argument is the
  -- domain name ("commentTarget", "attrScope", etc.); second is the offending
  -- value. Used by Tier 2 DBC metadata parsers (nodes / comments / attributes).
  InvalidKind             : String → String → ParseError
  -- Non-terminating rational in a DBC-decimal field (EV_ initial/min/max,
  -- SG_ factor/offset/min/max, BA_DEF_ FLOAT min/max, BA_ float value).
  -- DBC text grammar is decimal-terminating by construction, so only the
  -- JSON wire form `{"numerator": n, "denominator": d}` can produce a
  -- rational whose denominator has a prime factor outside {2, 5}. First
  -- argument is the field name for diagnostics.
  NonTerminatingRational  : String → ParseError
  -- Name field that fails the DBC identifier grammar (letter/underscore start,
  -- alphanumeric/underscore continue).  Introduced in Track B.3.d Layer 2 to
  -- reject invalid identifiers at the JSON parse boundary; the text parser
  -- already rejects these syntactically via `parseIdentifier`.
  InvalidIdentifier       : String → ParseError
  -- Non-integer value in a `multiplex_values` JSON array.  Split out from
  -- `InvalidPresence` in R23 (AGDA-C-5.1) so the wire code distinguishes
  -- "presence string not 'always'" (the original InvalidPresence intent)
  -- from "multiplex_values array contains a non-natural element".  The
  -- two pre-R23 emit sites at `JSONParser.parseNatList[⁺]` shared the
  -- `InvalidPresence "non-integer in multiplex_values"` literal which
  -- collapsed both classes onto a single wire code.
  NonIntegerMultiplexValue : ParseError
  InContext               : String → ParseError → ParseError
  -- NOTE: Adversarial-input bounds are emitted via the top-level
  -- `Error.InputBoundExceeded` ctor (R19 cluster 14 / AGDA-C-6.2 —
  -- consolidated from the three previously duplicate per-ADT ctors).
  -- A ParseError observer sees `InputBoundExceeded` at the Error sum
  -- level rather than inside ParseError itself.

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
  "extended CAN ID " ++ₛ showℕ n ++ₛ " exceeds limit " ++ₛ showℕ (extended-can-id-max ∸ 1)
formatParseError (StdCANIdOutOfRange n) =
  "standard CAN ID " ++ₛ showℕ n ++ₛ " exceeds limit " ++ₛ showℕ (standard-can-id-max ∸ 1)
formatParseError (DefaultCANIdOutOfRange n) =
  "CAN ID " ++ₛ showℕ n ++ₛ " exceeds limit " ++ₛ showℕ (standard-can-id-max ∸ 1) ++ₛ " for standard ID"
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
formatParseError (InvalidKind domain value) =
  "invalid " ++ₛ domain ++ₛ " kind '" ++ₛ value ++ₛ "'"
formatParseError (NonTerminatingRational f) =
  "rational field '" ++ₛ f ++ₛ "' is non-terminating in decimal (denominator has a prime factor outside {2, 5})"
formatParseError (InvalidIdentifier s) =
  "'" ++ₛ s ++ₛ "' is not a valid DBC identifier (must start with letter or '_', followed by alphanumerics or '_')"
formatParseError NonIntegerMultiplexValue =
  "non-integer value in 'multiplex_values' array (every element must be a JSON natural number)"
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
parseErrorCode (InvalidKind _ _)          = "parse_invalid_kind"
parseErrorCode (NonTerminatingRational _) = "parse_non_terminating_rational"
parseErrorCode (InvalidIdentifier _)       = "parse_invalid_identifier"
parseErrorCode NonIntegerMultiplexValue    = "parse_non_integer_multiplex_value"
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
  InContext              : String → ExtractionError → ExtractionError

formatExtractionError : ExtractionError → String
formatExtractionError MuxValueMismatch         = "multiplexor value mismatch"
formatExtractionError (MuxSignalNotFound name)  =
  "multiplexor signal '" ++ₛ name ++ₛ "' not found in message"
formatExtractionError MuxChainCycle             = "multiplexor chain depth exceeded (cycle?)"
formatExtractionError (MuxExtractionFailed name) =
  "failed to extract multiplexor signal '" ++ₛ name ++ₛ "'"
formatExtractionError (BitExtractionFailed reason) =
  "bit extraction failed: " ++ₛ reason
formatExtractionError (InContext ctx inner) =
  ctx ++ₛ ": " ++ₛ formatExtractionError inner

extractionErrorCode : ExtractionError → String
extractionErrorCode MuxValueMismatch         = "extraction_mux_value_mismatch"
extractionErrorCode (MuxSignalNotFound _)    = "extraction_mux_signal_not_found"
extractionErrorCode MuxChainCycle            = "extraction_mux_chain_cycle"
extractionErrorCode (MuxExtractionFailed _)  = "extraction_mux_extraction_failed"
extractionErrorCode (BitExtractionFailed _)  = "extraction_bit_extraction_failed"
extractionErrorCode (InContext _ inner)      = extractionErrorCode inner

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
  InContext              : String → FrameError → FrameError
  -- NOTE: Frame-byte-count and similar adversarial-input bounds emit
  -- via the top-level `Error.InputBoundExceeded` ctor (R19 cluster 14 /
  -- AGDA-C-6.2 consolidation).

formatFrameError : FrameError → String
formatFrameError (SignalNotFound name)          = "signal '" ++ₛ name ++ₛ "' not found in message"
formatFrameError (SignalIndexOOB idx)           = "signal index " ++ₛ showℕ idx ++ₛ " out of range"
formatFrameError (InjectionFailed n)            = "injection failed for signal '" ++ₛ n ++ₛ "'"
formatFrameError SignalsOverlap                 = "signals overlap"
formatFrameError CANIdNotFound                  = "CAN ID not found in DBC"
formatFrameError CANIdMismatch                  = "CAN ID does not match frame"
formatFrameError (SignalValueOutOfBounds desc)  = "value out of bounds: " ++ₛ desc
formatFrameError (InContext ctx inner)          = ctx ++ₛ ": " ++ₛ formatFrameError inner

frameErrorCode : FrameError → String
frameErrorCode (SignalNotFound _)          = "frame_signal_not_found"
frameErrorCode (SignalIndexOOB _)          = "frame_signal_index_oob"
frameErrorCode (InjectionFailed _)         = "frame_injection_failed"
frameErrorCode SignalsOverlap              = "frame_signals_overlap"
frameErrorCode CANIdNotFound               = "frame_can_id_not_found"
frameErrorCode CANIdMismatch               = "frame_can_id_mismatch"
frameErrorCode (SignalValueOutOfBounds _)  = "frame_signal_value_out_of_bounds"
frameErrorCode (InContext _ inner)         = frameErrorCode inner

-- ============================================================================
-- ROUTE/COMMAND ERRORS (Protocol/Routing.agda)
-- ============================================================================

data RouteError : Set where
  RouteMissingField    : String → RouteError           -- field name
  RouteMissingArray    : String → RouteError           -- field name
  UnknownCommand       : String → RouteError           -- command name
  MissingCommandField  : RouteError
  DLCExceedsMax        : RouteError
  ByteArrayParseFailed : RouteError
  ByteCountMismatch    : RouteError
  MissingDBCField      : RouteError
  MissingPropsField    : RouteError
  WrappedParse         : ParseError → RouteError
  InContext            : String → RouteError → RouteError

formatRouteError : RouteError → String
formatRouteError (RouteMissingField f) =
  "missing '" ++ₛ f ++ₛ "' field"
formatRouteError (RouteMissingArray f) =
  "missing '" ++ₛ f ++ₛ "' array"
formatRouteError (UnknownCommand s) =
  "unknown command '" ++ₛ s ++ₛ "'"
formatRouteError MissingCommandField =
  "missing 'command' field"
formatRouteError DLCExceedsMax =
  "DLC exceeds limit " ++ₛ showℕ maxDLC-FD
formatRouteError ByteArrayParseFailed =
  "failed to parse byte array"
formatRouteError ByteCountMismatch =
  "byte count does not match DLC"
formatRouteError MissingDBCField =
  "missing 'dbc' field"
formatRouteError MissingPropsField =
  "missing 'properties' field"
formatRouteError (WrappedParse pe) =
  "parse error: " ++ₛ formatParseError pe
formatRouteError (InContext ctx inner) =
  ctx ++ₛ ": " ++ₛ formatRouteError inner

routeErrorCode : RouteError → String
routeErrorCode (RouteMissingField _)    = "route_missing_field"
routeErrorCode (RouteMissingArray _)    = "route_missing_array"
routeErrorCode (UnknownCommand _)       = "route_unknown_command"
routeErrorCode MissingCommandField      = "route_missing_command_field"
routeErrorCode DLCExceedsMax            = "route_dlc_exceeds_max"
routeErrorCode ByteArrayParseFailed     = "route_byte_array_parse_failed"
routeErrorCode ByteCountMismatch        = "route_byte_count_mismatch"
routeErrorCode MissingDBCField          = "route_missing_dbc_field"
routeErrorCode MissingPropsField        = "route_missing_props_field"
routeErrorCode (WrappedParse pe)        = parseErrorCode pe
routeErrorCode (InContext _ inner)      = routeErrorCode inner

-- ============================================================================
-- HANDLER/STATE ERRORS (Protocol/Handlers.agda, StreamState.agda)
-- ============================================================================

data HandlerError : Set where
  NoDBC                  : HandlerError
  AlreadyStreaming       : HandlerError
  NotStreaming           : HandlerError
  StreamNotStarted       : HandlerError
  StreamActive           : HandlerError
  PropertyParseFailed    : ℕ → HandlerError
  InvalidDLCCode         : HandlerError
  -- Carries the FULL structured list of validation issues produced by
  -- DBC.Validator.validateDBCFull — errors AND warnings, so a rejected
  -- parse still reports the complete picture (a caller fixing the errors
  -- must not then be surprised by warnings that were silently dropped).
  -- formatHandlerError flattens the error-level issues to a single
  -- human-readable string for the wire `message` field; ResponseFormat's
  -- `errorExtras` exposes the whole list structurally as `issues` (the
  -- same element shape as the `validation` response), which the bindings
  -- decode into their typed validation errors.
  ValidationFailed       : List ValidationIssue → HandlerError
  -- Non-monotonic timestamp: current < previous (carries both for diagnostics).
  -- Metric LTL operators (MetricEventually, MetricAlways) compute elapsed time
  -- via natural subtraction (∸), which clamps at 0 on backward timestamps and
  -- silently produces wrong verdicts. handleDataFrame refuses such frames.
  NonMonotonicTimestamp  : ℕ → ℕ → HandlerError
  WrappedParse           : ParseError → HandlerError
  WrappedFrame           : FrameError → HandlerError
  InContext              : String → HandlerError → HandlerError

formatHandlerError : HandlerError → String
formatHandlerError NoDBC                 = "DBC not loaded"
formatHandlerError AlreadyStreaming      = "stream already active"
formatHandlerError NotStreaming          = "stream not active"
formatHandlerError StreamNotStarted      = "stream not started"
formatHandlerError StreamActive          = "stream still active"
formatHandlerError (PropertyParseFailed idx) =
  "property parse failure at index " ++ₛ showℕ idx
formatHandlerError InvalidDLCCode        = "invalid DLC code"
-- The message flattens only the error-level issues (byte-identical to the
-- pre-full-list wire text); warnings travel in the structured `issues`
-- field appended by ResponseFormat.errorExtras.
formatHandlerError (ValidationFailed issues) =
  "validation failed: " ++ₛ formatIssuesText (errorIssues issues)
formatHandlerError (NonMonotonicTimestamp curr prev) =
  "non-monotonic timestamp: " ++ₛ showℕ curr ++ₛ " μs < previous " ++ₛ showℕ prev ++ₛ
  " μs (metric LTL operators require monotonic timestamps)"
formatHandlerError (WrappedParse pe)     = "parse error: " ++ₛ formatParseError pe
formatHandlerError (WrappedFrame fe)     = "frame error: " ++ₛ formatFrameError fe
formatHandlerError (InContext ctx inner) = ctx ++ₛ ": " ++ₛ formatHandlerError inner

handlerErrorCode : HandlerError → String
handlerErrorCode NoDBC                 = "handler_no_dbc"
handlerErrorCode AlreadyStreaming      = "handler_already_streaming"
handlerErrorCode NotStreaming          = "handler_not_streaming"
handlerErrorCode StreamNotStarted      = "handler_stream_not_started"
handlerErrorCode StreamActive          = "handler_stream_active"
handlerErrorCode (PropertyParseFailed _) = "handler_property_parse_failed"
handlerErrorCode InvalidDLCCode        = "handler_invalid_dlc_code"
handlerErrorCode (ValidationFailed _)  = "handler_validation_failed"
handlerErrorCode (NonMonotonicTimestamp _ _) = "handler_non_monotonic_timestamp"
handlerErrorCode (WrappedParse pe)     = parseErrorCode pe
handlerErrorCode (WrappedFrame fe)     = frameErrorCode fe
handlerErrorCode (InContext _ inner)   = handlerErrorCode inner

-- ============================================================================
-- DISPATCH ERRORS (Main.agda)
-- ============================================================================

data DispatchError : Set where
  MissingTypeField   : DispatchError
  UnknownMessageType : String → DispatchError
  InvalidJSON        : DispatchError
  RequestNotObject   : DispatchError

formatDispatchError : DispatchError → String
formatDispatchError MissingTypeField       = "missing 'type' field"
formatDispatchError (UnknownMessageType s) = "unknown message type '" ++ₛ s ++ₛ "'"
formatDispatchError InvalidJSON            = "invalid JSON"
formatDispatchError RequestNotObject       = "request must be a JSON object"

dispatchErrorCode : DispatchError → String
dispatchErrorCode MissingTypeField       = "dispatch_missing_type_field"
dispatchErrorCode (UnknownMessageType _) = "dispatch_unknown_message_type"
dispatchErrorCode InvalidJSON            = "dispatch_invalid_json"
dispatchErrorCode RequestNotObject       = "dispatch_request_not_object"

-- ============================================================================
-- DBC TEXT PARSE ERRORS (DBC/TextParser.agda)
-- ============================================================================

-- Errors emitted by the DBC text parser (Track B.3.e entry point).  Kept
-- separate from `ParseError` (the JSON-protocol parser) because the
-- vocabularies do not overlap; each evolves independently.
-- Why `refineAttributes` rejected an attribute entry — carried alongside
-- the offending attribute's name so the error states the exact cause
-- instead of an "unknown or ill-typed" disjunction.
data AttrRefineCause : Set where
  -- The entry references an attribute name no `BA_DEF_` / `BA_DEF_REL_` declares.
  UnknownAttrDef : AttrRefineCause
  -- The supplied value does not fit the declared attribute type
  -- (e.g. an out-of-range ENUM index, or a string where INT is declared).
  IllTypedValue  : AttrRefineCause

data DBCTextParseError : Set where
  ParseFailure              : DBCTextParseError
  TrailingInput             : Position → DBCTextParseError
  -- Carries the cause and the name of the offending attribute, so the
  -- error pinpoints WHICH `BA_DEF_DEF_` / `BA_` / `BA_REL_` entry failed
  -- and WHY (unknown attribute vs ill-typed value).
  AttributeRefinementFailed : AttrRefineCause → String → DBCTextParseError
  -- NOTE: DBC-text-input bytes adversarial bound emits via the top-level
  -- `Error.InputBoundExceeded` ctor (R19 cluster 14 / AGDA-C-6.2).

formatDBCTextParseError : DBCTextParseError → String
formatDBCTextParseError ParseFailure =
  "DBC text parse failed"
formatDBCTextParseError (TrailingInput pos) =
  "parse failed at line " ++ₛ showℕ (Position.line pos)
    ++ₛ ", column " ++ₛ showℕ (Position.column pos)
    ++ₛ ": first unparseable statement"
formatDBCTextParseError (AttributeRefinementFailed UnknownAttrDef name) =
  "attribute refinement failed: '" ++ₛ name
    ++ₛ "' is not a declared attribute (no matching BA_DEF_)"
formatDBCTextParseError (AttributeRefinementFailed IllTypedValue name) =
  "attribute refinement failed: the value given for '" ++ₛ name
    ++ₛ "' does not fit its declared type"

dbcTextParseErrorCode : DBCTextParseError → String
dbcTextParseErrorCode ParseFailure                = "dbc_text_parse_failure"
dbcTextParseErrorCode (TrailingInput _)           = "dbc_text_trailing_input"
dbcTextParseErrorCode (AttributeRefinementFailed _ _) = "dbc_text_attribute_refinement_failed"

-- ============================================================================
-- TOP-LEVEL ERROR SUM
-- ============================================================================

data Error : Set where
  ParseErr           : ParseError → Error
  FrameErr           : FrameError → Error
  ExtractionErr      : ExtractionError → Error
  RouteErr           : RouteError → Error
  HandlerErr         : HandlerError → Error
  DispatchErr        : DispatchError → Error
  DBCTextParseErr    : DBCTextParseError → Error
  WithContext        : String → Error → Error
  -- Adversarial-input bound exceeded at any parser surface.  Consolidated
  -- from the previously per-ADT `InputBoundExceeded` ctors on ParseError /
  -- FrameError / DBCTextParseError (R19 cluster 14 / AGDA-C-6.2).  The
  -- `BoundKind` discriminates which kind of bound (NestingDepth /
  -- AtomCount / IdentifierLength / FrameByteCount / etc.); the
  -- ADT-prefix discrimination on the wire code is no longer needed —
  -- bindings dispatch on `bound_kind` from the structured payload.
  InputBoundExceeded : BoundKind → ℕ → ℕ → Error

formatError : Error → String
formatError (ParseErr pe)                       = formatParseError pe
formatError (FrameErr fe)                       = formatFrameError fe
formatError (ExtractionErr ee)                  = formatExtractionError ee
formatError (RouteErr re)                       = formatRouteError re
formatError (HandlerErr he)                     = formatHandlerError he
formatError (DispatchErr de)                    = formatDispatchError de
formatError (DBCTextParseErr de)                = formatDBCTextParseError de
formatError (WithContext ctx inner)             = ctx ++ₛ ": " ++ₛ formatError inner
formatError (InputBoundExceeded kind obs limit) =
  boundKindLabel kind ++ₛ " " ++ₛ showℕ obs ++ₛ " exceeds limit " ++ₛ showℕ limit

errorCode : Error → String
errorCode (ParseErr pe)             = parseErrorCode pe
errorCode (FrameErr fe)             = frameErrorCode fe
errorCode (ExtractionErr ee)        = extractionErrorCode ee
errorCode (RouteErr re)             = routeErrorCode re
errorCode (HandlerErr he)           = handlerErrorCode he
errorCode (DispatchErr de)          = dispatchErrorCode de
errorCode (DBCTextParseErr de)      = dbcTextParseErrorCode de
errorCode (WithContext _ inner)     = errorCode inner
errorCode (InputBoundExceeded _ _ _) = "input_bound_exceeded"
