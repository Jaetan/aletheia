// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The codes an error reply carries: the `error_codes` of
//! `docs/WIRE_CODES.yaml`, one [`ErrorCode`] each, in its order.

/// The machine-readable code of an error reply, the kernel's or the shared
/// library's own, as the Python, Go and C++ vocabularies name them: a reply
/// holding a code outside them is refused.
///
/// Each variant is the code of the `error_codes` row of `docs/WIRE_CODES.yaml`
/// whose name is the variant's in snake case, declared in that file's order;
/// the row says what the code reports.
///
/// The vocabulary is minted by the kernel and grows with kernel features, so
/// this enum is `#[non_exhaustive]`: matches outside this crate carry a `_`
/// arm, and a new kernel code is not a breaking change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ErrorCode {
    // A malformed DBC, property or frame.
    ParseMissingField,
    ParseInvalidByteOrder,
    ParseInvalidPresence,
    ParseMissingSigned,
    ParseInvalidSigned,
    ParseNotAnObject,
    ParseExtCanIdOutOfRange,
    ParseStdCanIdOutOfRange,
    ParseDefaultCanIdOutOfRange,
    ParseInvalidDlcBytes,
    ParseRootNotObject,
    ParseMissingSignalName,
    ParseSignalBitLengthZero,
    ParseSignalStartBitExceedsFrame,
    ParseSignalBitLengthExceedsFrame,
    ParseSignalBigEndianOverflow,
    ParseInvalidKind,
    ParseNonTerminatingRational,
    ParseInvalidIdentifier,
    ParseNonIntegerMultiplexValue,
    ParseNonNaturalField,
    ParseDlcCodeOutOfRange,
    ParsePayloadLengthMismatch,
    ParsePayloadByteOutOfRange,
    ParseNonPositiveDenominator,
    ParseSignalArrayLengthMismatch,
    ParseTimestampPastWire,
    // A signal extracted from a data frame.
    ExtractionMuxValueMismatch,
    ExtractionMuxSignalNotFound,
    ExtractionMuxChainCycle,
    ExtractionMuxExtractionFailed,
    ExtractionValueExceedsWireRange,
    ExtractionSignalPastFrameEnd,
    // A frame built or updated.
    FrameSignalNotFound,
    FrameSignalIndexOob,
    FrameValueOutOfRange,
    FrameValueNotRepresentable,
    FrameSignalsOverlap,
    FrameSignalPastFrameEnd,
    FrameCanIdNotFound,
    FrameCanIdMismatch,
    FrameSignalValueOutOfBounds,
    // A command routed.
    RouteMissingField,
    RouteUnknownCommand,
    RouteMissingCommandField,
    RouteMissingDbcField,
    RouteMissingPropsField,
    // The stream state machine.
    HandlerNoDbc,
    HandlerAlreadyStreaming,
    HandlerNotStreaming,
    HandlerStreamNotStarted,
    HandlerStreamActive,
    HandlerPropertyParseFailed,
    HandlerPropertyRefused,
    HandlerUnknownSignal,
    HandlerValidationFailed,
    HandlerTextRoundtripFailed,
    HandlerNonMonotonicTimestamp,
    // A request dispatched.
    DispatchMissingTypeField,
    DispatchUnknownMessageType,
    DispatchInvalidJson,
    DispatchRequestNotObject,
    // A DBC text or a decimal parsed.
    TextParseFailure,
    TextTrailingInput,
    DbcTextAttributeRefinementFailed,
    // An adversarial-input bound, the DBC character set and its keywords.
    InputBoundExceeded,
    DbcInvalidCharacter,
    DbcKeywordName,
    // The shared library's own refusal of an argument or a result.
    FfiValidationError,
}

/// Every code, in the order of `docs/WIRE_CODES.yaml` and of the declaration.
pub(super) const ERROR_CODES: [ErrorCode; 69] = [
    ErrorCode::ParseMissingField,
    ErrorCode::ParseInvalidByteOrder,
    ErrorCode::ParseInvalidPresence,
    ErrorCode::ParseMissingSigned,
    ErrorCode::ParseInvalidSigned,
    ErrorCode::ParseNotAnObject,
    ErrorCode::ParseExtCanIdOutOfRange,
    ErrorCode::ParseStdCanIdOutOfRange,
    ErrorCode::ParseDefaultCanIdOutOfRange,
    ErrorCode::ParseInvalidDlcBytes,
    ErrorCode::ParseRootNotObject,
    ErrorCode::ParseMissingSignalName,
    ErrorCode::ParseSignalBitLengthZero,
    ErrorCode::ParseSignalStartBitExceedsFrame,
    ErrorCode::ParseSignalBitLengthExceedsFrame,
    ErrorCode::ParseSignalBigEndianOverflow,
    ErrorCode::ParseInvalidKind,
    ErrorCode::ParseNonTerminatingRational,
    ErrorCode::ParseInvalidIdentifier,
    ErrorCode::ParseNonIntegerMultiplexValue,
    ErrorCode::ParseNonNaturalField,
    ErrorCode::ParseDlcCodeOutOfRange,
    ErrorCode::ParsePayloadLengthMismatch,
    ErrorCode::ParsePayloadByteOutOfRange,
    ErrorCode::ParseNonPositiveDenominator,
    ErrorCode::ParseSignalArrayLengthMismatch,
    ErrorCode::ParseTimestampPastWire,
    ErrorCode::ExtractionMuxValueMismatch,
    ErrorCode::ExtractionMuxSignalNotFound,
    ErrorCode::ExtractionMuxChainCycle,
    ErrorCode::ExtractionMuxExtractionFailed,
    ErrorCode::ExtractionValueExceedsWireRange,
    ErrorCode::ExtractionSignalPastFrameEnd,
    ErrorCode::FrameSignalNotFound,
    ErrorCode::FrameSignalIndexOob,
    ErrorCode::FrameValueOutOfRange,
    ErrorCode::FrameValueNotRepresentable,
    ErrorCode::FrameSignalsOverlap,
    ErrorCode::FrameSignalPastFrameEnd,
    ErrorCode::FrameCanIdNotFound,
    ErrorCode::FrameCanIdMismatch,
    ErrorCode::FrameSignalValueOutOfBounds,
    ErrorCode::RouteMissingField,
    ErrorCode::RouteUnknownCommand,
    ErrorCode::RouteMissingCommandField,
    ErrorCode::RouteMissingDbcField,
    ErrorCode::RouteMissingPropsField,
    ErrorCode::HandlerNoDbc,
    ErrorCode::HandlerAlreadyStreaming,
    ErrorCode::HandlerNotStreaming,
    ErrorCode::HandlerStreamNotStarted,
    ErrorCode::HandlerStreamActive,
    ErrorCode::HandlerPropertyParseFailed,
    ErrorCode::HandlerPropertyRefused,
    ErrorCode::HandlerUnknownSignal,
    ErrorCode::HandlerValidationFailed,
    ErrorCode::HandlerTextRoundtripFailed,
    ErrorCode::HandlerNonMonotonicTimestamp,
    ErrorCode::DispatchMissingTypeField,
    ErrorCode::DispatchUnknownMessageType,
    ErrorCode::DispatchInvalidJson,
    ErrorCode::DispatchRequestNotObject,
    ErrorCode::TextParseFailure,
    ErrorCode::TextTrailingInput,
    ErrorCode::DbcTextAttributeRefinementFailed,
    ErrorCode::InputBoundExceeded,
    ErrorCode::DbcInvalidCharacter,
    ErrorCode::DbcKeywordName,
    ErrorCode::FfiValidationError,
];

impl ErrorCode {
    /// The [`ErrorCode`] a wire word names, `None` for a word that names none.
    #[must_use]
    pub fn from_wire(word: &str) -> Option<Self> {
        ERROR_CODES.into_iter().find(|code| code.as_str() == word)
    }

    /// The wire word for this code.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            ErrorCode::ParseMissingField => "parse_missing_field",
            ErrorCode::ParseInvalidByteOrder => "parse_invalid_byte_order",
            ErrorCode::ParseInvalidPresence => "parse_invalid_presence",
            ErrorCode::ParseMissingSigned => "parse_missing_signed",
            ErrorCode::ParseInvalidSigned => "parse_invalid_signed",
            ErrorCode::ParseNotAnObject => "parse_not_an_object",
            ErrorCode::ParseExtCanIdOutOfRange => "parse_ext_can_id_out_of_range",
            ErrorCode::ParseStdCanIdOutOfRange => "parse_std_can_id_out_of_range",
            ErrorCode::ParseDefaultCanIdOutOfRange => "parse_default_can_id_out_of_range",
            ErrorCode::ParseInvalidDlcBytes => "parse_invalid_dlc_bytes",
            ErrorCode::ParseRootNotObject => "parse_root_not_object",
            ErrorCode::ParseMissingSignalName => "parse_missing_signal_name",
            ErrorCode::ParseSignalBitLengthZero => "parse_signal_bit_length_zero",
            ErrorCode::ParseSignalStartBitExceedsFrame => "parse_signal_start_bit_exceeds_frame",
            ErrorCode::ParseSignalBitLengthExceedsFrame => "parse_signal_bit_length_exceeds_frame",
            ErrorCode::ParseSignalBigEndianOverflow => "parse_signal_big_endian_overflow",
            ErrorCode::ParseInvalidKind => "parse_invalid_kind",
            ErrorCode::ParseNonTerminatingRational => "parse_non_terminating_rational",
            ErrorCode::ParseInvalidIdentifier => "parse_invalid_identifier",
            ErrorCode::ParseNonIntegerMultiplexValue => "parse_non_integer_multiplex_value",
            ErrorCode::ParseNonNaturalField => "parse_non_natural_field",
            ErrorCode::ParseDlcCodeOutOfRange => "parse_dlc_code_out_of_range",
            ErrorCode::ParsePayloadLengthMismatch => "parse_payload_length_mismatch",
            ErrorCode::ParsePayloadByteOutOfRange => "parse_payload_byte_out_of_range",
            ErrorCode::ParseNonPositiveDenominator => "parse_non_positive_denominator",
            ErrorCode::ParseSignalArrayLengthMismatch => "parse_signal_array_length_mismatch",
            ErrorCode::ParseTimestampPastWire => "parse_timestamp_past_wire",
            ErrorCode::ExtractionMuxValueMismatch => "extraction_mux_value_mismatch",
            ErrorCode::ExtractionMuxSignalNotFound => "extraction_mux_signal_not_found",
            ErrorCode::ExtractionMuxChainCycle => "extraction_mux_chain_cycle",
            ErrorCode::ExtractionMuxExtractionFailed => "extraction_mux_extraction_failed",
            ErrorCode::ExtractionValueExceedsWireRange => "extraction_value_exceeds_wire_range",
            ErrorCode::ExtractionSignalPastFrameEnd => "extraction_signal_past_frame_end",
            ErrorCode::FrameSignalNotFound => "frame_signal_not_found",
            ErrorCode::FrameSignalIndexOob => "frame_signal_index_oob",
            ErrorCode::FrameValueOutOfRange => "frame_value_out_of_range",
            ErrorCode::FrameValueNotRepresentable => "frame_value_not_representable",
            ErrorCode::FrameSignalsOverlap => "frame_signals_overlap",
            ErrorCode::FrameSignalPastFrameEnd => "frame_signal_past_frame_end",
            ErrorCode::FrameCanIdNotFound => "frame_can_id_not_found",
            ErrorCode::FrameCanIdMismatch => "frame_can_id_mismatch",
            ErrorCode::FrameSignalValueOutOfBounds => "frame_signal_value_out_of_bounds",
            ErrorCode::RouteMissingField => "route_missing_field",
            ErrorCode::RouteUnknownCommand => "route_unknown_command",
            ErrorCode::RouteMissingCommandField => "route_missing_command_field",
            ErrorCode::RouteMissingDbcField => "route_missing_dbc_field",
            ErrorCode::RouteMissingPropsField => "route_missing_props_field",
            ErrorCode::HandlerNoDbc => "handler_no_dbc",
            ErrorCode::HandlerAlreadyStreaming => "handler_already_streaming",
            ErrorCode::HandlerNotStreaming => "handler_not_streaming",
            ErrorCode::HandlerStreamNotStarted => "handler_stream_not_started",
            ErrorCode::HandlerStreamActive => "handler_stream_active",
            ErrorCode::HandlerPropertyParseFailed => "handler_property_parse_failed",
            ErrorCode::HandlerPropertyRefused => "handler_property_refused",
            ErrorCode::HandlerUnknownSignal => "handler_unknown_signal",
            ErrorCode::HandlerValidationFailed => "handler_validation_failed",
            ErrorCode::HandlerTextRoundtripFailed => "handler_text_roundtrip_failed",
            ErrorCode::HandlerNonMonotonicTimestamp => "handler_non_monotonic_timestamp",
            ErrorCode::DispatchMissingTypeField => "dispatch_missing_type_field",
            ErrorCode::DispatchUnknownMessageType => "dispatch_unknown_message_type",
            ErrorCode::DispatchInvalidJson => "dispatch_invalid_json",
            ErrorCode::DispatchRequestNotObject => "dispatch_request_not_object",
            ErrorCode::TextParseFailure => "text_parse_failure",
            ErrorCode::TextTrailingInput => "text_trailing_input",
            ErrorCode::DbcTextAttributeRefinementFailed => "dbc_text_attribute_refinement_failed",
            ErrorCode::InputBoundExceeded => "input_bound_exceeded",
            ErrorCode::DbcInvalidCharacter => "dbc_invalid_character",
            ErrorCode::DbcKeywordName => "dbc_keyword_name",
            ErrorCode::FfiValidationError => "ffi_validation_error",
        }
    }
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}
