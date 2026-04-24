"""Machine-readable error codes mirroring Agda's ``Error`` ADT.

This module is the Python side of the cross-binding error-code contract.
The wire values here correspond 1:1 to the strings emitted by
``errorCode`` / ``parseErrorCode`` / ``frameErrorCode`` / ``routeErrorCode``
/ ``handlerErrorCode`` / ``dispatchErrorCode`` / ``extractionErrorCode``
in ``src/Aletheia/Error.agda``.

Kept in its own module so the protocol TypedDicts and the enum don't all
pile into one oversized file.  ``tests/test_error_code_sync.py`` parses
the Agda source and asserts this enum is a reciprocal superset — drift
either direction fails CI.
"""

from enum import Enum


class ErrorCode(str, Enum):
    """Machine-readable error codes matching Agda Error ADT.

    Each code maps 1:1 to an Agda error constructor via errorCode.
    """
    # Parse errors
    PARSE_MISSING_FIELD = "parse_missing_field"
    PARSE_INVALID_BYTE_ORDER = "parse_invalid_byte_order"
    PARSE_INVALID_PRESENCE = "parse_invalid_presence"
    PARSE_MISSING_SIGNED = "parse_missing_signed"
    PARSE_INVALID_SIGNED = "parse_invalid_signed"
    PARSE_NOT_AN_OBJECT = "parse_not_an_object"
    PARSE_EXT_CAN_ID_OUT_OF_RANGE = "parse_ext_can_id_out_of_range"
    PARSE_STD_CAN_ID_OUT_OF_RANGE = "parse_std_can_id_out_of_range"
    PARSE_DEFAULT_CAN_ID_OUT_OF_RANGE = "parse_default_can_id_out_of_range"
    PARSE_INVALID_DLC_BYTES = "parse_invalid_dlc_bytes"
    PARSE_ROOT_NOT_OBJECT = "parse_root_not_object"
    PARSE_MISSING_SIGNAL_NAME = "parse_missing_signal_name"
    PARSE_SIGNAL_BIT_LENGTH_ZERO = "parse_signal_bit_length_zero"
    PARSE_SIGNAL_OVERFLOWS_FRAME = "parse_signal_overflows_frame"
    PARSE_SIGNAL_MSB_BELOW_BIT_LENGTH = "parse_signal_msb_below_bit_length"
    PARSE_INVALID_KIND = "parse_invalid_kind"
    PARSE_NON_TERMINATING_RATIONAL = "parse_non_terminating_rational"
    PARSE_INVALID_IDENTIFIER = "parse_invalid_identifier"
    # Frame errors
    FRAME_SIGNAL_NOT_FOUND = "frame_signal_not_found"
    FRAME_SIGNAL_INDEX_OOB = "frame_signal_index_oob"
    FRAME_INJECTION_FAILED = "frame_injection_failed"
    FRAME_SIGNALS_OVERLAP = "frame_signals_overlap"
    FRAME_CAN_ID_NOT_FOUND = "frame_can_id_not_found"
    FRAME_CAN_ID_MISMATCH = "frame_can_id_mismatch"
    FRAME_SIGNAL_VALUE_OUT_OF_BOUNDS = "frame_signal_value_out_of_bounds"
    # Route errors
    ROUTE_MISSING_FIELD = "route_missing_field"
    ROUTE_MISSING_ARRAY = "route_missing_array"
    ROUTE_UNKNOWN_COMMAND = "route_unknown_command"
    ROUTE_MISSING_COMMAND_FIELD = "route_missing_command_field"
    ROUTE_DLC_EXCEEDS_MAX = "route_dlc_exceeds_max"
    ROUTE_BYTE_ARRAY_PARSE_FAILED = "route_byte_array_parse_failed"
    ROUTE_BYTE_COUNT_MISMATCH = "route_byte_count_mismatch"
    ROUTE_MISSING_DBC_FIELD = "route_missing_dbc_field"
    ROUTE_MISSING_PROPS_FIELD = "route_missing_props_field"
    # Handler errors
    HANDLER_NO_DBC = "handler_no_dbc"
    HANDLER_ALREADY_STREAMING = "handler_already_streaming"
    HANDLER_NOT_STREAMING = "handler_not_streaming"
    HANDLER_STREAM_NOT_STARTED = "handler_stream_not_started"
    HANDLER_STREAM_ACTIVE = "handler_stream_active"
    HANDLER_PROPERTY_PARSE_FAILED = "handler_property_parse_failed"
    HANDLER_INVALID_DLC_CODE = "handler_invalid_dlc_code"
    HANDLER_VALIDATION_FAILED = "handler_validation_failed"
    HANDLER_NON_MONOTONIC_TIMESTAMP = "handler_non_monotonic_timestamp"
    # Dispatch errors
    DISPATCH_MISSING_TYPE_FIELD = "dispatch_missing_type_field"
    DISPATCH_UNKNOWN_MESSAGE_TYPE = "dispatch_unknown_message_type"
    DISPATCH_INVALID_JSON = "dispatch_invalid_json"
    DISPATCH_REQUEST_NOT_OBJECT = "dispatch_request_not_object"
    # Extraction errors
    EXTRACTION_MUX_VALUE_MISMATCH = "extraction_mux_value_mismatch"
    EXTRACTION_MUX_SIGNAL_NOT_FOUND = "extraction_mux_signal_not_found"
    EXTRACTION_MUX_CHAIN_CYCLE = "extraction_mux_chain_cycle"
    EXTRACTION_MUX_EXTRACTION_FAILED = "extraction_mux_extraction_failed"
    EXTRACTION_BIT_EXTRACTION_FAILED = "extraction_bit_extraction_failed"


__all__ = ["ErrorCode"]
