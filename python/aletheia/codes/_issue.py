# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""DBC validation issue types — severity, code, and single-issue record.

Mirror of the Agda ``IssueCode`` ADT and the Go ``Issue*`` constants in
``go/aletheia/result.go`` / C++ ``IssueCode`` enum in
``cpp/include/aletheia/validation.hpp``.  The public ``aletheia`` package
re-exports ``IssueCode`` and ``ValidationIssue`` (see ``__init__.py``);
``IssueSeverity`` is accessible as ``aletheia.codes.IssueSeverity``.
"""

from enum import StrEnum
from typing import TypedDict


class IssueSeverity(StrEnum):
    """Validation issue severity."""

    ERROR = "error"
    WARNING = "warning"


class IssueCode(StrEnum):
    """Validation issue codes matching Agda IssueCode enum."""

    DUPLICATE_MESSAGE_ID = "duplicate_message_id"
    DUPLICATE_SIGNAL_NAME = "duplicate_signal_name"
    FACTOR_ZERO = "factor_zero"
    MULTIPLEXOR_NOT_FOUND = "multiplexor_not_found"
    MULTIPLEXOR_CYCLE = "multiplexor_cycle"
    GLOBAL_NAME_COLLISION = "global_name_collision"
    MIN_EXCEEDS_MAX = "min_exceeds_max"
    SIGNAL_EXCEEDS_DLC = "signal_exceeds_dlc"
    SIGNAL_OVERLAP = "signal_overlap"
    BIT_LENGTH_ZERO = "bit_length_zero"
    DUPLICATE_MESSAGE_NAME = "duplicate_message_name"
    OFFSET_SCALE_RANGE = "offset_scale_range"
    EMPTY_MESSAGE = "empty_message"
    START_BIT_OUT_OF_RANGE = "start_bit_out_of_range"
    BIT_LENGTH_EXCESSIVE = "bit_length_excessive"
    MULTIPLEXOR_NON_UNIT_SCALING = "multiplexor_non_unit_scaling"
    DUPLICATE_ATTRIBUTE_NAME = "duplicate_attribute_name"
    UNKNOWN_COMMENT_TARGET = "unknown_comment_target"
    UNKNOWN_MESSAGE_SENDER = "unknown_message_sender"
    UNKNOWN_SIGNAL_RECEIVER = "unknown_signal_receiver"
    UNKNOWN_VALUE_DESCRIPTION_TARGET = "unknown_value_description_target"
    # Text round-trip diagnostics, emitted by format_dbc_text (error-severity for
    # divergence, warning-severity for the rest).
    TEXT_ROUNDTRIP_DIVERGENCE = "text_roundtrip_divergence"
    MULTI_VALUE_MUX_SELECTOR = "multi_value_mux_selector"
    MUX_MASTER_INCOHERENT = "mux_master_incoherent"
    BIG_ENDIAN_MSB_LAYOUT = "big_endian_msb_layout"
    UNKNOWN_ATTRIBUTE_NAME = "unknown_attribute_name"
    ATTRIBUTE_VALUE_TYPE_MISMATCH = "attribute_value_type_mismatch"
    ATTRIBUTE_ENUM_EMPTY = "attribute_enum_empty"
    ATTRIBUTE_ENUM_DEFAULT_UNSTABLE = "attribute_enum_default_unstable"


class ValidationIssue(TypedDict):
    """A single DBC validation issue."""

    severity: IssueSeverity
    code: IssueCode
    detail: str


__all__ = [
    "IssueCode",
    "IssueSeverity",
    "ValidationIssue",
]
