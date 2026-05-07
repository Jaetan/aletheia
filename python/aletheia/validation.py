"""DBC validation issue types — severity, code, and single-issue record.

Split out of ``protocols.py`` at Track E.11 (2026-05-08) when CHECK 23
(``UnknownValueDescriptionTarget``) plus the CHECK 21 mirror gap fix
(``UnknownSignalReceiver``) pushed ``protocols.py`` over the 1000-line
pylint threshold.  Per ``feedback_no_weak_config_bumps.md``, splitting
is the response to a tripped lint threshold — not bumping the limit.

The public ``aletheia`` package re-exports ``IssueCode`` and
``ValidationIssue`` from here (see ``__init__.py``); ``IssueSeverity`` is
accessible as ``aletheia.validation.IssueSeverity``.
"""

from enum import Enum
from typing import TypedDict


class IssueSeverity(str, Enum):
    """Validation issue severity"""
    ERROR = "error"
    WARNING = "warning"


class IssueCode(str, Enum):
    """Validation issue codes matching Agda IssueCode enum"""
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


class ValidationIssue(TypedDict):
    """A single DBC validation issue"""
    severity: IssueSeverity
    code: IssueCode
    detail: str


__all__ = [
    "IssueSeverity",
    "IssueCode",
    "ValidationIssue",
]
