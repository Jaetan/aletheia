// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <string>
#include <vector>

namespace aletheia {

enum class IssueSeverity { Error, Warning };

enum class IssueCode {
    DuplicateMessageId,
    DuplicateMessageName,
    DuplicateSignalName,
    FactorZero,
    MultiplexorNotFound,
    MultiplexorCycle,
    GlobalNameCollision,
    MinExceedsMax,
    SignalExceedsDlc,
    SignalOverlap,
    BitLengthZero,
    OffsetScaleRange,
    EmptyMessage,
    StartBitOutOfRange,
    BitLengthExcessive,
    MultiplexorNonUnitScaling,
    DuplicateAttributeName,
    UnknownCommentTarget,
    UnknownMessageSender,
    Unknown
};

struct ValidationIssue {
    IssueSeverity severity;
    IssueCode code;
    std::string detail;
};

struct ValidationResult {
    bool has_errors;
    std::vector<ValidationIssue> issues;
};

} // namespace aletheia
