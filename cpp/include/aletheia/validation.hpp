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
    MultiplexorNotAlwaysPresent,
    GlobalNameCollision,
    MinExceedsMax,
    SignalExceedsDlc,
    SignalOverlap,
    BitLengthZero,
    DlcOutOfRange,
    OffsetScaleRange,
    EmptyMessage,
    StartBitOutOfRange,
    BitLengthExcessive
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
