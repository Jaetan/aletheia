#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/error.go.
# Claim: every peer-binding surface its typed-error documentation names is
# there under the name it gives. Python has the InputBoundExceededError,
# DBCValidationFailedError and TextRoundTripFailedError classes; Rust has the
# Error::InputBoundExceeded, Error::ValidationFailed and
# Error::TextRoundtripFailed variants; C++ has the InputBoundExceededError
# struct and, for the two refusals it gives no separate type, the
# ErrorCode::HandlerValidationFailed and ErrorCode::HandlerTextRoundtripFailed
# members. The documentation is read as one blob, so a sentence wrapped across
# comment lines is still matched. Non-zero exit: a named surface is missing,
# or the documentation stopped naming one and this probe outlived its claim.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
doc=$(grep '^[[:space:]]*//' go/aletheia/error.go | sed 's|^[[:space:]]*//[[:space:]]\?||' | tr '\n' ' ')

# names <sentence> <file> <pattern> <what>
names() {
    case $doc in
        *"$1"*) ;;
        *) echo "error.go no longer says \"$1\"; retire this line of the probe with the claim"; status=1; return ;;
    esac
    grep -qE "$3" "$2" || { echo "$4 is missing from $2"; status=1; }
}

names "Python's InputBoundExceededError" python/aletheia/client/_types.py '^class InputBoundExceededError' "the Python bound class"
names "Python raises DBCValidationFailedError" python/aletheia/client/_types.py '^class DBCValidationFailedError' "the Python validation-failed class"
names "Python raises TextRoundTripFailedError" python/aletheia/client/_types.py '^class TextRoundTripFailedError' "the Python round-trip class"
names "Error::InputBoundExceeded" rust/src/error.rs '^    InputBoundExceeded \{' "the Rust bound variant"
names "Error::ValidationFailed" rust/src/error.rs '^    ValidationFailed \{' "the Rust validation-failed variant"
names "Error::TextRoundtripFailed" rust/src/error.rs '^    TextRoundtripFailed \{' "the Rust round-trip variant"
names "aletheia::InputBoundExceededError" cpp/include/aletheia/limits.hpp 'struct InputBoundExceededError' "the C++ bound struct"
names "ErrorCode::HandlerValidationFailed" cpp/include/aletheia/error.hpp 'HandlerValidationFailed,' "the C++ validation-failed code"
names "ErrorCode::HandlerTextRoundtripFailed" cpp/include/aletheia/error.hpp 'HandlerTextRoundtripFailed,' "the C++ round-trip code"

[ "$status" -eq 0 ] && echo "PASS: every peer error surface error.go names is there"
exit $status
