# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/error.hpp.
# Claim: every name the header's comments cite resolves: the Agda errorCode
# function the codes mirror, the cancellation rule in CANCELLATION.md, and
# the Go, Python and Rust counterparts of the binary-path, input-bound and
# round-trip errors. Non-zero exit: a citation resolves nowhere.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
need() { grep -qE "$2" "$3" || { echo "unresolved: $1"; status=1; }; }
need "Agda errorCode" '^errorCode : Error' src/Aletheia/Error.agda
need "CANCELLATION.md Rule 1 heading" '^### .*Rule 1 .*cooperative at FFI boundaries' docs/architecture/CANCELLATION.md
need "Go ErrBinaryPathUnsupported" '^var ErrBinaryPathUnsupported' go/aletheia/error.go
need "Go InputBoundExceededError" '^type InputBoundExceededError struct' go/aletheia/error.go
need "Python InputBoundExceededError" '^class InputBoundExceededError' python/aletheia/client/_types.py
need "Go text round-trip code" 'CodeHandlerTextRoundtripFailed' go/aletheia/error.go
need "Rust text round-trip error" 'TextRoundtripFailed' rust/src/error.rs
exit $status
