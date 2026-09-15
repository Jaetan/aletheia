#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/response.hpp.
# Claim: what the header's comments cite exists: the kernel emits the
# "uncached_atom" warning kind, its end-of-stream verdict has the Unsure
# constructor the Unresolved verdict mirrors, the first-violation halt and
# the batch ordering are stated in the kernel modules named, and the Go and
# Rust SignalError types exist. Non-zero exit: a citation resolves nowhere.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
need() { grep -qE "$2" "$3" || { echo "unresolved: $1"; status=1; }; }
need "uncached_atom wire string" 'formatWarningKind UncachedAtom = "uncached_atom"' src/Aletheia/Protocol/ResponseFormat.agda
need "FinalVerdict Unsure" '^  Unsure : LTLReason' src/Aletheia/LTL/Incremental.agda
need "first-violation halt" 'First violation halts' src/Aletheia/Protocol/StreamState.agda
need "batch ordering in Message" 'completed before a halting violation come first, then the violation' src/Aletheia/Protocol/Message.agda
need "Go SignalError" '^type SignalError struct' go/aletheia/result.go
need "Rust SignalError" '^pub struct SignalError' rust/src/response.rs
exit $status
