#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/backend.go.
# Claim: every identifier, file and event the interface comments cite exists
# and is what the comment says: the Client serialises through a field named
# lockCh; the MockBackend holds a sync.Mutex and the FFIBackend struct holds
# none; the C++ header the grouping mirrors still carries its [MANDATORY]
# and [OPTIONAL] markers; the rts.cores_mismatch event is one runtime_start.go
# logs, on the logger the FFIBackend hands it; every [Client.X] doc link names
# a Client method; and every other doc link names a declaration. Non-zero
# exit: a citation resolves nowhere or contradicts the code.
set -u
cd "$(dirname "$0")/.." || exit 2
f=go/aletheia/backend.go
status=0
grep -q '^	lockCh *chan struct{}' go/aletheia/client.go || { echo "client.go has no lockCh field"; status=1; }
grep -q '^	mu *sync.Mutex' go/aletheia/mock.go || { echo "MockBackend has no sync.Mutex"; status=1; }
awk '/^type FFIBackend struct/{f=1} f{print} f && /^}/{exit}' go/aletheia/ffi.go | grep -q 'sync.Mutex' && { echo "FFIBackend carries a mutex, the comment says it does not"; status=1; }
grep -q '\[MANDATORY\]' cpp/include/aletheia/backend.hpp || { echo "backend.hpp has no [MANDATORY] marker"; status=1; }
grep -q '\[OPTIONAL\]' cpp/include/aletheia/backend.hpp || { echo "backend.hpp has no [OPTIONAL] marker"; status=1; }
grep -q '"rts.cores_mismatch"' go/aletheia/runtime_start.go || { echo "runtime_start.go logs no rts.cores_mismatch event"; status=1; }
grep -q 'startRuntimeOn(.*cfg\.logger)' go/aletheia/ffi.go || { echo "the FFIBackend hands the start no logger"; status=1; }
for m in $(grep -o '\[Client\.[A-Za-z]*\]' "$f" | tr -d '[]' | cut -d. -f2 | sort -u); do
    grep -q "^func (c \*Client) $m(" go/aletheia/client.go go/aletheia/client_stream.go go/aletheia/client_enrich.go || { echo "[Client.$m] names no Client method"; status=1; }
done
for t in $(grep -o '\[[A-Z][A-Za-z]*\]' "$f" | tr -d '[]' | sort -u | grep -vx 'MANDATORY\|OPTIONAL'); do
    grep -q "^type $t \|^func $t(" go/aletheia/*.go || { echo "[$t] resolves to no declaration"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: every citation in backend.go resolves"
exit $status
