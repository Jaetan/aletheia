#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/README.md.
# Claim: what the prose cites exists and says what the README attributes to
# it. The Go section of the cancellation contract is numbered 2.2 and
# describes the channel semaphore; the client's lock is a field named lockCh
# built as a 1-deep channel; NewFFIBackendFromEnv exists and reads
# ALETHEIA_LIB; the excel module requires excelize. Non-zero exit: a cited
# section, identifier or dependency is gone or no longer says so.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
section=$(awk '/^### 2\.2 Go$/{f=1; next} /^### /{f=0} f' docs/architecture/CANCELLATION.md)
[ -n "$section" ] || { echo "CANCELLATION.md has no section 2.2 Go"; status=1; }
case $section in *"chan struct{}"*) ;; *) echo "section 2.2 no longer describes the channel semaphore"; status=1 ;; esac
grep -q '^	lockCh *chan struct{}' go/aletheia/client.go || { echo "client.go has no lockCh channel field"; status=1; }
grep -q 'lockCh: *make(chan struct{}, 1)' go/aletheia/client.go || { echo "lockCh is not built as a 1-deep channel"; status=1; }
grep -q '^func NewFFIBackendFromEnv(' go/aletheia/ffi.go || { echo "NewFFIBackendFromEnv is gone"; status=1; }
awk '/^func NewFFIBackendFromEnv\(/{f=1} f{print} f && /^}/{exit}' go/aletheia/ffi.go | grep -q 'ALETHEIA_LIB' || { echo "NewFFIBackendFromEnv does not read ALETHEIA_LIB"; status=1; }
grep -q 'github.com/xuri/excelize' go/excel/go.mod || { echo "the excel module does not require excelize"; status=1; }
[ "$status" -eq 0 ] && echo "PASS: the cited section, identifiers and dependency resolve"
exit $status
