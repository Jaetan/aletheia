#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/mock.go against python/aletheia/client/_backend.py.
# Claim: the sentinels this binding's mock records for the binary operations
# are the ones the Python mock records, name for name. The two mocks exist so
# that a test in either language can assert which operation a client reached,
# and a cross-binding test that compares those assertions reads the same words
# in both. Nothing compiles one list against the other. Non-zero exit: the two
# mocks record different operation names, or either file stopped recording any.
set -u
cd "$(dirname "$0")/.." || exit 2
go_mock=go/aletheia/mock.go
py_mock=python/aletheia/client/_backend.py
for f in "$go_mock" "$py_mock"; do
	[ -f "$f" ] || { echo "missing $f"; exit 1; }
done

# Only the names passed at a call site count; the prose above them says
# <binary:OP> and must not be read as an operation.
go_names=$(grep -oP 'Process\(state, "<binary:\K[a-zA-Z]+' "$go_mock" | sort -u)
py_names=$(grep -oP '_record_and_pop\(b"<binary:\K[a-zA-Z]+' "$py_mock" | sort -u)

if [ -z "$go_names" ] || [ -z "$py_names" ]; then
	echo "one of the two mocks records no sentinel; the probe is reading it wrong"
	exit 1
fi
if [ "$go_names" = "$py_names" ]; then
	echo "PASS: both mocks record the same $(printf '%s\n' "$go_names" | wc -l) operations"
	exit 0
fi
echo "the two mocks record different operations"
diff <(printf '%s\n' "$py_names") <(printf '%s\n' "$go_names") | sed 's/^</  python: /; s/^>/  go: /'
exit 1
