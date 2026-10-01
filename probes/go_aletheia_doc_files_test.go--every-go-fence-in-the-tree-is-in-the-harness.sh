#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/doc_files_test.go.
# Claim: every tracked Markdown file that carries a Go fence is in the
# harness's docFiles list, so no Go example in the documentation escapes
# compilation and execution, and every listed file is tracked. A Go fence is
# read the way the harness's extractor reads it: leading blanks stripped, then
# an opening fence of three backticks whose info string's first word is exactly
# go and holds no backtick. Code no check runs opens with tildes, which neither
# reads.
# Non-zero exit: a file with a Go fence is not listed, a listed file is not
# tracked, or the list cannot be read.
set -u
cd "$(dirname "$0")/.." || exit 2
listed=$(awk '$0 == "var docFiles = []string{" {on=1; next} on && /^\}$/ {exit} on' go/aletheia/doc_files_test.go \
	| grep -o '"[^"]*\.md"' | tr -d '"' | sort)
[ -n "$listed" ] || { echo "no docFiles entries found"; exit 2; }
status=0
for f in $listed; do
	git ls-files --error-unmatch "$f" > /dev/null 2>&1 || { echo "$f is listed and not tracked"; status=1; }
done
fenced=$(git ls-files -z -- '*.md' '*.mdx' '*.svx' | xargs -0 awk '
	{ line = $0; sub(/^[ \t]+/, "", line) }
	line ~ /^```go([ \t][^`]*)?$/ { print FILENAME; nextfile }' | sort)
for f in $fenced; do
	printf '%s\n' "$listed" | grep -qxF "$f" || { echo "$f carries a Go fence and is not in docFiles"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: every Markdown file with a Go fence is listed ($(printf '%s\n' "$fenced" | wc -l) files carry one)"
exit $status
