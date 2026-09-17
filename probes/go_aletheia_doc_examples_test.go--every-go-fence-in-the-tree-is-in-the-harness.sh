#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/doc_examples_test.go.
# Claim: every tracked Markdown file that carries a Go fence is in the
# harness's docFiles list, so no Go example in the documentation escapes
# compilation and execution, and every listed file exists. CHANGELOG.md is
# the one exception: its fences describe past releases. Non-zero exit: a file
# with a Go fence is unlisted, or a listed file is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
listed=$(grep -o '"\.\./[^"]*\.md"' go/aletheia/doc_examples_test.go | tr -d '"' | sed 's|^\.\./\.\./||; s|^\.\./|go/|' | sort)
[ -n "$listed" ] || { echo "no docFiles entries found"; exit 1; }
for f in $listed; do
    git ls-files --error-unmatch "$f" > /dev/null 2>&1 || { echo "$f is listed and not tracked"; status=1; }
done
for f in $(git grep -l '^```go' -- '*.md' | sort); do
    [ "$f" = "CHANGELOG.md" ] && continue
    printf '%s\n' "$listed" | grep -qxF "$f" || { echo "$f carries a Go fence and is not in docFiles"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: every Markdown file with a Go fence is in the harness ($(printf '%s\n' "$listed" | wc -l) listed)"
exit $status
