#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes every tracked file.
# Claim: no tracked file carries a stray tool-call tag on a line of its own.
# An assistant writing a file through a tool call can leave the call's own
# closing tags in the content, and nothing notices: the file still parses, the
# renderer hides an unknown tag, and the gates read the text above it. The
# repository's front page and its pitch both ended in such tags, and had since
# they were written.
# The tags are matched on a line of their own so that prose about them, and
# this file, do not trip it.
# Non-zero exit: a tracked file carries one.
set -u
cd "$(dirname "$0")/.." || exit 2

hits=$(git grep -n -E '^</(content|invoke|function_calls|antml:[a-z_]+)>$' -- . ':!probes/*' || true)
if [ -n "$hits" ]; then
    echo "a tracked file carries a stray tool-call tag:"
    printf '%s\n' "$hits" | sed 's/^/  /'
    exit 1
fi
echo "PASS: no tracked file carries a stray tool-call tag"
