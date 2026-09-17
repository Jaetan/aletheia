#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes every tracked C++ source and header, and the C++ fences the documents
# carry, which the doc-example harness compiles and a reader copies.
# Claim: a const-qualified auto is spelled `auto const`, never `const auto`, the
# one placement the C++ standard in AGENTS/cpp.md fixes, so the tree reads one
# way and a fix-it that writes `auto const` lands in a tree that already does.
# A mention of the rejected spelling itself, in backticks, is not a declaration.
# Non-zero exit: at least one declaration spells it the other way.
set -u
cd "$(dirname "$0")/.." || exit 2
hits=$(git ls-files -z -- '*.cpp' '*.hpp' '*.md' | xargs -0 grep -nE '(^|[^`])\bconst auto\b' || true)
[ -z "$hits" ] || {
    echo "const auto where the standard says auto const:"
    printf '%s\n' "$hits" | head -20
    exit 1
}
exit 0
