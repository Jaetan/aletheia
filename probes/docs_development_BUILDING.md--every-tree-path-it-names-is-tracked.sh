#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md.
# Claim: every repository path the guide names in backticks resolves to a
# tracked file or directory: a path under a top-level source directory, a
# Dockerfile, or a bare file name such as a Cabal or Agda library file (matched
# on its base name; the standard library's own .agda-lib lives outside the
# tree and is not one). Build outputs (build/, cpp/build, python/.venv) are
# not tracked and are not checked. The guide used to name a Dockerfile the tree no
# longer carries.
# Non-zero exit: the guide names a path nothing in the tree tracks.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
tracked=$(git ls-files)
[ -n "$tracked" ] || exit 2
tokens=$(grep -oE '`[^` ]+`' "$doc" | tr -d '`' | sort -u \
    | grep -E '^((tools|docs|cpp|go|rust|python|src|haskell-shim|examples|probes|packaging|benchmarks)/[A-Za-z0-9_./-]+|Dockerfile[.A-Za-z]*|[A-Za-z_.-]+\.(cabal|md)|aletheia\.agda-lib)$' \
    | grep -vE '(^|/)build(/|$)|\.venv' | sed 's#/$##')
status=0; n=0
for t in $tokens; do
    n=$((n + 1))
    case $t in
        */*) printf '%s\n' "$tracked" | grep -qE "^$t(/|$)" || { echo "not tracked: $t"; status=1; } ;;
        *)   printf '%s\n' "$tracked" | grep -qE "(^|/)$t$" || { echo "not tracked: $t"; status=1; } ;;
    esac
done
[ "$n" -gt 0 ] || { echo "no path token found; the probe would pass vacuously"; exit 2; }
[ "$status" -eq 0 ] && echo "PASS: all $n tree paths the guide names are tracked"
exit "$status"
