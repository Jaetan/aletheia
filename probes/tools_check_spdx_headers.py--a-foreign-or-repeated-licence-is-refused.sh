#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_spdx_headers.py.
# Claim: the gate checks agreement, not only presence. A file carrying the
# compliant header pair and a second declaration, or one naming a licence the
# repository does not grant, makes the gate exit non-zero and name the file.
# The check runs against a throwaway repository under the build tree, so the
# worktree is never modified. Non-zero exit: the gate accepts a foreign
# identifier, accepts a repeated one, or refuses a compliant tree. Exits 2
# when git or the interpreter is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
repo=$PWD
py=$repo/python/.venv/bin/python
command -v git > /dev/null && [ -x "$py" ] || exit 2
scratch=cpp/build/probe-scratch/spdx-agreement
rm -rf "$scratch"
mkdir -p "$scratch" || exit 2
# The gate anchors its repository root on its own module path, so the copy of
# the package is what puts the throwaway repository in scope.
cp -r tools "$scratch/tools" || exit 2
printf 'Copyright 2025 Nicolas Pelletier\n' > "$scratch/LICENSE.md"
printf '# SPDX-FileCopyrightText: 2025 Nicolas Pelletier\n# SPDX-License-Identifier: BSD-2-Clause\n' > "$scratch/ok.py"
(cd "$scratch" && git init -q . && git add -A) || exit 2

run() { (cd "$scratch" && "$py" -m tools.check_spdx_headers 2>&1); }

out=$(run); rc=$?
[ "$rc" -eq 0 ] || { echo "a compliant tree was refused: $out"; exit 1; }

printf '# SPDX-FileCopyrightText: 2025 Nicolas Pelletier\n# SPDX-License-Identifier: Apache-2.0\n' > "$scratch/foreign.py"
(cd "$scratch" && git add -A)
out=$(run); rc=$?
[ "$rc" -ne 0 ] || { echo "a foreign licence identifier was accepted"; exit 1; }
# The reason matters, not only the exit code: a file whose only declaration
# is foreign also lacks the compliant pair, so the presence arm alone would
# refuse it and the agreement arm could be absent without the probe noticing.
case $out in *foreign.py*does\ not\ grant*) ;; *) echo "the refusal is not about the licence: $out"; exit 1 ;; esac
rm -f "$scratch/foreign.py"

printf '# SPDX-FileCopyrightText: 2025 Nicolas Pelletier\n# SPDX-License-Identifier: BSD-2-Clause\n# SPDX-License-Identifier: BSD-2-Clause\n' > "$scratch/twice.py"
(cd "$scratch" && git add -A)
out=$(run); rc=$?
[ "$rc" -ne 0 ] || { echo "a repeated licence declaration was accepted"; exit 1; }
case $out in *twice.py*) ;; *) echo "the refusal does not name the file: $out"; exit 1 ;; esac
rm -rf "$scratch"
