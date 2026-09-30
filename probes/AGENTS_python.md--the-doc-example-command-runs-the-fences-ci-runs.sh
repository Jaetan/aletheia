#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes AGENTS/python.md.
# Claim: the doc-example command its Verification block prints collects the
# fences the run_ci step collects, those of the documents DOC_EXAMPLE_DOCS in
# tools/_ci_steps.py names, so a reader running it runs what CI runs. The
# command named a subset of CI's documents, and skipped a guide's fences.
# The command is run only when its shape is the one pinned below, since it
# is read out of a document.
# Non-zero exit: the command is missing or has another shape, fails to
# collect, or collects other fences than the step's documents.
set -u
cd "$(dirname "$0")/.." || exit 2
python=python/.venv/bin/python
[ -f AGENTS/python.md ] && [ -x "$python" ] || exit 2

cmd=$(awk '/^cd "\$\(git rev-parse --show-toplevel\)" && python3 -m pytest --markdown-docs/ {on=1} on {print} on && !/\\$/ {exit}' AGENTS/python.md)
[ -n "$cmd" ] || { echo "AGENTS/python.md prints no doc-example command"; exit 1; }
"$python" - "$cmd" <<'EOF' || exit 1
import re
import sys

joined = " ".join(line.strip().removesuffix("\\").strip() for line in sys.argv[1].splitlines())
documents = r"""\$\(python3 -c 'from tools\._ci_steps import DOC_EXAMPLE_DOCS; print\(\*DOC_EXAMPLE_DOCS, sep="\\n"\)'\)"""
shape = (
    r'cd "\$\(git rev-parse --show-toplevel\)" && python3 -m pytest --markdown-docs '
    r'--rootdir="\$\(pwd\)" -o pythonpath=python/tests ' + documents
)
if not re.fullmatch(shape, joined):
    print(f"the command has another shape than the one this probe runs:\n  {joined}")
    sys.exit(1)
EOF

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
# From a subdirectory, with the venv's interpreter as python3, as a reader in
# an activated venv runs it.
(cd python && PATH="$PWD/.venv/bin:$PATH" bash -c "$cmd --collect-only -q -p no:cacheprovider") > "$scratch/documented.log" 2>&1 || {
    echo "the documented command fails to collect:"
    tail -n 5 "$scratch/documented.log" | sed 's/^/  /'
    exit 1
}
mapfile -t docs < <("$python" -c 'from tools._ci_steps import DOC_EXAMPLE_DOCS; print(*DOC_EXAMPLE_DOCS, sep="\n")')
[ "${#docs[@]}" -gt 0 ] || { echo "DOC_EXAMPLE_DOCS is empty"; exit 1; }
"$python" -m pytest --markdown-docs --collect-only -q -p no:cacheprovider --rootdir "$PWD" \
    -o pythonpath=python/tests "${docs[@]}" > "$scratch/step.log" 2>&1 || {
    echo "the step's documents fail to collect:"
    tail -n 5 "$scratch/step.log" | sed 's/^/  /'
    exit 1
}
documented=$(grep -F '::[CodeFence#' "$scratch/documented.log" | sort)
step=$(grep -F '::[CodeFence#' "$scratch/step.log" | sort)
[ -n "$step" ] || { echo "the step's documents hold no fence"; exit 1; }
if [ "$documented" != "$step" ]; then
    echo "the documented command and the step collect different fences:"
    diff <(printf '%s\n' "$documented") <(printf '%s\n' "$step") | sed 's/^/  /'
    exit 1
fi
echo "PASS: the documented command collects the step's $(printf '%s\n' "$step" | wc -l) fences"
