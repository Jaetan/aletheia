#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_cpp_restated_types.py.
# Claim: the ratchet fires in both directions, and refuses to pass when it could
# not run. A declaration restating a type the record does not name must fail, or
# a type written twice lands unnoticed, which is the defect the record exists
# for; a row naming a declaration the tree no longer holds must fail too, since
# such a row is standing permission to write that declaration back; and a run
# with no compile database must fail rather than report a clean tree, because a
# gate whose pass is not the absence of a violation has a bug.
# Each half is checked by injecting the violation and reading the exit code and
# the diagnostic. The injections land in a scratch copy of the working tree,
# with the compile database rewritten to it and the fetched dependencies shared
# read-only, so the tree itself is never written: a sweep, a hook or a commit
# reading it meanwhile would take the fixture for the user's change. The gate
# parses the copy from disk through the rewritten compile command, so no
# rebuild is needed.
# Non-zero exit: the gate passed over a restating declaration, or over a stale
# row, or over a missing compile database, or refused the tracked tree, or
# failed without naming what it refused.
# Exits 2 without the virtual environment or without the configured build tree.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
subject=cpp/src/enrich.cpp
record=docs/CPP_RESTATED_TYPES.yaml
[ -f "$subject" ] || exit 2
[ -f "$record" ] || exit 2
[ -f cpp/build/compile_commands.json ] || exit 2

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
    git -C "$tree" apply --index --allow-empty || exit 2
mkdir -p "$tree/cpp/build" || exit 2
ln -s "$PWD/cpp/build/_deps" "$tree/cpp/build/_deps" || exit 2
sed "s|$PWD/cpp|$tree/cpp|g" cpp/build/compile_commands.json > "$tree/cpp/build/compile_commands.json" || exit 2
lens() { (cd "$tree" && "$py" -m tools.check_cpp_restated_types); }
cp "$tree/$subject" "$work/subject" || exit 2

if ! lens > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# Forward: a declaration whose initializer already fixes its type, written out.
cat >> "$tree/$subject" << 'CPP'

namespace {
// Probe fixture, in a scratch copy of the tree.
auto aletheia_probe_restated(const std::string& s) -> std::string {
    const std::string copy = s.substr(0);
    return copy;
}
} // namespace
CPP
if lens > "$work/forward.txt" 2>&1; then
	echo "the gate passed over a declaration restating its type"
	exit 1
fi
if ! grep -q "const std::string copy = s.substr(0)" "$work/forward.txt"; then
	echo "the gate refused a restating declaration without printing it:"
	head -4 "$work/forward.txt" | sed 's/^/  /'
	exit 1
fi
cp "$work/subject" "$tree/$subject"

# Reverse: a row whose declaration the tree does not hold.
cat >> "$tree/$record" << 'YAML'
  - file: cpp/src/enrich.cpp
    text: "const std::string aletheia_probe = s.substr(0)"
    count: 1
YAML
if lens > "$work/reverse.txt" 2>&1; then
	echo "the gate passed over a row naming a declaration the tree does not hold"
	exit 1
fi
if ! grep -q "aletheia_probe" "$work/reverse.txt"; then
	echo "the gate refused a stale row without printing it:"
	head -4 "$work/reverse.txt" | sed 's/^/  /'
	exit 1
fi

# Could not run: an unconfigured tree must fail, not read as clean.
if "$py" - "$work" << 'PY' > "$work/nodb.txt" 2>&1; then
import sys
from pathlib import Path

from tools.check_cpp_restated_types import translation_units

answer = translation_units(Path(sys.argv[1]))
if isinstance(answer, str):
    print(answer)
    sys.exit(1)
print(f"a tree with no compile database yielded {len(answer)} translation units")
PY
	echo "the gate read an unconfigured tree as one it could scan:"
	head -2 "$work/nodb.txt" | sed 's/^/  /'
	exit 1
fi
if ! grep -q "cmake -B build" "$work/nodb.txt"; then
	echo "the refusal does not say how to configure the tree:"
	head -2 "$work/nodb.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a restating declaration, a stale row, and a tree it cannot scan each fail the gate by name"
