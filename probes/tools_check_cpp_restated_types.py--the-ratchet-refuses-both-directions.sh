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
# the diagnostic. The forward half injects into a tracked source, which the gate
# parses from disk through the recorded compile command, so no rebuild is
# needed. The tracked files are restored from copies rather than from git, so
# the probe cannot discard unrelated work in the tree.
# Non-zero exit: the gate passed over a restating declaration, or over a stale
# row, or over a missing compile database, or refused the tracked tree, or
# failed without naming what it refused.
# Exits 2 without the virtual environment or without the configured build tree.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
subject=cpp/src/enrich.cpp
record=docs/CPP_RESTATED_TYPES.yaml
[ -f "$subject" ] || exit 2
[ -f "$record" ] || exit 2
[ -f cpp/build/compile_commands.json ] || exit 2

work=$(mktemp -d) || exit 2
trap 'cp "$work/subject" '"$subject"' 2> /dev/null; cp "$work/record" '"$record"' 2> /dev/null; rm -rf "$work"' EXIT
cp "$subject" "$work/subject"
cp "$record" "$work/record"

if ! "$py" -m tools.check_cpp_restated_types > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# Forward: a declaration whose initializer already fixes its type, written out.
cat >> "$subject" << 'CPP'

namespace {
// Probe fixture: removed by the probe before it exits.
auto aletheia_probe_restated(const std::string& s) -> std::string {
    const std::string copy = s.substr(0);
    return copy;
}
} // namespace
CPP
if "$py" -m tools.check_cpp_restated_types > "$work/forward.txt" 2>&1; then
	echo "the gate passed over a declaration restating its type"
	exit 1
fi
if ! grep -q "const std::string copy = s.substr(0)" "$work/forward.txt"; then
	echo "the gate refused a restating declaration without printing it:"
	head -4 "$work/forward.txt" | sed 's/^/  /'
	exit 1
fi
cp "$work/subject" "$subject"

# Reverse: a row whose declaration the tree does not hold.
cat >> "$record" << 'YAML'
  - file: cpp/src/enrich.cpp
    text: "const std::string aletheia_probe = s.substr(0)"
    count: 1
YAML
if "$py" -m tools.check_cpp_restated_types > "$work/reverse.txt" 2>&1; then
	echo "the gate passed over a row naming a declaration the tree does not hold"
	exit 1
fi
if ! grep -q "aletheia_probe" "$work/reverse.txt"; then
	echo "the gate refused a stale row without printing it:"
	head -4 "$work/reverse.txt" | sed 's/^/  /'
	exit 1
fi
cp "$work/record" "$record"

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

if ! "$py" -m tools.check_cpp_restated_types > "$work/restored.txt" 2>&1; then
	echo "the tree did not come back clean after the probe:"
	head -4 "$work/restored.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a restating declaration, a stale row, and a tree it cannot scan each fail the gate by name"
