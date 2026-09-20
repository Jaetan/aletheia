#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_mutation_setup.py.
# Claim: the gate fires on a test that reads the tree above python/, cannot skip
# and is not excluded from the mutmut lane, and it stays quiet for one that
# reads the same way and skips. mutmut copies python/ alone, so such a path
# resolves to python/ under mutants/ and names nothing; a test that asserts on
# what it found there fails the baseline, which leaves the lane with no mutants
# at all and reads as a lane that ran. Both files are written into
# python/tests/ and removed again, and the tracked tree is checked before and
# after.
# Non-zero exit: the gate passed over the test that cannot run there, refused
# the one that skips, or refused the tracked tree. Exits 2 without the virtual
# environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

asserting=python/tests/test_probe_above_the_tree_asserting.py
skipping=python/tests/test_probe_above_the_tree_skipping.py
trap 'rm -f "$asserting" "$skipping"' EXIT

if ! "$py" -m tools.check_mutation_setup > /dev/null 2>&1; then
	echo "the gate refuses the tracked tree:"
	"$py" -m tools.check_mutation_setup 2>&1 | head -3 | sed 's/^/  /'
	exit 1
fi

# The two files below carry no licence header: they live for one run of this
# probe, are never tracked, and a second declaration in this file is what the
# SPDX gate refuses.
cat > "$asserting" <<'EOF'
"""Written by a probe: reads above python/ and asserts on what it finds."""

from pathlib import Path


def test_the_repository_root_has_workflows() -> None:
    """Fails under mutants/, where parents[2] is python/ itself."""
    assert list((Path(__file__).resolve().parents[2] / ".github" / "workflows").glob("*.yml"))
EOF

out=$(mktemp) || exit 2
if "$py" -m tools.check_mutation_setup > "$out" 2>&1; then
	echo "the gate passed over a test the mutated tree cannot satisfy"
	rm -f "$out"
	exit 1
fi
if ! grep -q "test_probe_above_the_tree_asserting.py" "$out"; then
	echo "the gate failed without naming the test:"
	head -3 "$out" | sed 's/^/  /'
	rm -f "$out"
	exit 1
fi
rm -f "$asserting"

cat > "$skipping" <<'EOF'
"""Written by a probe: reads above python/ and skips when it is not there."""

from pathlib import Path

import pytest


def test_the_repository_root_has_workflows() -> None:
    """Says nothing under mutants/, where parents[2] is python/ itself."""
    workflows = Path(__file__).resolve().parents[2] / ".github" / "workflows"
    if not workflows.is_dir():
        pytest.skip("not the repository root, so there is nothing to read")
    assert list(workflows.glob("*.yml"))
EOF

if ! "$py" -m tools.check_mutation_setup > "$out" 2>&1; then
	echo "the gate refuses a test that reads above python/ and skips:"
	head -3 "$out" | sed 's/^/  /'
	rm -f "$out"
	exit 1
fi
rm -f "$out" "$skipping"

if ! "$py" -m tools.check_mutation_setup > /dev/null 2>&1; then
	echo "the tracked tree does not pass the gate once the probe's files are gone"
	exit 1
fi
echo "PASS: the asserting test fails the gate by name, the skipping one does not"
