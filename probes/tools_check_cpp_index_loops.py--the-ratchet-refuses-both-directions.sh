#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_cpp_index_loops.py.
# Claim: the ratchet fires in both directions, and a gate that fires in only one
# is not a ratchet. A counting loop the record does not name must fail, or a new
# hand-written bound lands unnoticed, which is the defect the record exists for;
# and a row naming a loop the tree no longer holds must fail too, because such a
# row is standing permission to put that loop back, so the gate would pass over
# the very reintroduction it was written to refuse.
# Both halves are checked by injecting the violation and reading the exit code
# and the diagnostic, since a gate whose pass is not the absence of a violation
# has a bug. The forward half runs once per loop spelling, because a gate that
# knew only `for` would be passed by rewriting the header. The injections land
# in a scratch copy of the working tree, so the tree itself is never written: a
# sweep, a hook or a commit reading it meanwhile would take the fixture for the
# user's change.
# Non-zero exit: the gate passed over an unrecorded loop, or over a stale row,
# or refused the tracked tree, or failed without naming what it refused.
# Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
subject=cpp/src/enrich.cpp
record=docs/CPP_INDEX_LOOPS.yaml
[ -f "$subject" ] || exit 2
[ -f "$record" ] || exit 2

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
    git -C "$tree" apply --index --allow-empty || exit 2
lens() { (cd "$tree" && "$py" -m tools.check_cpp_index_loops); }
cp "$tree/$subject" "$work/subject" || exit 2

if ! lens > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# Forward, once per loop spelling. A gate that knew only `for` would be passed
# by rewriting the header, so `while` and `do`/`while` are injected too; each
# steps its index in the body, which is where the header alone cannot see it.
probe_forward() {
	cat >> "$tree/$subject"
	if lens > "$work/forward.txt" 2>&1; then
		echo "the gate passed over an unrecorded $1 loop"
		return 1
	fi
	if ! grep -q "$2" "$work/forward.txt"; then
		echo "the gate refused an unrecorded $1 loop without printing it:"
		head -4 "$work/forward.txt" | sed 's/^/  /'
		return 1
	fi
	cp "$work/subject" "$tree/$subject"
}

probe_forward for "i < v.size()" << 'CPP' || exit 1

namespace {
// Probe fixture, in a scratch copy of the tree.
void aletheia_probe_for(std::span<const int> v) {
    int total = 0;
    for (std::size_t i = 0; i < v.size(); ++i)
        total += v[i];
    (void)total;
}
} // namespace
CPP

probe_forward while "while (i < v.size())" << 'CPP' || exit 1

namespace {
// Probe fixture, in a scratch copy of the tree.
void aletheia_probe_while(std::span<const int> v) {
    int total = 0;
    std::size_t i = 0;
    while (i < v.size()) {
        total += v[i];
        ++i;
    }
    (void)total;
}
} // namespace
CPP

probe_forward do-while "do ... while" << 'CPP' || exit 1

namespace {
// Probe fixture, in a scratch copy of the tree.
void aletheia_probe_do_while(std::span<const int> v) {
    int total = 0;
    std::size_t i = 0;
    do {
        total += v[i];
        ++i;
    } while (i < v.size());
    (void)total;
}
} // namespace
CPP

# Reverse: a row whose loop the tree does not hold.
cat >> "$tree/$record" << 'YAML'
  - file: cpp/src/enrich.cpp
    text: "for (std::size_t aletheia_probe = 0; aletheia_probe < 1; ++aletheia_probe)"
    count: 1
YAML
if lens > "$work/reverse.txt" 2>&1; then
	echo "the gate passed over a row naming a loop the tree does not hold"
	exit 1
fi
if ! grep -q "aletheia_probe" "$work/reverse.txt"; then
	echo "the gate refused a stale row without printing it:"
	head -4 "$work/reverse.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: an unrecorded for, while and do-while, and a stale row, each fail the gate by name"
