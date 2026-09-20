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
# knew only `for` would be passed by rewriting the header. The tracked files are restored from copies rather than from git, so
# the probe cannot discard unrelated work in the tree.
# Non-zero exit: the gate passed over an unrecorded loop, or over a stale row,
# or refused the tracked tree, or failed without naming what it refused.
# Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
subject=cpp/src/enrich.cpp
record=docs/CPP_INDEX_LOOPS.yaml
[ -f "$subject" ] || exit 2
[ -f "$record" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'cp "$work/subject" '"$subject"' 2> /dev/null; cp "$work/record" '"$record"' 2> /dev/null; rm -rf "$work"' EXIT
cp "$subject" "$work/subject"
cp "$record" "$work/record"

if ! "$py" -m tools.check_cpp_index_loops > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# Forward, once per loop spelling. A gate that knew only `for` would be passed
# by rewriting the header, so `while` and `do`/`while` are injected too; each
# steps its index in the body, which is where the header alone cannot see it.
probe_forward() {
	cat >> "$subject"
	if "$py" -m tools.check_cpp_index_loops > "$work/forward.txt" 2>&1; then
		echo "the gate passed over an unrecorded $1 loop"
		cp "$work/subject" "$subject"
		return 1
	fi
	if ! grep -q "$2" "$work/forward.txt"; then
		echo "the gate refused an unrecorded $1 loop without printing it:"
		head -4 "$work/forward.txt" | sed 's/^/  /'
		cp "$work/subject" "$subject"
		return 1
	fi
	cp "$work/subject" "$subject"
}

probe_forward for "i < v.size()" << 'CPP' || exit 1

namespace {
// Probe fixture: removed by the probe before it exits.
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
// Probe fixture: removed by the probe before it exits.
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
// Probe fixture: removed by the probe before it exits.
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
cat >> "$record" << 'YAML'
  - file: cpp/src/enrich.cpp
    text: "for (std::size_t aletheia_probe = 0; aletheia_probe < 1; ++aletheia_probe)"
    count: 1
YAML
if "$py" -m tools.check_cpp_index_loops > "$work/reverse.txt" 2>&1; then
	echo "the gate passed over a row naming a loop the tree does not hold"
	exit 1
fi
if ! grep -q "aletheia_probe" "$work/reverse.txt"; then
	echo "the gate refused a stale row without printing it:"
	head -4 "$work/reverse.txt" | sed 's/^/  /'
	exit 1
fi
cp "$work/record" "$record"

if ! "$py" -m tools.check_cpp_index_loops > "$work/restored.txt" 2>&1; then
	echo "the tree did not come back clean after the probe:"
	head -4 "$work/restored.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: an unrecorded for, while and do-while, and a stale row, each fail the gate by name"
