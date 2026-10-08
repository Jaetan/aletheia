#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_precise_hints.py.
# Claim: the ratchet fires in both directions. An imprecise hint the record
# does not name fails, whichever fault it holds and wherever it is written:
# Any or object, a primitive inside a container or as a key, three nested
# subscripts, an alias over one of those, and a hint in the Python a probe
# hands its interpreter, which no other checker reads. A row naming more hints
# than its file holds fails too, since it is standing permission to write one
# back. Each half is checked by injecting the violation and reading the exit
# code and the diagnostic, since a gate whose pass is not the absence of a
# violation has a bug. The injections land in a scratch copy of the working
# tree, so the tree itself is never written.
# Non-zero exit: the gate passed over an unrecorded hint or a stale row,
# refused the tracked tree, or refused without naming what it refused.
# Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
module=tools/_resources.py
probe=probes/cpp_mull.yml--the-test-double-is-held-out.sh
record=docs/PYTHON_IMPRECISE_HINTS.yaml
for file in "$module" "$probe" "$record"; do [ -f "$file" ] || exit 2; done

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
	git -C "$tree" apply --index --allow-empty || exit 2
lens() { (cd "$tree" && "$py" -m tools.check_precise_hints); }
cp "$tree/$module" "$work/module" || exit 2
cp "$tree/$probe" "$work/probe" || exit 2

if ! lens > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# One fault per injection, appended to a module; the diagnostic must print the
# row the record would carry, whose text is the hint's own, since a fault's
# description can hold the same words.
refused() {
	if lens > "$work/forward.txt" 2>&1; then
		echo "the gate passed over $1"
		return 1
	fi
	if ! grep -qF -- "text: \"$2\"" "$work/forward.txt"; then
		echo "the gate refused $1 without printing the row for $2:"
		head -4 "$work/forward.txt" | sed 's/^/  /'
		return 1
	fi
	cp "$work/module" "$tree/$module"
	cp "$work/probe" "$tree/$probe"
}

inject() { printf '\n%s\n' "$1" >> "$tree/$module"; refused "$2" "$3"; }

inject 'def aletheia_probe(value: object) -> None: ...' "an object parameter" "object" || exit 1
inject 'aletheia_probe: list[float] = []' "a list of floats" "list[float]" || exit 1
inject 'def aletheia_probe() -> dict[str, Cpu]: ...' "a str key" "dict[str, Cpu]" || exit 1
inject 'aletheia_probe: list[dict[Cpu, list[Cpu]]] = []' "three nested subscripts" \
	"list[dict[Cpu, list[Cpu]]]" || exit 1
inject 'type AletheiaProbe = tuple[int, int]' "an alias over ints" \
	"type AletheiaProbe = tuple[int, int]" || exit 1

# A hint in the Python a probe hands its interpreter.
sed -i 's/^from tools.mutation_cpp_dry_run import MULL_RUNNER, dry_run_report, lane_binary$/&\ndef aletheia_probe(cpus: set[int]) -> None: ...\n/' "$tree/$probe"
grep -q '^def aletheia_probe' "$tree/$probe" || { echo "the probe fixture did not land"; exit 2; }
refused "a hint inside a probe's Python" "set[int]" || exit 1

# Reverse: a row whose hint the tree does not hold.
cat >> "$tree/$record" << 'YAML'
  - file: tools/_resources.py
    text: "dict[aletheia_probe, int]"
    count: 1
YAML
if lens > "$work/reverse.txt" 2>&1; then
	echo "the gate passed over a row naming a hint the tree does not hold"
	exit 1
fi
if ! grep -qF "dict[aletheia_probe, int]" "$work/reverse.txt"; then
	echo "the gate refused a stale row without printing it:"
	head -4 "$work/reverse.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: object, a primitive in a container and as a key, three nested subscripts, an alias and a probe's hint each fail the gate by name, and so does a stale row"
