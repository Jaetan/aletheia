#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_mutation_setup.py.
# Claim: the gate fires when a hot-path source named in docs/MUTATION_BENCH.yaml
# is not where the file says. That list is the mutation lane's own idea of what
# is worth mutating, and a file renamed or split out from under it silently
# shrinks the lane; only this gate reads the two against each other.
# The check runs against a copy, so the tracked file is not touched.
# Non-zero exit: the gate passed over a path that names nothing, or refused the
# tracked file. Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

if ! "$py" -m tools.check_mutation_setup > /dev/null 2>&1; then
	echo "the gate refuses the tracked file:"
	"$py" -m tools.check_mutation_setup 2>&1 | head -3 | sed 's/^/  /'
	exit 1
fi

work=$(mktemp -d) || exit 2
trap 'cp "$work/MUTATION_BENCH.yaml" docs/MUTATION_BENCH.yaml 2> /dev/null; rm -rf "$work"' EXIT
cp docs/MUTATION_BENCH.yaml "$work/MUTATION_BENCH.yaml"

sed -i 's|^      - go/aletheia/client.go$|      - go/aletheia/moved_away.go|' docs/MUTATION_BENCH.yaml
if ! grep -q "moved_away.go" docs/MUTATION_BENCH.yaml; then
	echo "the line the probe renames is not where it looked for it"
	exit 1
fi
if "$py" -m tools.check_mutation_setup > "$work/out.txt" 2>&1; then
	echo "the gate passed over a hot-path source that is not there"
	exit 1
fi
if ! grep -q "moved_away.go" "$work/out.txt"; then
	echo "the gate failed without naming the path:"
	head -3 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
cp "$work/MUTATION_BENCH.yaml" docs/MUTATION_BENCH.yaml
echo "PASS: a hot-path source that is not where the file says fails the gate by name"
