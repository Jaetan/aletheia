#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_mutation_setup.py.
# Claim: the gate fires when a hot-path source named in docs/MUTATION_BENCH.yaml
# is not where the file says. That list is the mutation lane's own idea of what
# is worth mutating, and a file renamed or split out from under it silently
# shrinks the lane; only this gate reads the two against each other.
# The rename lands in a scratch copy of the working tree, so the tree itself is
# never written: a sweep, a hook or a commit reading it meanwhile would take the
# rename for the user's change.
# Non-zero exit: the gate passed over a path that names nothing, or refused the
# tracked file. Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2

if ! "$py" -m tools.check_mutation_setup > /dev/null 2>&1; then
	echo "the gate refuses the tracked file:"
	"$py" -m tools.check_mutation_setup 2>&1 | head -3 | sed 's/^/  /'
	exit 1
fi

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
    git -C "$tree" apply --index --allow-empty || exit 2
record=$tree/docs/MUTATION_BENCH.yaml

sed -i 's|^      - go/aletheia/client.go$|      - go/aletheia/moved_away.go|' "$record"
if ! grep -q "moved_away.go" "$record"; then
	echo "the line the probe renames is not where it looked for it"
	exit 1
fi
if (cd "$tree" && "$py" -m tools.check_mutation_setup) > "$work/out.txt" 2>&1; then
	echo "the gate passed over a hot-path source that is not there"
	exit 1
fi
if ! grep -q "moved_away.go" "$work/out.txt"; then
	echo "the gate failed without naming the path:"
	head -3 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a hot-path source that is not where the file says fails the gate by name"
