#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_mutation_setup.py.
# Claim: the gate fires when docs/MUTATION_BENCH.yaml has no block for a binding
# the runner sweeps, and when it has a block for one the runner does not.  A
# binding with no block is a lane whose first run reports first_run and gates
# nothing, which is what a fourth binding looked like until its block landed;
# a block for no binding is a record nothing reads.
# The edit lands in a scratch copy of the working tree, so the tree itself is
# never written.
# Non-zero exit: the gate passed over a missing or an unread block, or refused
# the tracked file. Exits 2 without the virtual environment.
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
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
	git -C "$tree" apply --index --allow-empty || exit 2
record=$tree/docs/MUTATION_BENCH.yaml

# The Rust block renamed to a binding no runner has: one block missing, one unread.
sed -i 's|^  rust:$|  haskell:|' "$record"
if ! grep -q "^  haskell:$" "$record"; then
	echo "the block the probe renames is not where it looked for it"
	exit 1
fi
if (cd "$tree" && "$py" -m tools.check_mutation_setup) > "$work/out.txt" 2>&1; then
	echo "the gate passed with the Rust block renamed away"
	exit 1
fi
for want in "no block for rust" "haskell.*no such binding"; do
	if ! grep -Eq "$want" "$work/out.txt"; then
		echo "the gate failed without saying '$want':"
		head -4 "$work/out.txt" | sed 's/^/  /'
		exit 1
	fi
done
echo "PASS: a binding without a block, and a block without a binding, each fail the gate by name"
