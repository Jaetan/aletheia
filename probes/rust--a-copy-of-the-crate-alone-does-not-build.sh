#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes rust/ against rust/.cargo/mutants.toml and tools/mutation_rust.py.
# Claim: the crate's tests cannot be built from a copy of the crate alone,
# which is why the mutation lane sweeps in place.  The suite includes the DBC
# corpus and the parity snapshots under python/ at compile time, so a copy
# that does not carry the repository around it fails to compile its tests.
# A copy that builds would mean the reason for the in-place sweep is gone and
# the lane could run in copies again, in parallel; this probe is what says so.
# Non-zero exit: the copied crate's tests built, or failed for another reason.
# Exits 2 without cargo.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v cargo > /dev/null || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd rust && git ls-files -z . | grep -zv '^excel/' | xargs -0 -I{} cp --parents {} "$work/") || exit 2
if (cd "$work" && cargo test --no-run --all-features) > "$work/build.txt" 2>&1; then
	echo "the copied crate's tests built, so the lane no longer has to sweep in place"
	exit 1
fi
if ! grep -q "couldn't read .*python/tests/fixtures" "$work/build.txt"; then
	echo "the copied crate failed to build for another reason:"
	grep -m 3 "^error" "$work/build.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a copy of the crate alone does not build its tests, for want of the fixtures above it"
