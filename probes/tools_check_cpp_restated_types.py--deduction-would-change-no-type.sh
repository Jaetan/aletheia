#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_cpp_restated_types.py.
# Claim: the lens reports a declaration only where `auto` would deduce the
# written type exactly, so acting on what it prints cannot change a type. Two
# shapes have to stay out, and both were reported once before the matcher was
# fixed, which is why they are pinned rather than argued:
#   a written type reached through a user-defined conversion. A proxy accessor
#   returns a proxy, and the declared type calls the proxy's conversion
#   operator, so the conversion's result carries the declared type while the
#   expression as written does not. Read through the compiler's rebuilt tree
#   the two look equal; `auto` deduces the proxy, and for a proxy bound to a
#   temporary the copy dangles;
#   a declaration that is already deduced under a pointer, `auto*` or
#   `auto const*`. Its type is a pointer to a deduced type rather than a
#   deduced type, so the plain exclusion does not see it and the lens would
#   report a declaration that has nothing to restate.
# A third shape is injected alongside them, a declaration that genuinely
# restates, so a lens that reported nothing at all could not pass this probe.
# The injection lands in a scratch copy of the working tree, with the compile
# database rewritten to it and the fetched dependencies shared read-only, so
# the tree itself is never written: a sweep, a hook or a commit reading it
# meanwhile would take the fixture for the user's change.
# Non-zero exit: the lens reported a conversion or an already-deduced pointer,
# or failed to report the one declaration that does restate.
# Exits 2 without the virtual environment or without the configured build tree.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
subject=cpp/src/enrich.cpp
[ -f "$subject" ] || exit 2
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

cat >> "$tree/$subject" << 'CPP'

namespace {
// Probe fixture, in a scratch copy of the tree.
struct AletheiaProbeProxy {
    // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
    operator std::string() const { return {}; }
};
AletheiaProbeProxy aletheia_probe_proxy();
std::string aletheia_probe_plain();
void aletheia_probe_uses() {
    const std::string through_conversion = aletheia_probe_proxy();
    auto* const already_deduced = std::addressof(through_conversion);
    const std::string genuinely_restated = aletheia_probe_plain();
    (void)already_deduced;
    (void)genuinely_restated;
}
} // namespace
CPP

lens > "$work/out.txt" 2>&1

# Whole declarations, not names: one fixture names another in its initializer.
check_absent() {
	if grep -qF "$1" "$work/out.txt"; then
		echo "the lens reported a declaration where auto deduces another type or none is written:"
		grep -m1 -F "$1" "$work/out.txt" | sed 's/^/  /'
		exit 1
	fi
}
check_absent "const std::string through_conversion = aletheia_probe_proxy()"
check_absent "auto* const already_deduced = std::addressof(through_conversion)"

if ! grep -qF "const std::string genuinely_restated = aletheia_probe_plain()" "$work/out.txt"; then
	echo "the lens did not report the declaration that does restate its type:"
	tail -2 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a user-defined conversion and an already-deduced pointer stay out, and a restatement is reported"
