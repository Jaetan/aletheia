#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_test_determinism.py.
# Claim: the ratchet fires in both directions, in every binding. A test that
# reads physical time or starts a thread fails the gate when the record does not
# name it: a Go timer and goroutine, a Python sleep and thread, a C++ sleep and
# std::thread, a Rust sleep inside a test module. A row naming more sites than
# its file holds fails too, since it is standing permission to bring one back.
# Each half is checked by injecting the violation and reading the exit code and
# the diagnostic, since a gate whose pass is not the absence of a violation has
# a bug. The injections land in a scratch copy of the working tree, so the tree
# itself is never written.
# Non-zero exit: the gate passed over an unrecorded site or a stale row,
# refused the tracked tree, or refused without naming what it refused.
# Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
record=docs/TEST_DETERMINISM.yaml
go_test=go/aletheia/types_test.go
py_test=python/tests/test_types_serialization.py
cpp_test=cpp/tests/unit_tests_validation.cpp
rust_src=rust/src/types.rs
for file in "$record" "$go_test" "$py_test" "$cpp_test" "$rust_src"; do [ -f "$file" ] || exit 2; done

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
	git -C "$tree" apply --index --allow-empty || exit 2
lens() { (cd "$tree" && "$py" -m tools.check_test_determinism); }

if ! lens > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# One site per injection, appended to a test file and taken out again after;
# the diagnostic must name the file and the primitive's label.
refused() {
	local file=$1 code=$2 label=$3
	cp "$tree/$file" "$work/saved"
	printf '\n%s\n' "$code" >> "$tree/$file"
	if lens > "$work/forward.txt" 2>&1; then
		echo "the gate passed over $label in $file"
		return 1
	fi
	if ! grep -qF -- "$file" "$work/forward.txt" || ! grep -qF -- "text: \"$label\"" "$work/forward.txt"; then
		echo "the gate refused $file without printing the row for $label:"
		head -4 "$work/forward.txt" | sed 's/^/  /'
		return 1
	fi
	cp "$work/saved" "$tree/$file"
}

refused "$go_test" 'func aletheiaProbe() { time.Sleep(1) }' "time: a clock or timer from package time" || exit 1
refused "$go_test" 'func aletheiaProbe() { go aletheiaProbe() }' "thread: a go statement" || exit 1
refused "$py_test" 'time.sleep(1)' "time: a clock or sleep from module time" || exit 1
refused "$py_test" 'threading.Thread(target=print)' "thread: a thread or timer from module threading" || exit 1
refused "$cpp_test" 'static void aletheia_probe() { std::this_thread::sleep_for(d); }' "time: a sleep" || exit 1
refused "$cpp_test" 'static void aletheia_probe() { std::thread t([] {}); }' "thread: a std::thread or std::jthread" || exit 1
refused "$rust_src" '#[cfg(test)] mod aletheia_probe { fn t() { std::thread::sleep(d); } }' "time: a sleep" || exit 1

# Reverse: a row naming a site the tree does not hold. An empty record is
# spelled as an empty list, which takes rows only once it is a block list.
sed -i 's/^sites: \[\]$/sites:/' "$tree/$record"
cat >> "$tree/$record" << 'YAML'
  - file: go/aletheia/types_test.go
    text: "thread: a go statement"
    count: 1
YAML
if lens > "$work/reverse.txt" 2>&1; then
	echo "the gate passed over a row naming a site the tree does not hold"
	exit 1
fi
if ! grep -qF "a recorded row names more sites than the file holds" "$work/reverse.txt"; then
	echo "the gate refused a stale row without saying so:"
	head -4 "$work/reverse.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a timer and a thread in a Go, a Python, a C++ and a Rust test each fail the gate by name, and so does a stale row"
