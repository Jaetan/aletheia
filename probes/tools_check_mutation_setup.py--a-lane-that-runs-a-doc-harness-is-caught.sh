#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_mutation_setup.py.
# Claim: the gate refuses, by binding, a mutation lane whose per-mutant run
# reaches its doc-example harness, a lane whose skip drops a test that is not
# the harness, and a harness renamed out from under the check; and it passes a
# comment that merely names the harness. Each arm is one edit, made in a
# scratch copy of the working tree and undone before the next, so the tree
# itself is never written.
# Python: --markdown-docs among mutmut's pytest arguments or the project's
# addopts, and the run-ci step spelling the option another way. Go: the
# runner's GOFLAGS with no -skip, with a -skip matching nothing, and with one
# that also matches the harness's fixture test, and the harness renamed. Rust:
# the skip dropped, the skip handed to cargo rather than to the test binaries,
# a filter that matches every test sharing its prefix, and the harness
# renamed. C++: the harness's source folded into the binary the Mull runner
# runs, and the harness's source moved.
# Non-zero exit: the gate refused the tracked tree or the comment, passed over
# an arm, or refused one without the diagnostic that names it. Exits 2 without
# the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands. It lands in the index too,
# which is what each arm is restored from.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
	git -C "$tree" apply --index --allow-empty || exit 2
lens() { (cd "$tree" && "$py" -m tools.check_mutation_setup); }

if ! lens > "$work/out.txt" 2>&1; then
	echo "the gate refuses the tracked tree:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi

# Replace one string of one file of the copy, refusing an edit that matches
# anything but exactly once, so an arm can never pass on an edit that missed.
edit() {
	"$py" - "$tree/$1" "$2" "$3" << 'PY'
import sys
from pathlib import Path

path, old, new = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text(encoding="utf-8")
if text.count(old) != 1:
    print(f"the edit's anchor occurs {text.count(old)} times in {path.name}, not once: {old!r}")
    raise SystemExit(1)
path.write_text(text.replace(old, new), encoding="utf-8")
PY
}

# One arm: the edit, the gate's refusal naming the expected diagnostic, and the
# file restored from the copy's index.
arm() {
	edit "$1" "$2" "$3" || return 1
	if lens > "$work/arm.txt" 2>&1; then
		echo "the gate passed over: $4"
		return 1
	fi
	if ! grep -qF -- "$5" "$work/arm.txt"; then
		echo "the gate refused ($4) without saying: $5"
		head -4 "$work/arm.txt" | sed 's/^/  /'
		return 1
	fi
	git -C "$tree" checkout -q -- "$1" || return 1
}

harness=every_rust_fence_of_the_listed_documents_builds_and_runs
skip='f"{caller} -count=1 -skip=^{GO_DOC_HARNESS}$"'

arm python/pyproject.toml 'pytest_add_cli_args = [' 'pytest_add_cli_args = ["--markdown-docs",' \
	"mutmut's own arguments collect the fences" \
	"[python/doc-harness] mutmut runs pytest with --markdown-docs" || exit 1
arm python/pyproject.toml 'addopts = ["-ra",' 'addopts = ["--markdown-docs", "-ra",' \
	"the project's addopts collect the fences" \
	"[python/doc-harness] mutmut runs pytest with --markdown-docs" || exit 1
arm tools/_ci_steps.py '"--markdown-docs",' '"--markdown-fences",' \
	"the harness option spelled another way" \
	"[python/doc-harness] tools/_ci_steps.py passes no --markdown-docs" || exit 1

arm tools/mutation_run.py "$skip" 'f"{caller} -count=1"' \
	"GOFLAGS with no -skip" \
	"[go/doc-harness] the GOFLAGS the runner gives gremlins carry no -skip" || exit 1
arm tools/mutation_run.py "$skip" 'f"{caller} -count=1 -skip=^TestDocFences$"' \
	"a -skip matching no test" \
	"[go/doc-harness] every mutant's run reaches TestDocExamples" || exit 1
arm tools/mutation_run.py "$skip" 'f"{caller} -count=1 -skip=^{GO_DOC_HARNESS}"' \
	"a -skip matching the fixture test too" \
	"[go/doc-harness] the lane's skip also drops TestDocExamplesFixture_ChecksYAMLLoads" || exit 1
arm go/aletheia/doc_examples_test.go 'func TestDocExamples(t *testing.T)' 'func TestDocFences(t *testing.T)' \
	"the Go harness renamed" \
	"[go/doc-harness] TestDocExamples is defined 0 times" || exit 1

arm rust/.cargo/mutants.toml "[\"--\", \"--skip\", \"$harness\"]" '["--"]' \
	"no --skip" \
	"[rust/doc-harness] every mutant's run reaches $harness" || exit 1
arm rust/.cargo/mutants.toml "[\"--\", \"--skip\", \"$harness\"]" "[\"--skip\", \"$harness\"]" \
	"--skip handed to cargo rather than the test binaries" \
	"[rust/doc-harness] every mutant's run reaches $harness" || exit 1
arm rust/.cargo/mutants.toml "\"$harness\"]" '"every_"]' \
	"a filter matching every test sharing its prefix" \
	"[rust/doc-harness] the lane's skip also drops every_listed_document_is_tracked_and_carries_a_rust_fence" || exit 1
arm rust/tests/doc_examples.rs "fn $harness()" 'fn every_rust_fence_runs()' \
	"the Rust harness renamed" \
	"[rust/doc-harness] $harness is defined 0 times" || exit 1

arm cpp/CMakeLists.txt 'add_executable(doc_example_tests tests/doc_example_tests.cpp)' \
	'add_executable(doc_example_tests tests/doc_example_tests.cpp)
target_sources(unit_tests PRIVATE tests/doc_example_tests.cpp)' \
	"the harness folded into the swept binary" \
	"[cpp/doc-harness] unit_tests, the binary the Mull runner runs once per mutant, compiles tests/doc_example_tests.cpp" || exit 1
arm cpp/CMakeLists.txt 'add_executable(doc_example_tests tests/doc_example_tests.cpp)' \
	'add_executable(doc_example_tests tests/doc_fences.cpp)' \
	"the C++ harness moved" \
	"[cpp/doc-harness] no target of cpp/CMakeLists.txt compiles tests/doc_example_tests.cpp" || exit 1

# A comment is not a command: naming the harness there is no fold.
edit cpp/CMakeLists.txt 'add_executable(doc_example_tests tests/doc_example_tests.cpp)' \
	'add_executable(doc_example_tests tests/doc_example_tests.cpp)
# target_sources(unit_tests PRIVATE tests/doc_example_tests.cpp)' || exit 1
if ! lens > "$work/out.txt" 2>&1; then
	echo "the gate refuses a comment naming the harness:"
	head -4 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: every arm of every binding fails the gate by name, and a comment does not"
