# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Static mutation-setup coverage gate.

Always-on invariants, checked without running the mutation tools (which take
30 min - 2 hours wall):

1. **Hot-path sources exist.** Parses ``docs/MUTATION_BENCH.yaml`` and verifies,
   for every binding, that the declared hot-path source files exist on disk —
   catches silent removal or rename of a hot-path file.

2. **Tools-importing tests are excluded from the Python mutmut lane.** Every
   ``python/tests/test_*.py`` that imports the repo-root ``tools`` package must
   appear as ``--ignore=tests/<name>.py`` (full filename, extension included) in
   ``[tool.mutmut].pytest_add_cli_args``.
   Such a test ModuleNotFound-aborts pytest collection inside mutmut's relocated
   ``mutants/`` work-tree (which has no ``tools``), which kills the baseline
   stats phase -> *zero* mutants run -> the (advisory) lane silently goes red.
   This gate is in the REQUIRED sweep, so it surfaces the drift at PR time.
   (Reproduced 2026-06-20: ``tests/test_check_changelog.py`` landed in #51
   importing ``tools`` without an ignore, crashing the lane unnoticed for days.)

3. **A test that reads the tree above ``python/`` either skips or is excluded.**
   mutmut copies ``python/`` alone into ``mutants/``, so a test resolving
   ``Path(__file__).resolve().parents[2]`` lands on ``python/`` there rather
   than on the repository root, and every path it builds is absent.  A test
   that answers that by skipping is fine wherever it runs; one that asserts
   fails the baseline instead, which is the same zero-mutant outcome as an
   aborted collection, so it must carry an ``--ignore=`` too.
   (Reproduced 2026-09-20: ``tests/test_doc_only_path_exemption.py`` read
   ``.github/workflows`` through ``parents[2]``, found nothing under
   ``mutants/`` and failed the lane on its own assertion.)

4. **The record has one block per binding the runner drives, and no other.**
   A binding the runner can sweep with no block is a lane with no baseline,
   whose first run reports ``first_run`` and gates nothing; a block for a
   binding the runner does not know is a record nothing reads.

5. **Every ledger row still names a line of the tree.** The survivors, the
   unobserved kills and the Go lane's not-covered mutants are each recorded by
   mutator, file and the text of the
   source line, keyed on that text rather than on the line's number so that an
   edit above the site does not move a row and an edit of the site does.  What
   moves one, then, is a rename or a rewording, which nothing else notices: the
   sweep would, half an hour later and only on the lane.  Each row's file is
   read here for its text.

6. **No lane's per-mutant run reaches its binding's doc-example harness.**
   A harness builds and runs every fence of the documents as a program of
   its own, holding the documents to the binding; the unit tests hold the
   binding's behaviour.  Run per mutant it costs its whole run each time, and
   the Rust sweep with it and without it gave the same verdict on every
   mutant.  Python's is the pytest option that collects the fences, absent
   from what mutmut runs; Go's and Rust's are one test each, which the lane
   skips by name, and the skip must reach that test and no other; C++'s is its
   own binary's source, which the binary the Mull runner runs must not
   compile.  Each harness is first found where it is defined, so a rename is a
   failure here rather than a check that names nothing.

The dynamic counterpart is ``tools/mutation_run.py``, which actually drives
each binding's mutation tool against this list and writes per-binding
survivor counts.

Usage:
  python3 tools/check_mutation_setup.py

Exits 0 if every invariant holds, 1 otherwise (with a precise diagnostic naming
the offending entries).

Forward-revert verified 2026-05-09 (invariant 1): rename one hot-path entry in
the YAML to a non-existent path -> this gate fires; restore the path -> exit 0.
Forward-revert verified 2026-06-20 (invariant 2): drop the
``test_check_changelog.py`` ignore -> this gate fires; restore it -> exit 0.
Forward-revert verified 2026-09-26 (invariant 4): rename the Rust block to a
binding no runner has -> this gate fires twice, by name; restore it -> exit 0
(``probes/tools_check_mutation_setup.py--a-binding-without-a-block-is-caught.sh``).
Forward-revert verified 2026-10-01 (invariant 6): each lane in turn made to
reach its harness, to skip another test beside it, or to name a harness
renamed away -> this gate fires, by binding; restore it -> exit 0
(``probes/tools_check_mutation_setup.py--a-lane-that-runs-a-doc-harness-is-caught.sh``).
"""

from __future__ import annotations

import collections
import re
import sys
import tomllib
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NewType, TypedDict, cast

import yaml

from tools._common import RelPath, emit
from tools.mutation_cpp import CPP_TEST_TARGET
from tools.mutation_cpp_legs import CppTree
from tools.mutation_cpp_slices import partition, slice_domain
from tools.mutation_run import GO_DOC_HARNESS, RUNNERS, GoFlags, go_sweep_goflags

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from tools.mutation_cpp_legs import CppTreeName
    from tools.mutation_cpp_slices import TreeRuns

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"
PYPROJECT_PATH = REPO_ROOT / "python" / "pyproject.toml"
PY_TESTS_DIR = REPO_ROOT / "python" / "tests"

# A column-0 (top-level) ``import tools`` / ``from tools ...`` — the only form
# that runs, and aborts collection, at pytest import time.  An INDENTED import
# (inside a function, an ``if TYPE_CHECKING:`` block, or a ``try/except
# ImportError`` guard) is deliberately NOT matched: it either does not execute
# during collection or is guarded, so it does not crash the mutmut baseline —
# matching it would be a false positive.  (A transitive import via a helper is
# also not caught; it likewise does not abort collection at the test module.)
_TOOLS_IMPORT_RE = re.compile(r"^(?:from|import)[ \t]+tools(?:\.|[ \t]|$)", re.MULTILINE)
# An ``--ignore=tests/<name>.py`` entry in the mutmut pytest args.
_IGNORE_ARG_RE = re.compile(r"^--ignore=(tests/[\w./-]+\.py)$")
# A path built above ``python/``: ``parents[2]`` and up from a file in
# ``python/tests/``, or a literal walk up two levels.  Under ``mutants/`` the
# same expression stops at ``python/``, so whatever it names is not there.
_ABOVE_TREE_RE = re.compile(r"parents\[[2-9]\]|\.\./\.\./")
# What lets a test answer an absent path by saying nothing rather than failing.
_SKIPS_RE = re.compile(r"pytest\.skip|skipif|importorskip")


def _load_bindings() -> dict[str, object]:
    """Load and validate ``SPEC_PATH``, returning its ``bindings`` mapping.

    Exits 2 with a precise stderr diagnostic if the spec is missing,
    malformed, or its ``bindings`` entry is not a mapping.
    """
    if not SPEC_PATH.is_file():
        _ = sys.stderr.write(f"ERROR: spec missing at {SPEC_PATH}\n")
        sys.exit(2)
    spec: object = yaml.safe_load(SPEC_PATH.read_text())
    if not isinstance(spec, dict) or "bindings" not in spec:
        _ = sys.stderr.write(f"ERROR: malformed spec at {SPEC_PATH}\n")
        sys.exit(2)
    bindings = cast("dict[str, object]", spec)["bindings"]
    if not isinstance(bindings, dict):
        _ = sys.stderr.write("ERROR: spec.bindings must be a mapping\n")
        sys.exit(2)
    return cast("dict[str, object]", bindings)


def _collect_failures(bindings: dict[str, object]) -> list[str]:
    """Return one diagnostic per spec defect across every binding entry."""
    failures: list[str] = []
    for binding_name, binding_spec in bindings.items():
        if not isinstance(binding_spec, dict):
            failures.append(
                f"[{binding_name}] binding spec must be a mapping",
            )
            continue
        spec = cast("dict[str, object]", binding_spec)
        tool = spec.get("tool")
        if not isinstance(tool, str) or not tool:
            failures.append(
                f"[{binding_name}] missing 'tool' field in spec",
            )
        hot_path = spec.get("hot_path", [])
        if not isinstance(hot_path, list) or not hot_path:
            failures.append(
                f"[{binding_name}] missing or empty 'hot_path' field",
            )
            continue
        for rel in cast("list[object]", hot_path):
            if not isinstance(rel, str):
                continue
            full = REPO_ROOT / rel
            if not full.is_file():
                failures.append(
                    f"[{binding_name}] hot-path source does not exist: {rel}",
                )
    return failures


def _mutmut_ignored_tests() -> set[str]:
    """Return the ``tests/<name>.py`` files excluded via ``--ignore`` in [tool.mutmut].

    Exits 2 if pyproject.toml is missing or its ``[tool.mutmut]`` section absent —
    those would silently make the invariant-2 check vacuous.
    """
    if not PYPROJECT_PATH.is_file():
        _ = sys.stderr.write(f"ERROR: pyproject.toml missing at {PYPROJECT_PATH}\n")
        sys.exit(2)
    data = tomllib.loads(PYPROJECT_PATH.read_text())
    mutmut = data.get("tool", {}).get("mutmut")
    if not isinstance(mutmut, dict):
        _ = sys.stderr.write(f"ERROR: no [tool.mutmut] section in {PYPROJECT_PATH}\n")
        sys.exit(2)
    args = cast("dict[str, object]", mutmut).get("pytest_add_cli_args", [])
    ignored: set[str] = set()
    if isinstance(args, list):
        for arg in cast("list[object]", args):
            if isinstance(arg, str):
                match = _IGNORE_ARG_RE.match(arg)
                if match:
                    ignored.add(match.group(1))
    return ignored


def _tools_importing_tests_unignored() -> list[str]:
    """One diagnostic per ``tools``-importing test missing from the mutmut ignore list.

    Exits 2 if ``python/tests/`` is absent — returning ``[]`` there would make
    invariant 2 silently vacuous (the gate passes despite being unable to
    enforce the rule), mirroring the missing-pyproject / missing-[tool.mutmut]
    hard failures in ``_mutmut_ignored_tests``.
    """
    if not PY_TESTS_DIR.is_dir():
        _ = sys.stderr.write(f"ERROR: python tests dir missing at {PY_TESTS_DIR}\n")
        sys.exit(2)
    ignored = _mutmut_ignored_tests()
    failures: list[str] = []
    for path in sorted(PY_TESTS_DIR.glob("test_*.py")):
        if _TOOLS_IMPORT_RE.search(path.read_text(encoding="utf-8")):
            rel = f"tests/{path.name}"
            if rel not in ignored:
                failures.append(
                    f"[python/mutmut] {rel} imports the repo-root `tools` package but is "
                    + f"not excluded — add `--ignore={rel}` to [tool.mutmut].pytest_add_cli_args "
                    + "(else it aborts mutmut's baseline collection in mutants/ -> zero mutants)",
                )
    return failures


def _above_tree_tests_unignored() -> list[str]:
    """One diagnostic per test that reads above ``python/``, cannot skip, and is not ignored.

    The three properties are one finding together: reaching above the copied
    tree is ordinary, and several tests do it and skip when what they wanted is
    absent; it is the test that asserts on what it found there that fails
    mutmut's baseline and leaves the lane with no mutants at all.
    """
    ignored = _mutmut_ignored_tests()
    failures: list[str] = []
    for path in sorted(PY_TESTS_DIR.glob("test_*.py")):
        source = path.read_text(encoding="utf-8")
        if not _ABOVE_TREE_RE.search(source) or _SKIPS_RE.search(source):
            continue
        rel = f"tests/{path.name}"
        if rel not in ignored:
            failures.append(
                f"[python/mutmut] {rel} reads the tree above python/ and cannot skip, but "
                + f"is not excluded — add `--ignore={rel}` to [tool.mutmut].pytest_add_cli_args, "
                + "or make it skip when the path is absent (under mutants/ it is)",
            )
    return failures


def cpp_slice_weights_are_of_the_domain(bindings: dict[str, object]) -> list[str]:
    """Hold each tree's recorded weights to the files a slice can actually claim.

    Every tree is cut on weights of its own, so a tree with none is refused:
    its slices would be cut on nothing, every file weighing the same.  The
    slices are cut over every tracked file of the library, so no file can be
    left out of them; what can go wrong is the other direction, a recorded
    weight for a file that has been renamed or held out, which silently stops
    counting toward the balance.  The partition itself is checked here too:
    the whole domain, once each, which is the property every other refusal in
    the lane is written against.
    """
    spec = cast("dict[str, object]", bindings.get("cpp", {}))
    baseline = cast("dict[str, object]", spec.get("baseline", {}))
    by_tree = cast("dict[CppTreeName, TreeRuns]", baseline.get("runs_by_file", {}))
    domain = slice_domain(REPO_ROOT, REPO_ROOT / "cpp" / "mull.yml")
    failures = [
        f"[cpp/slices] runs_by_file names {name}, which is no tree the lane builds"
        for name in sorted(set(by_tree) - {tree.key for tree in CppTree})
    ]
    for tree in CppTree:
        recorded = by_tree.get(tree.key, {})
        if not recorded:
            failures.append(
                f"[cpp/slices] runs_by_file records nothing for the {tree.value} tree, so its "
                + "slices are cut on nothing: re-take it from a run's cpp-runs.json",
            )
            continue
        failures += [
            f"[cpp/slices] {path} carries a recorded weight in the {tree.value} tree and is "
            + "not a file a slice can claim: it is untracked, renamed, or held out by "
            + "cpp/mull.yml, so its weight counts toward no slice"
            for path in sorted(set(recorded) - set(domain))
        ]
        claimed = [path for claims in partition(domain, recorded) for path in claims]
        if sorted(claimed) != sorted(domain):
            failures.append(
                f"[cpp/slices] the {tree.value} tree's partition claims {len(claimed)} of the "
                + f"domain's {len(domain)} files; a file in no slice is mutated by every "
                + "slice, and one in two is swept twice",
            )
    return failures


def every_runner_has_a_block(bindings: dict[str, object]) -> list[str]:
    """Hold the record to one block per binding the runner drives, and no other."""
    known = {name for name, _skip_var, _runner in RUNNERS}
    return [
        f"[bindings] no block for {name}, which the runner sweeps: its first run would "
        + "report first_run and gate nothing"
        for name in sorted(known - set(bindings))
    ] + [
        f"[bindings/{name}] the runner has no such binding, so nothing reads this block"
        for name in sorted(set(bindings) - known)
    ]


def ledger_rows_still_name_their_line(bindings: dict[str, object]) -> list[str]:
    """Hold every recorded ledger row to a file and a line the tree still has.

    Every ledger keys a row on the text of its source line rather than on the
    line's number, so that an edit above the site does not move it and an edit
    of the site does.  What moves it, then, is exactly what nothing else
    notices: the line is reworded, or its file is renamed, and the row goes on
    claiming something about a line that is gone.  The sweep would say so, but
    only after half an hour, and only on the lane; this says so in the
    always-on gate, reading the recorded file for the recorded text.  A row
    whose count exceeds the times the text occurs is not a defect: several
    mutants of one line share it, and the tree does not say how many.
    """
    failures: list[str] = []
    for binding_name, binding_spec in bindings.items():
        if not isinstance(binding_spec, dict):
            continue
        spec = cast("dict[str, object]", binding_spec)
        baseline = cast("dict[str, object]", spec.get("baseline", {}))
        for name in ("survivors_ledger", "unobserved_ledger", "not_covered_ledger"):
            rows = baseline.get(name, [])
            if not isinstance(rows, list):
                failures.append(f"[{binding_name}/{name}] must be a list of rows")
                continue
            for row in cast("list[object]", rows):
                if not isinstance(row, dict):
                    failures.append(f"[{binding_name}/{name}] every row must be a mapping")
                    continue
                failures += _row_names_its_line(binding_name, name, cast("dict[str, object]", row))
    return failures


def _row_names_its_line(binding_name: str, ledger: str, row: dict[str, object]) -> list[str]:
    """Say why one ledger row no longer names a line of the tree, or nothing."""
    file, text = row.get("file"), row.get("text")
    if not isinstance(file, str) or not isinstance(text, str):
        return [f"[{binding_name}/{ledger}] a row must carry a 'file' and a 'text'"]
    source = REPO_ROOT / file
    if not source.is_file():
        return [
            f"[{binding_name}/{ledger}] {file} is not a file of the tree: the row records a "
            + "line of a source that was renamed or removed, and nothing else reads it",
        ]
    if not any(line.strip() == text for line in source.read_text(encoding="utf-8").split("\n")):
        return [
            f"[{binding_name}/{ledger}] {file} holds no line reading {text!r}: the row was "
            + "recorded against a line the tree has since reworded, so re-take the ledger "
            + "from a sweep or delete the row with the change that made it stale",
        ]
    return []


# One argument of a command line the lane runs its tests with.
PytestArg = NewType("PytestArg", str)
CargoTestArg = NewType("CargoTestArg", str)
# A test as its runner selects it by name.
TestName = NewType("TestName", str)

# Each binding's doc-example harness, as the lane that must not run it would
# name it; Go's is the runner's own ``GO_DOC_HARNESS``.
PYTHON_DOC_HARNESS = PytestArg("--markdown-docs")
RUST_DOC_HARNESS = TestName("every_rust_fence_of_the_listed_documents_builds_and_runs")
CPP_DOC_HARNESS = "tests/doc_example_tests.cpp"

MUTANTS_TOML_PATH = REPO_ROOT / "rust" / ".cargo" / "mutants.toml"
CMAKE_PATH = REPO_ROOT / "cpp" / "CMakeLists.txt"

# A Go test: a top-level function the go command runs, TestMain excluded by its signature.
_GO_TEST_RE = re.compile(r"^func (Test\w*)\(\w+ \*testing\.T\)", re.MULTILINE)
# The pattern of a ``-skip`` flag in GOFLAGS.
_GO_SKIP_RE = re.compile(r"(?:^|\s)-skip=(\S+)")
# A Rust test: a function under ``#[test]``, whatever attributes follow it.
_RUST_TEST_RE = re.compile(r"#\[test\]\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?fn\s+(\w+)")
# A CMake command that names a target's sources.
_CMAKE_SOURCES_RE = re.compile(r"\b(?:add_executable|target_sources)\s*\(([^)]*)\)")


class _PytestIni(TypedDict, total=False):
    addopts: list[PytestArg]


class _PytestTool(TypedDict, total=False):
    ini_options: _PytestIni


class _MutmutTool(TypedDict, total=False):
    pytest_add_cli_args: list[PytestArg]
    pytest_add_cli_args_test_selection: list[PytestArg]


class _Tools(TypedDict, total=False):
    mutmut: _MutmutTool
    pytest: _PytestTool


class _Pyproject(TypedDict, total=False):
    tool: _Tools


class _MutantsToml(TypedDict, total=False):
    additional_cargo_test_args: list[CargoTestArg]


def no_lane_runs_a_doc_harness() -> list[Prose]:
    """Hold each lane's per-mutant run to its binding's tests less the doc-example harness."""
    return [
        *python_lane_runs_no_doc_harness(),
        *go_lane_runs_no_doc_harness(),
        *rust_lane_runs_no_doc_harness(),
        *cpp_lane_runs_no_doc_harness(),
    ]


def python_lane_runs_no_doc_harness() -> list[Prose]:
    """Refuse the fence-collecting option among the arguments mutmut runs pytest with.

    mutmut runs pytest with its own arguments and the project's ``addopts``;
    the harness is the run-ci step that passes the option, found there first.
    """
    steps = (REPO_ROOT / "tools" / "_ci_steps.py").read_text(encoding="utf-8")
    if f'"{PYTHON_DOC_HARNESS}"' not in steps:
        return [
            Prose(
                f"[python/doc-harness] tools/_ci_steps.py passes no {PYTHON_DOC_HARNESS}: the "
                + "harness is spelled another way now, and this check would name nothing"
            )
        ]
    tool = cast("_Pyproject", tomllib.loads(PYPROJECT_PATH.read_text(encoding="utf-8"))).get(
        "tool", {}
    )
    mutmut = tool.get("mutmut", {})
    runs = [
        *mutmut.get("pytest_add_cli_args", []),
        *mutmut.get("pytest_add_cli_args_test_selection", []),
        *tool.get("pytest", {}).get("ini_options", {}).get("addopts", []),
    ]
    if PYTHON_DOC_HARNESS in runs:
        return [
            Prose(
                f"[python/doc-harness] mutmut runs pytest with {PYTHON_DOC_HARNESS}, so every "
                + "mutant's run collects the documents' fences, which no mutant reaches"
            )
        ]
    return []


def go_lane_runs_no_doc_harness() -> list[Prose]:
    """Hold the Go lane's ``-skip`` to the doc-example harness and nothing else.

    The flag is read from the ``GOFLAGS`` the runner gives gremlins, the last
    ``-skip`` being the one go keeps, and matched as go matches a top-level
    test, unanchored; Python's ``re`` reads the pattern's anchors and word
    characters as RE2 does.
    """
    package = REPO_ROOT / "go" / "aletheia"
    names = [
        TestName(match.group(1))
        for path in sorted(package.glob("*_test.go"))
        for match in _GO_TEST_RE.finditer(path.read_text(encoding="utf-8"))
    ]
    skips = [match.group(1) for match in _GO_SKIP_RE.finditer(go_sweep_goflags(GoFlags("")))]
    if not skips:
        return [
            Prose(
                "[go/doc-harness] the GOFLAGS the runner gives gremlins carry no -skip, so "
                + f"every mutant's run reaches {GO_DOC_HARNESS}"
            )
        ]
    pattern = re.compile(skips[-1])
    skipped = [name for name in names if pattern.search(name)]
    return _skips_the_harness_alone("go", TestName(GO_DOC_HARNESS), names, skipped)


def rust_lane_runs_no_doc_harness() -> list[Prose]:
    """Hold the Rust lane's ``--skip`` filters to the doc-example harness and nothing else.

    cargo-mutants appends the configuration's test arguments to ``cargo
    test``, where those after ``--`` reach the test binaries; libtest skips a
    test whose name contains a filter, or equals it under ``--exact``.
    """
    config = cast("_MutantsToml", tomllib.loads(MUTANTS_TOML_PATH.read_text(encoding="utf-8")))
    args = config.get("additional_cargo_test_args", [])
    binary_args = args[args.index(CargoTestArg("--")) + 1 :] if "--" in args else []
    filters = [
        arg.removeprefix("--skip=")
        for i, arg in enumerate(binary_args)
        if arg.startswith("--skip=") or (i > 0 and binary_args[i - 1] == "--skip")
    ]
    exact = "--exact" in binary_args
    names = [
        TestName(match.group(1))
        for directory in ("src", "tests")
        for path in sorted((REPO_ROOT / "rust" / directory).rglob("*.rs"))
        for match in _RUST_TEST_RE.finditer(path.read_text(encoding="utf-8"))
    ]
    skipped = [name for name in names if any(name == f if exact else f in name for f in filters)]
    return _skips_the_harness_alone("rust", RUST_DOC_HARNESS, names, skipped)


def _skips_the_harness_alone(
    binding: Literal["go", "rust"],
    harness: TestName,
    names: list[TestName],
    skipped: list[TestName],
) -> list[Prose]:
    """Say why a lane's skip does not drop the harness alone from the tests it runs, or nothing."""
    defined = names.count(harness)
    if defined != 1:
        return [
            Prose(
                f"[{binding}/doc-harness] {harness} is defined {defined} times among the "
                + "binding's tests rather than once: the harness was renamed or duplicated, "
                + "and the lane's skip is checked against a name the tree does not settle"
            )
        ]
    failures: list[Prose] = []
    if harness not in skipped:
        failures.append(
            Prose(
                f"[{binding}/doc-harness] every mutant's run reaches {harness}: the lane's "
                + "skip does not match it"
            )
        )
    failures += [
        Prose(
            f"[{binding}/doc-harness] the lane's skip also drops {name}, which is not the "
            + "doc-example harness, so no mutant is tested against it"
        )
        for name in sorted(set(skipped) - {harness})
    ]
    return failures


def cpp_lane_runs_no_doc_harness() -> list[Prose]:
    """Refuse the doc-example harness's source among those of the binary the Mull runner runs.

    Every ``add_executable`` and ``target_sources`` of ``cpp/CMakeLists.txt``
    is read, comments dropped, so a source folded into the test binary under
    the mutation build counts as the unconditional ones do.
    """
    text = "\n".join(
        line.split("#", 1)[0] for line in CMAKE_PATH.read_text(encoding="utf-8").splitlines()
    )
    sources: dict[RelPath, list[RelPath]] = collections.defaultdict(list)
    for match in _CMAKE_SOURCES_RE.finditer(text):
        target, *rest = match.group(1).split()
        sources[RelPath(target)] += [RelPath(word) for word in rest]
    building = sorted(target for target, words in sources.items() if CPP_DOC_HARNESS in words)
    if not building:
        return [
            Prose(
                f"[cpp/doc-harness] no target of cpp/CMakeLists.txt compiles {CPP_DOC_HARNESS}: "
                + "the harness moved, and this check would name nothing"
            )
        ]
    if CPP_TEST_TARGET in building:
        return [
            Prose(
                f"[cpp/doc-harness] {CPP_TEST_TARGET}, the binary the Mull runner runs once per "
                + f"mutant, compiles {CPP_DOC_HARNESS}"
            )
        ]
    return []


def _ledger_rows(bindings: dict[str, object]) -> int:
    """Count the ledger rows the record carries, over every binding and every ledger."""
    total = 0
    for binding_spec in bindings.values():
        if not isinstance(binding_spec, dict):
            continue
        spec = cast("dict[str, object]", binding_spec)
        baseline = cast("dict[str, object]", spec.get("baseline", {}))
        for name in ("survivors_ledger", "unobserved_ledger", "not_covered_ledger"):
            rows = baseline.get(name, [])
            if isinstance(rows, list):
                total += len(cast("list[object]", rows))
    return total


def _total_hot_paths(bindings: dict[str, object]) -> int:
    """Return the total number of declared hot-path sources across bindings."""
    total = 0
    for binding_spec in bindings.values():
        if not isinstance(binding_spec, dict):
            continue
        hot_path = cast("dict[str, object]", binding_spec).get("hot_path", [])
        if isinstance(hot_path, list):
            total += len(cast("list[object]", hot_path))
    return total


def main() -> int:
    """Check hot paths exist, tools-tests are ignored, and the slices are of the tree."""
    bindings = _load_bindings()
    failures = _collect_failures(bindings)
    failures += _tools_importing_tests_unignored()
    failures += _above_tree_tests_unignored()
    failures += cpp_slice_weights_are_of_the_domain(bindings)
    failures += every_runner_has_a_block(bindings)
    failures += ledger_rows_still_name_their_line(bindings)
    failures += no_lane_runs_a_doc_harness()

    if failures:
        _ = sys.stderr.write("Mutation-setup coverage gate FAILED:\n")
        for failure in failures:
            _ = sys.stderr.write(f"  - {failure}\n")
        _ = sys.stderr.write(
            f"\n{len(failures)} issue(s) above.  For a missing hot-path source: "
            + f"restore it or update {SPEC_PATH.relative_to(REPO_ROOT)} to reflect "
            + "the rename (AGENTS.md cat 14(g) has the canonical lists).  For a "
            + "test that the mutated tree cannot satisfy: add its `--ignore=` to "
            + "[tool.mutmut], or let it skip.  For a doc-example harness a lane "
            + "reaches: skip it in that lane's per-mutant run, and it alone.\n",
        )
        return 1

    total = _total_hot_paths(bindings)
    emit(
        "Mutation-setup coverage gate OK: "
        + f"{len(bindings)} bindings, {total} hot-path sources all present; "
        + "every test the mutated tree cannot satisfy is mutmut-ignored; "
        + "every recorded C++ slice weight is a file the partition claims; "
        + "one block per binding the runner drives; "
        + f"each of {_ledger_rows(bindings)} ledger rows names a line the tree holds; "
        + "no lane's per-mutant run reaches its doc-example harness.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
