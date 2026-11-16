# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Static mutation-setup coverage gate.

Always-on invariants, checked without running the mutation tools (which take
30 min - 2 hours wall):

1. **Hot-path sources exist.** Parses ``docs/MUTATION_BENCH.yaml`` and verifies,
   for every binding, that the declared hot-path source files exist on disk,
   which catches the silent removal or rename of a hot-path file.

2. **Tools-importing tests are excluded from the Python mutmut lane.** Every
   ``python/tests/test_*.py`` whose collection imports the repo-root ``tools``
   package, itself or through a helper module of ``python/tests/``, must
   appear as ``--ignore=tests/<name>.py`` (full filename, extension included)
   in ``[tool.mutmut].pytest_add_cli_args``, and ``python/tests/conftest.py``,
   which pytest imports for every test, must import it nowhere.
   Such a test holds the repository's tools, not the package's hot paths, and
   reads the tree above ``python/`` through them, which mutmut's relocated
   ``mutants/`` work-tree lacks (invariant 3); run per mutant it costs its
   whole run each time.  The conftest puts the repository root on the path, so
   the import itself resolves there too.

3. **A test that reads the tree above ``python/`` either skips or is excluded.**
   mutmut copies ``python/`` alone into ``mutants/``, so a test resolving
   ``Path(__file__).resolve().parents[2]`` lands on ``python/`` there rather
   than on the repository root, and every path it builds is absent.  A test
   that answers that by skipping is fine wherever it runs; one that asserts
   fails the baseline instead, which is the same zero-mutant outcome as an
   aborted collection, so it must carry an ``--ignore=`` too.

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
   binding's behaviour.  Run per mutant it costs its whole run each time.
   Python's is the pytest option that collects the fences, absent
   from what mutmut runs; Go's and Rust's are one test each, which the lane
   skips by name, and the skip must reach that test and no other; C++'s is its
   own binary's source, which the binary the Mull runner runs must not
   compile.  Each harness is first found where it is defined, so a rename is a
   failure here rather than a check that names nothing.  The Rust lane also
   skips the benchmark program's tests, every test of
   ``rust/tests/benchmark_program.rs``, which build the benchmark example
   with a cargo of their own, and the skip must reach each of them.  The
   examples a binding's source carries are held to the binding the same way
   and kept out alike: the Go lane's skip reaches every Example function,
   which go test checks against its Output, and the Rust lane selects its
   targets so cargo runs no doctest.

7. **Every recorded C++ slice weight is a file a slice can claim**, and the
   partition claims the whole domain once.

8. **The Go lane turns on every mutator gremlins ships off.**
   ``go/.gremlins.yaml`` sets ``enabled: true`` under each, read as gremlins
   reads it: YAML 1.2 and every key lowercased.  A kind left off makes no
   mutants, and only the lane's recorded ``generated`` count says so.  The
   lane names this file to gremlins and strips every ``GREMLINS_`` variable
   from its environment, so no other configuration file and no variable
   overrides it, and a file its reader refuses, one repeating a key among
   them, stops gremlins before it sweeps.

9. **The mutation build links the C++ library statically.** The Mull runner
   finds mutants in the test executable, and a shared library hides most of
   them from it, so ``cpp/CMakeLists.txt``, read as CMake reads it, sets
   ``ALETHEIA_CPP_LINKAGE`` to ``STATIC`` first under ``ALETHEIA_MUTATION``,
   nowhere else but in that branch's ``else()``, and the library takes that
   form.

10. **Every measured block records the counts its lane is judged by.** The
    runner holds a sweep's ``total_mutants``, and on the lanes whose tool
    reports one its ``generated``, to the record only where the record holds
    them, so a block recording its ``survivors`` records those too.

11. **A tool told which files to mutate is told the hot path.** mutmut's
    ``source_paths`` and cargo-mutants' ``examine_globs`` each name exactly it.

12. **The binary the Mull runner runs compiles every integration case**, which
    ``cpp/CMakeLists.txt`` folds into it under the mutation build.

13. **mutmut forks each mutant's process from its server**
    (``process_isolation = "forkserver"``), which has only collected the suite:
    mutmut's own process runs the suite to time it, starting the kernel's runtime
    and its threads, and a process forked from one holding threads may make only
    async-signal-safe calls.

14. **mutmut writes its log where the lane keeps it** (``log_to_file = true``,
    ``log_file_path`` left at its default under ``mutants/``): a mutant's run
    that raises exits 255 and is filed as a timeout with nothing else of it
    kept, and ``tools/mutation_run.py`` keeps that log beside the witness.

Invariants 6, 8, 9 and 12 are checked by ``tools/check_mutation_setup_lanes.py``.  The
dynamic counterpart is ``tools/mutation_run.py``, which actually drives each
binding's mutation tool against this list and writes per-binding survivor
counts.

Usage:
  python -m tools.check_mutation_setup

Exits 0 if every invariant holds, 1 otherwise (with a precise diagnostic naming
the offending entries), 2 when a file or directory this module reads cannot be
read, or TOML, CMake or a test's Python it cannot parse; a ``go/.gremlins.yaml``
gremlins' reader refuses is invariant 8's refusal instead, since it is a defect
of the file, which the lane's gremlins stops on.
"""

from __future__ import annotations

import argparse
import re
import sys
from typing import TYPE_CHECKING, NewType, cast

import yaml

from tools import check_mutation_setup_imports as collection_imports
from tools._common import RelPath, emit
from tools.check_mutation_setup_lanes import (
    GO_DEFAULT_OFF_MUTATORS,
    MUTANTS_TOML_PATH,
    PYPROJECT_PATH,
    REPO_ROOT,
    Glob,
    TomlString,
    TomlTable,
    cpp_lane_links_the_library_statically,
    cpp_lane_runs_every_integration_case,
    cpp_lane_runs_no_doc_harness,
    exit_unreadable,
    go_lane_runs_no_doc_harness,
    go_lane_turns_on_the_default_off_mutators,
    listed_or_exit,
    python_lane_runs_no_doc_harness,
    read_or_exit,
    rust_lane_runs_no_doc_harness,
    strings_or_exit,
    table_or_exit,
    toml_or_exit,
)
from tools.mutation_cpp_slices import partition, slice_domain
from tools.mutation_run import RUNNERS

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools.mutation_cpp_slices import FileRuns

SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"

# A binding as the record names its block.
BindingName = NewType("BindingName", str)

# An ``--ignore=tests/<name>.py`` entry in the mutmut pytest args.
_IGNORE_ARG_RE = re.compile(r"^--ignore=(tests/[\w./-]+\.py)$")
# A path built above ``python/``: ``parents[2]`` and up, or three ``.parent``
# steps, from a file in ``python/tests/``, or a literal walk up two levels.
# Under ``mutants/`` the same expression stops at ``python/``, so whatever it
# names is not there; a test reads the root through ``tests/_repo_root.py``.
_ABOVE_TREE_RE = re.compile(r"parents\[[2-9]\]|(?:\.parent){3}|\.\./\.\./")
# What lets a test answer an absent path by saying nothing rather than failing.
_SKIPS_RE = re.compile(r"pytest\.skip|skipif|importorskip")


def _load_bindings() -> dict[str, object]:
    """Return the record's ``bindings`` mapping, or stop the gate with exit 2 naming why not."""
    try:
        spec: object = yaml.safe_load(read_or_exit(SPEC_PATH))
    except yaml.YAMLError as exc:
        exit_unreadable(SPEC_PATH, Prose(" ".join(str(exc).split())))
    if not isinstance(spec, dict) or "bindings" not in spec:
        exit_unreadable(SPEC_PATH, Prose("it holds no mapping with a bindings entry"))
    bindings = cast("dict[str, object]", spec)["bindings"]
    if not isinstance(bindings, dict):
        exit_unreadable(SPEC_PATH, Prose("its bindings entry is not a mapping"))
    return cast("dict[str, object]", bindings)


def _baseline(bindings: dict[str, object], binding: BindingName) -> dict[str, object]:
    """Return one block's ``baseline``, empty where the block or its baseline is no mapping."""
    spec = bindings.get(binding)
    if not isinstance(spec, dict):
        return {}
    baseline = cast("dict[str, object]", spec).get("baseline", {})
    return cast("dict[str, object]", baseline) if isinstance(baseline, dict) else {}


def every_block_names_its_tool_and_hot_paths(bindings: dict[str, object]) -> list[Prose]:
    """Return one diagnostic per spec defect across every binding entry."""
    failures: list[Prose] = []
    for binding_name, binding_spec in bindings.items():
        if not isinstance(binding_spec, dict):
            failures.append(Prose(f"[{binding_name}] binding spec must be a mapping"))
            continue
        spec = cast("dict[str, object]", binding_spec)
        tool = spec.get("tool")
        if not isinstance(tool, str) or not tool:
            failures.append(Prose(f"[{binding_name}] missing 'tool' field in spec"))
        hot_path = spec.get("hot_path", [])
        if not isinstance(hot_path, list) or not hot_path:
            failures.append(Prose(f"[{binding_name}] missing or empty 'hot_path' field"))
            continue
        for rel in cast("list[object]", hot_path):
            if not isinstance(rel, str):
                failures.append(Prose(f"[{binding_name}] hot-path entry is not a path: {rel!r}"))
            elif not (REPO_ROOT / rel).is_file():
                failures.append(Prose(f"[{binding_name}] hot-path source does not exist: {rel}"))
    return failures


# A test file as ``[tool.mutmut]`` names it: ``tests/<name>.py``.
TestPath = NewType("TestPath", str)


def every_selecting_tool_mutates_its_hot_path(
    hot_paths: Mapping[BindingName, Sequence[RelPath]],
) -> list[Prose]:
    """Hold the files mutmut and cargo-mutants are told to mutate to ``hot_path``, both ways.

    mutmut mutates ``[tool.mutmut] source_paths``, from ``python/``, and
    cargo-mutants ``examine_globs`` in ``rust/.cargo/mutants.toml``, from
    ``rust/``; gremlins and Mull are told no list.  A file on one side alone is
    surface no existence check holds, or a hot path no mutant reaches.
    """
    told = (
        (
            BindingName("python"),
            Prose("[tool.mutmut] source_paths"),
            "python/",
            strings_or_exit(
                PYPROJECT_PATH,
                _mutmut_table().get(TomlString("source_paths"), []),
                Prose("tool.mutmut.source_paths"),
            ),
        ),
        (
            BindingName("rust"),
            Prose("rust/.cargo/mutants.toml's examine_globs"),
            "rust/",
            strings_or_exit(
                MUTANTS_TOML_PATH,
                toml_or_exit(MUTANTS_TOML_PATH).get(TomlString("examine_globs"), []),
                Prose("examine_globs"),
            ),
        ),
    )
    failures: list[Prose] = []
    for binding, where, root, names in told:
        mutated = {RelPath(f"{root}{name}") for name in names}
        listed = set(hot_paths.get(binding, []))
        failures += [
            Prose(
                f"[{binding}] {where} has the tool mutate {rel}, which the hot path does not list"
            )
            for rel in sorted(mutated - listed)
        ]
        failures += [
            Prose(f"[{binding}] the hot path lists {rel}, which {where} leaves unmutated")
            for rel in sorted(listed - mutated)
        ]
    return failures


def _mutmut_table() -> TomlTable:
    """Return ``[tool.mutmut]`` of ``python/pyproject.toml``.

    Exits 2 if ``pyproject.toml`` cannot be read or has no ``[tool.mutmut]``
    section: invariants 2 and 3 would name every test they match, each told to
    join a section that does not exist, and invariant 11 every hot path.
    """
    tool = table_or_exit(
        PYPROJECT_PATH, toml_or_exit(PYPROJECT_PATH).get(TomlString("tool"), {}), Prose("tool")
    )
    if TomlString("mutmut") not in tool:
        exit_unreadable(PYPROJECT_PATH, Prose("it has no [tool.mutmut] section"))
    return table_or_exit(PYPROJECT_PATH, tool[TomlString("mutmut")], Prose("tool.mutmut"))


def python_lane_keeps_mutmuts_log() -> list[Prose]:
    """Return a failure unless mutmut writes its log where the lane keeps it (invariant 14)."""
    table = _mutmut_table()
    failures: list[Prose] = []
    log_to_file = table.get(TomlString("log_to_file"))
    if log_to_file is not True:
        failures.append(
            Prose(
                f"[python/mutmut] log_to_file is {log_to_file!r}, not true: a mutant's run "
                + "that raises is filed as a timeout, and mutmut's log is its record"
            )
        )
    if TomlString("log_file_path") in table:
        failures.append(
            Prose(
                "[python/mutmut] log_file_path is set: tools/mutation_run.py keeps mutmut's "
                + "log from its default place, mutants/mutmut-debug.log"
            )
        )
    return failures


def python_lane_forks_from_a_collecting_server() -> list[Prose]:
    """Return a failure unless mutmut forks each mutant's process from its server (invariant 13)."""
    isolation = _mutmut_table().get(TomlString("process_isolation"))
    if isolation == "forkserver":
        return []
    return [
        Prose(
            f"[python/mutmut] process_isolation is {isolation!r}, not 'forkserver': "
            + "mutmut's own process starts the kernel's runtime timing the suite, "
            + "and a process forked from it holds that runtime's threads"
        )
    ]


def _mutmut_ignored_tests() -> set[TestPath]:
    """Return the ``tests/<name>.py`` files excluded via ``--ignore`` in [tool.mutmut]."""
    return {
        TestPath(match.group(1))
        for arg in strings_or_exit(
            PYPROJECT_PATH,
            _mutmut_table().get(TomlString("pytest_add_cli_args"), []),
            Prose("tool.mutmut.pytest_add_cli_args"),
        )
        if (match := _IGNORE_ARG_RE.match(arg))
    }


def _test_files() -> list[Path]:
    """Return every ``test_*.py`` of ``python/tests/``, or stop the gate with exit 2 without one.

    Without the directory every check of it would pass holding nothing.
    """
    return listed_or_exit(collection_imports.PY_TESTS_DIR, Glob("test_*.py"))


def every_tools_importing_test_is_ignored() -> list[Prose]:
    """One diagnostic per test whose collection imports ``tools`` and the lane runs.

    A helper of ``python/tests/`` the test imports is read as the test is, so
    an import two modules down aborts the collection as one at the top does.
    """
    paths = _test_files()
    ignored = _mutmut_ignored_tests()
    failures: list[Prose] = []
    for path in paths:
        rel = TestPath(f"tests/{path.name}")
        route = collection_imports.tools_route(path, set())
        if route is not None and rel not in ignored:
            through = collection_imports.route_text(route)
            failures.append(
                Prose(
                    f"[python/mutmut] {rel} imports the repo-root `tools` package"
                    + f"{through} but is not excluded: add `--ignore={rel}` to "
                    + "[tool.mutmut].pytest_add_cli_args (it holds the tools, not a hot "
                    + "path, and costs every mutant its run)"
                )
            )
    conftest = collection_imports.PY_TESTS_DIR / "conftest.py"
    route = collection_imports.tools_route(conftest, set()) if conftest.is_file() else None
    if route is not None:
        through = collection_imports.route_text(route)
        failures.append(
            Prose(
                "[python/mutmut] tests/conftest.py imports the repo-root `tools` package"
                + f"{through}: pytest imports it for every test, so no `--ignore=` "
                + "keeps the tools out of a mutant's run"
            )
        )
    return failures


def every_above_tree_test_skips_or_is_ignored() -> list[Prose]:
    """One diagnostic per test that reads above ``python/``, cannot skip, and is not ignored.

    The three properties are one finding together: reaching above the copied
    tree is ordinary, and several tests do it and skip when what they wanted is
    absent; it is the test that asserts on what it found there that fails
    mutmut's baseline and leaves the lane with no mutants at all.
    """
    paths = _test_files()
    ignored = _mutmut_ignored_tests()
    failures: list[Prose] = []
    for path in paths:
        source = read_or_exit(path)
        if not _ABOVE_TREE_RE.search(source) or _SKIPS_RE.search(source):
            continue
        rel = TestPath(f"tests/{path.name}")
        if rel not in ignored:
            failures.append(
                Prose(
                    f"[python/mutmut] {rel} reads the tree above python/ and cannot skip, but "
                    + f"is not excluded: add `--ignore={rel}` to "
                    + "[tool.mutmut].pytest_add_cli_args, or make it skip when the path is "
                    + "absent (under mutants/ it is)"
                )
            )
    return failures


def cpp_slice_weights_are_of_the_domain(bindings: dict[str, object]) -> list[Prose]:
    """Hold the recorded weights to the files a slice can actually claim.

    The slices are cut on the recorded weights, so a record with none is
    refused: the slices would be cut on nothing, every file weighing the same.
    The slices are cut over every tracked file of the library, so no file can
    be left out of them; what can go wrong is the other direction, a recorded
    weight for a file that has been renamed or held out, which silently stops
    counting toward the balance.  The partition itself is checked here too:
    the whole domain, once each, which is the property every other refusal in
    the lane is written against.
    """
    recorded = cast("FileRuns", _baseline(bindings, BindingName("cpp")).get("runs_by_file", {}))
    if not recorded:
        return [
            Prose(
                "[cpp/slices] runs_by_file records nothing, so the slices are cut on "
                + "nothing: re-take it from a run's cpp-runs.json"
            )
        ]
    config = REPO_ROOT / "cpp" / "mull.yml"
    try:
        domain = slice_domain(REPO_ROOT, config)
    except (OSError, UnicodeDecodeError, yaml.YAMLError, TypeError) as exc:
        exit_unreadable(config, Prose(" ".join(str(exc).split())))
    failures = [
        Prose(
            f"[cpp/slices] {path} carries a recorded weight and is not a file a slice "
            + "can claim: it is untracked, renamed, or held out by cpp/mull.yml, so "
            + "its weight counts toward no slice"
        )
        for path in sorted(set(recorded) - set(domain))
    ]
    claimed = [path for claims in partition(domain, recorded) for path in claims]
    if sorted(claimed) != sorted(domain):
        failures.append(
            Prose(
                f"[cpp/slices] the partition claims {len(claimed)} of the domain's "
                + f"{len(domain)} files; a file in no slice is mutated by every slice, "
                + "and one in two is swept twice"
            )
        )
    return failures


def every_runner_has_a_block(bindings: dict[str, object]) -> list[Prose]:
    """Hold the record to one block per binding the runner drives, and no other."""
    known = {name for name, _skip_var, _runner in RUNNERS}
    return [
        Prose(
            f"[bindings] no block for {name}, which the runner sweeps: its first run would "
            + "report first_run and gate nothing"
        )
        for name in sorted(known - set(bindings))
    ] + [
        Prose(f"[bindings/{name}] the runner has no such binding, so nothing reads this block")
        for name in sorted(set(bindings) - known)
    ]


# The lanes whose tool reports every mutant it made, which the runner holds
# to the record's ``generated`` (tools/mutation_go.py, tools/mutation_rust.py).
_GENERATING_LANES = frozenset({BindingName("go"), BindingName("rust")})


def every_block_records_its_counts(bindings: dict[str, object]) -> list[Prose]:
    """Hold each measured block to the counts the runner judges a sweep against.

    The runner compares a sweep's count with the record's only where the
    record holds one, so a count dropped from a block is a comparison dropped
    from its lane, and nothing else says so.
    """
    failures: list[Prose] = []
    for name in map(BindingName, bindings):
        baseline = _baseline(bindings, name)
        if "survivors" not in baseline:
            continue
        counts = ["total_mutants", *(["generated"] if name in _GENERATING_LANES else [])]
        failures += [
            Prose(
                f"[{name}/baseline] records its survivors and no {count} count, so the "
                + f"lane holds a sweep's {count} to nothing"
            )
            for count in counts
            if not isinstance(baseline.get(count), int) or isinstance(baseline.get(count), bool)
        ]
    return failures


# A ledger a block's baseline records rows in.
LedgerName = NewType("LedgerName", str)
_LEDGERS = (
    LedgerName("survivors_ledger"),
    LedgerName("unobserved_ledger"),
    LedgerName("not_covered_ledger"),
)


def ledger_rows_still_name_their_line(bindings: dict[str, object]) -> list[Prose]:
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
    failures: list[Prose] = []
    for binding_name in map(BindingName, bindings):
        baseline = _baseline(bindings, binding_name)
        for name in _LEDGERS:
            rows = baseline.get(name, [])
            if not isinstance(rows, list):
                failures.append(Prose(f"[{binding_name}/{name}] must be a list of rows"))
                continue
            for row in cast("list[object]", rows):
                if not isinstance(row, dict):
                    failures.append(Prose(f"[{binding_name}/{name}] every row must be a mapping"))
                    continue
                failures += _row_names_its_line(binding_name, name, cast("dict[str, object]", row))
    return failures


def _row_names_its_line(
    binding_name: BindingName, ledger: LedgerName, row: dict[str, object]
) -> list[Prose]:
    """Say why one ledger row no longer names a line of the tree, or nothing."""
    file, text = row.get("file"), row.get("text")
    if not isinstance(file, str) or not isinstance(text, str):
        return [Prose(f"[{binding_name}/{ledger}] a row must carry a 'file' and a 'text'")]
    source = REPO_ROOT / file
    if not source.is_file():
        return [
            Prose(
                f"[{binding_name}/{ledger}] {file} is not a file of the tree: the row records a "
                + "line of a source that was renamed or removed, and nothing else reads it"
            )
        ]
    if not any(line.strip() == text for line in str(read_or_exit(source)).split("\n")):
        return [
            Prose(
                f"[{binding_name}/{ledger}] {file} holds no line reading {text!r}: the row was "
                + "recorded against a line the tree has since reworded, so re-take the ledger "
                + "from a sweep or delete the row with the change that made it stale"
            )
        ]
    return []


def _ledger_rows(bindings: dict[str, object]) -> int:
    """Count the ledger rows the record carries, over every binding and every ledger."""
    total = 0
    for binding_name in map(BindingName, bindings):
        baseline = _baseline(bindings, binding_name)
        for name in _LEDGERS:
            rows = baseline.get(name, [])
            if isinstance(rows, list):
                total += len(cast("list[object]", rows))
    return total


def listed_hot_paths(bindings: dict[str, object]) -> dict[BindingName, list[RelPath]]:
    """Return each block's ``hot_path`` entries that are paths, none where it lists none."""
    found: dict[BindingName, list[RelPath]] = {}
    for binding_name, binding_spec in bindings.items():
        if not isinstance(binding_spec, dict):
            continue
        hot_path = cast("dict[str, object]", binding_spec).get("hot_path", [])
        entries = cast("list[object]", hot_path) if isinstance(hot_path, list) else []
        found[BindingName(binding_name)] = [RelPath(rel) for rel in entries if isinstance(rel, str)]
    return found


def main() -> int:
    """Run every check of the module docstring, naming each failure on stderr."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    bindings = _load_bindings()
    hot_paths = listed_hot_paths(bindings)
    failures = every_block_names_its_tool_and_hot_paths(bindings)
    failures += every_selecting_tool_mutates_its_hot_path(hot_paths)
    failures += every_tools_importing_test_is_ignored()
    failures += every_above_tree_test_skips_or_is_ignored()
    failures += cpp_slice_weights_are_of_the_domain(bindings)
    failures += every_runner_has_a_block(bindings)
    failures += ledger_rows_still_name_their_line(bindings)
    failures += python_lane_runs_no_doc_harness()
    failures += python_lane_forks_from_a_collecting_server()
    failures += python_lane_keeps_mutmuts_log()
    failures += go_lane_runs_no_doc_harness()
    failures += rust_lane_runs_no_doc_harness()
    failures += cpp_lane_runs_no_doc_harness()
    failures += cpp_lane_runs_every_integration_case()
    failures += go_lane_turns_on_the_default_off_mutators()
    failures += cpp_lane_links_the_library_statically()
    failures += every_block_records_its_counts(bindings)

    if failures:
        _ = sys.stderr.write("Mutation-setup coverage gate FAILED:\n")
        for failure in failures:
            _ = sys.stderr.write(f"  - {failure}\n")
        _ = sys.stderr.write(
            f"\n{len(failures)} issue(s) above.  For a missing hot-path source: "
            + f"restore it or update {SPEC_PATH.relative_to(REPO_ROOT)} to reflect "
            + "the rename.  For a file mutmut or cargo-mutants is told to mutate and the "
            + "record does not list, or the reverse: name it in both or in neither.  "
            + "For a test that the mutated tree cannot satisfy: add its "
            + "`--ignore=` to [tool.mutmut], or let it skip.  For a doc-example harness "
            + "a lane reaches: skip it in that lane's per-mutant run, and it alone, the "
            + "Rust lane the benchmark program's tests beside it.  For a mutator or the "
            + "library's link form: restore it in go/.gremlins.yaml or cpp/CMakeLists.txt.  "
            + "For a count: re-take it from a sweep.\n",
        )
        return 1

    total = sum(map(len, hot_paths.values()))
    emit(
        "Mutation-setup coverage gate OK: "
        + f"{len(bindings)} bindings, {total} hot-path sources all present; "
        + "mutmut and cargo-mutants mutate their hot paths and no other file; "
        + "every test the mutated tree cannot satisfy is mutmut-ignored; "
        + "every recorded C++ slice weight is a file the partition claims; "
        + "one block per binding the runner drives; "
        + f"each of {_ledger_rows(bindings)} ledger rows names a line the tree holds; "
        + "no lane's per-mutant run reaches its doc-example harness; "
        + "mutmut forks each mutant from its server and writes its log where the lane keeps it; "
        + "the C++ lane's binary runs every integration case; "
        + f"the Go lane turns on the {len(GO_DEFAULT_OFF_MUTATORS)} mutators gremlins ships off; "
        + "the mutation build links the C++ library statically; "
        + "every measured block records its counts.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
