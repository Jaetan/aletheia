# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_mutation_setup``: each check refuses what it names, ``main`` runs all.

A check reading the tree is pointed at a planted one, the module's paths
monkeypatched to files the test writes; one reading the record alone is handed
a literal mapping; each one's diagnostics are compared whole.  The wiring test
stands every check in for one returning its own name, so a check ``main``
stops calling is a name missing from its output, and a check handed anything
but the record ``main`` read is a call the test refuses.  The lanes' checks,
invariants 6, 8 and 9, are held by ``test_check_mutation_setup_lanes.py`` and
``test_check_mutation_setup_cpp_lane.py``, the slice weights by
``test_check_mutation_slices.py``, and a ledger row naming a line the tree no
longer holds by ``test_mutation_unobserved_ledger.py``.
"""

from __future__ import annotations

import os
import sys
from typing import TYPE_CHECKING, Final, Literal, NewType
from unittest.mock import Mock

import pytest
from _gate_exit import stderr_of_exit_2
from _planted_tree import plant

from tools import check_mutation_setup
from tools._common import RelPath
from tools.check_mutation_setup import BindingName

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence
    from pathlib import Path

# A file's name under ``python/tests``.
TestFile = NewType("TestFile", str)
# A check of the gate as its module names it.
CheckName = NewType("CheckName", str)


# The record: one block per runner, each naming its tool and hot paths that exist.


def test_one_block_per_runner_passes() -> None:
    """A record with a block for each binding the runner sweeps, and none other, is clean."""
    assert not check_mutation_setup.every_runner_has_a_block(
        {"python": {}, "go": {}, "cpp": {}, "rust": {}}
    )


def test_a_runner_without_a_block_and_a_block_without_a_runner_are_named() -> None:
    """The Rust block renamed to a binding no runner has: one block missing, one unread."""
    assert check_mutation_setup.every_runner_has_a_block(
        {"python": {}, "go": {}, "cpp": {}, "haskell": {}}
    ) == [
        "[bindings] no block for rust, which the runner sweeps: its first run would "
        + "report first_run and gate nothing",
        "[bindings/haskell] the runner has no such binding, so nothing reads this block",
    ]


def test_a_hot_path_that_is_not_there_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Of two listed hot-path sources, the one the tree does not hold is named."""
    _ = plant(tmp_path, {RelPath("go/aletheia/client.go"): Prose("package aletheia\n")})
    monkeypatch.setattr(check_mutation_setup, "REPO_ROOT", tmp_path)
    assert check_mutation_setup.every_block_names_its_tool_and_hot_paths(
        {
            "go": {
                "tool": "gremlins",
                "hot_path": ["go/aletheia/client.go", "go/aletheia/moved_away.go"],
            }
        }
    ) == ["[go] hot-path source does not exist: go/aletheia/moved_away.go"]


def test_a_block_without_its_tool_or_its_hot_paths_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A block no mapping, naming no tool, listing no hot path or a hot path no path is named."""
    _ = plant(tmp_path, {RelPath("go/aletheia/client.go"): Prose("package aletheia\n")})
    monkeypatch.setattr(check_mutation_setup, "REPO_ROOT", tmp_path)
    assert check_mutation_setup.every_block_names_its_tool_and_hot_paths(
        {
            "a": "gremlins",
            "b": {"hot_path": ["go/aletheia/client.go"]},
            "c": {"tool": "", "hot_path": ["go/aletheia/client.go"]},
            "d": {"tool": "gremlins"},
            "e": {"tool": "gremlins", "hot_path": []},
            "f": {"tool": "gremlins", "hot_path": [3, "go/aletheia/client.go"]},
        }
    ) == [
        "[a] binding spec must be a mapping",
        "[b] missing 'tool' field in spec",
        "[c] missing 'tool' field in spec",
        "[d] missing or empty 'hot_path' field",
        "[e] missing or empty 'hot_path' field",
        "[f] hot-path entry is not a path: 3",
    ]


@pytest.mark.parametrize(
    ("record", "reason"),
    [
        pytest.param(None, Prose("No such file or directory"), id="missing"),
        pytest.param(
            Prose("bindings: [python\n"),
            Prose(
                'while parsing a flow sequence in "<unicode string>", line 1, column 11: '
                + "bindings: [python ^ expected ',' or ']', but got '<stream end>' in "
                + '"<unicode string>", line 2, column 1: ^'
            ),
            id="no YAML",
        ),
        pytest.param(
            Prose("- bindings\n"),
            Prose("it holds no mapping with a bindings entry"),
            id="a list",
        ),
        pytest.param(
            Prose("python: {}\n"),
            Prose("it holds no mapping with a bindings entry"),
            id="no bindings",
        ),
        pytest.param(
            Prose("bindings: [python]\n"),
            Prose("its bindings entry is not a mapping"),
            id="bindings a list",
        ),
    ],
)
def test_a_record_the_gate_cannot_read_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    record: Prose | None,
    reason: Prose,
) -> None:
    """A record missing, no YAML, or holding no mapping of bindings stops the gate with exit 2."""
    spec = tmp_path / "MUTATION_BENCH.yaml"
    if record is not None:
        _ = plant(tmp_path, {RelPath(spec.name): record})
    monkeypatch.setattr(check_mutation_setup, "SPEC_PATH", spec)
    monkeypatch.setattr(sys, "argv", ["check_mutation_setup"])
    assert stderr_of_exit_2(capsys, check_mutation_setup.main) == (
        f"ERROR: cannot read {spec}: {reason}\n"
    )


# Every measured block records the counts its lane is judged by.


def _no_count(binding: BindingName, count: Literal["total_mutants", "generated"]) -> Prose:
    """Return the diagnostic for a block recording its survivors and not ``count``."""
    return Prose(
        f"[{binding}/baseline] records its survivors and no {count} count, so the "
        + f"lane holds a sweep's {count} to nothing"
    )


def test_every_measured_block_recording_its_counts_passes() -> None:
    """Each lane's counts recorded, and a block measuring nothing, are clean."""
    assert not check_mutation_setup.every_block_records_its_counts(
        {
            "python": {"baseline": {"survivors": 0, "total_mutants": 12}},
            "go": {"baseline": {"survivors": 1, "total_mutants": 30, "generated": 34}},
            "rust": {"baseline": {"survivors": 0, "total_mutants": 9, "generated": 9}},
            "cpp": {"baseline": {"survivors": 0, "total_mutants": 40}},
            "unmeasured": {"baseline": {}},
            "no baseline": {"tool": "mull"},
            "no block": "mull",
        }
    )


def test_a_measured_block_missing_a_count_is_named() -> None:
    """A count absent, a boolean, or text where its lane is judged by it is named."""
    assert check_mutation_setup.every_block_records_its_counts(
        {
            "python": {"baseline": {"survivors": 0}},
            "go": {"baseline": {"survivors": 0}},
            "rust": {"baseline": {"survivors": 0, "total_mutants": 9, "generated": True}},
            "cpp": {"baseline": {"survivors": 0, "total_mutants": "40"}},
        }
    ) == [
        _no_count(BindingName("python"), "total_mutants"),
        _no_count(BindingName("go"), "total_mutants"),
        _no_count(BindingName("go"), "generated"),
        _no_count(BindingName("rust"), "generated"),
        _no_count(BindingName("cpp"), "total_mutants"),
    ]


# The Python lane: what mutmut's copy of python/ cannot run is ignored.


def _plant_python_tests(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
    files: Mapping[TestFile, Prose],
    ignored: Sequence[TestFile] = (),
) -> None:
    """Plant ``files`` in ``python/tests`` and a ``[tool.mutmut]`` ignoring ``ignored``."""
    args = ", ".join(f'"--ignore=tests/{name}"' for name in ignored)
    pyproject = RelPath("python/pyproject.toml")
    _ = plant(
        root,
        {RelPath(f"python/tests/{name}"): text for name, text in files.items()}
        | {pyproject: Prose(f"[tool.mutmut]\npytest_add_cli_args = [{args}]\n")},
    )
    monkeypatch.setattr(check_mutation_setup, "PY_TESTS_DIR", root / "python" / "tests")
    monkeypatch.setattr(check_mutation_setup, "PYPROJECT_PATH", root / pyproject)


_DIRECT: Final = Prose("")


def _not_ignored_import(name: TestFile, through: Prose = _DIRECT) -> Prose:
    """Return the diagnostic for a ``tools``-importing test the lane does not ignore."""
    return Prose(
        f"[python/mutmut] tests/{name} imports the repo-root `tools` package{through} but is "
        + f"not excluded: add `--ignore=tests/{name}` to [tool.mutmut].pytest_add_cli_args "
        + "(it holds the tools, not a hot path, and costs every mutant its run)"
    )


def _conftest_imports(through: Prose = _DIRECT) -> Prose:
    """Return the diagnostic for a ``conftest.py`` whose import reaches ``tools``."""
    return Prose(
        f"[python/mutmut] tests/conftest.py imports the repo-root `tools` package{through}: "
        + "pytest imports it for every test, so no `--ignore=` keeps the tools out of a "
        + "mutant's run"
    )


def _not_ignored_above_tree(name: TestFile) -> Prose:
    """Return the diagnostic for a test reading above ``python/`` that cannot skip, not ignored."""
    return Prose(
        f"[python/mutmut] tests/{name} reads the tree above python/ and cannot skip, but "
        + f"is not excluded: add `--ignore=tests/{name}` to [tool.mutmut].pytest_add_cli_args, "
        + "or make it skip when the path is absent (under mutants/ it is)"
    )


_TEST: Final = TestFile("test_x.py")


@pytest.mark.parametrize(
    "source",
    [
        pytest.param(Prose('"""Doc."""\nfrom tools.check import x\n'), id="from"),
        pytest.param(Prose("import tools\n"), id="import"),
        pytest.param(Prose("import os, tools.check\n"), id="the second of two"),
        pytest.param(Prose("class T:\n    import tools\n"), id="a class body"),
        pytest.param(Prose("with open('x') as f:\n    import tools\n"), id="a with body"),
        pytest.param(Prose("for x in []:\n    import tools\n"), id="a for body"),
        pytest.param(Prose("match 1:\n    case 1:\n        import tools\n"), id="a case"),
        pytest.param(
            Prose("try:\n    import tools\nexcept ImportError:\n    pass\n"), id="a try body"
        ),
        pytest.param(
            Prose("try:\n    import tools\nexcept* ImportError:\n    pass\n"), id="an except* body"
        ),
        pytest.param(
            Prose("try:\n    import os\nexcept ImportError:\n    import tools\n"), id="a handler"
        ),
        pytest.param(
            Prose("try:\n    import os\nexcept ImportError:\n    pass\nelse:\n    import tools\n"),
            id="the else of a try",
        ),
        pytest.param(
            Prose("if TYPE_CHECKING:\n    pass\nelse:\n    import tools\n"),
            id="the else of TYPE_CHECKING",
        ),
        pytest.param(Prose("def f():\n    import tools\nf()\n"), id="a function the module calls"),
        pytest.param(
            Prose("def g():\n    import tools\ndef f():\n    g()\nf()\n"),
            id="a function called through another",
        ),
        pytest.param(
            Prose("def f():\n    import tools\n    f()\nf()\n"), id="a function calling itself"
        ),
        pytest.param(
            Prose("def f(g):\n    import tools\n    return g\n@f\ndef test_x():\n    pass\n"),
            id="a function called as a decorator",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\n@pytest.mark.skipif(f())\ndef test_x():\n    pass\n"
            ),
            id="a function called in a decorator's arguments",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(x=f()):\n    pass\n"),
            id="a function called in a default argument",
        ),
        pytest.param(
            Prose("def f():\n    import tools\nclass T:\n    x = f()\n"),
            id="a function a class body calls",
        ),
        pytest.param(
            Prose("def f():\n    import tools\nX = [f() for _ in [1]]\n"),
            id="a function a comprehension calls",
        ),
        pytest.param(
            Prose("if True:\n    def f():\n        import tools\nf()\n"),
            id="a function defined under an if",
        ),
        pytest.param(
            Prose("class T:\n    def f():\n        import tools\n    f()\n"),
            id="a function a class body defines and calls",
        ),
        pytest.param(
            Prose("def g():\n    def h():\n        import tools\n    h()\ng()\n"),
            id="a function a called function defines and calls",
        ),
        pytest.param(Prose("__import__('tools')\n"), id="__import__"),
        pytest.param(
            Prose("from importlib import import_module\nimport_module('.check', 'tools')\n"),
            id="import_module relative to a package",
        ),
        pytest.param(
            Prose("import importlib\nimportlib.import_module('.check', package='tools')\n"),
            id="import_module relative to a package keyword",
        ),
        pytest.param(
            Prose("import importlib\nimportlib.import_module('tools.check')\n"),
            id="importlib.import_module",
        ),
        pytest.param(
            Prose("from importlib import import_module\nimport_module('tools')\n"),
            id="import_module",
        ),
    ],
)
def test_an_import_collection_runs_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, source: Prose
) -> None:
    """An import of ``tools`` that runs when pytest imports the test is named."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: source})
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(_TEST)
    ]


@pytest.mark.parametrize(
    "source",
    [
        pytest.param(Prose("def test_x() -> None:\n    from tools import x\n"), id="a function"),
        pytest.param(Prose("async def test_x() -> None:\n    import tools\n"), id="a coroutine"),
        pytest.param(
            Prose("class T:\n    def f(self) -> None:\n        import tools\n"), id="a method"
        ),
        pytest.param(
            Prose("def g():\n    import tools\ndef f():\n    g()\n"),
            id="a function only another calls",
        ),
        pytest.param(
            Prose("async def f():\n    import tools\nf()\n"), id="a coroutine the module calls"
        ),
        pytest.param(
            Prose("def f():\n    import tools\nX = lambda: f()\n"), id="a function a lambda calls"
        ),
        pytest.param(Prose("@pytest.fixture\ndef f():\n    import tools\n"), id="a fixture"),
        pytest.param(
            Prose("def f():\n    pass\nclass T:\n    def f(self):\n        import tools\nf()\n"),
            id="a method sharing a module function's name",
        ),
        pytest.param(
            Prose("def g():\n    h()\nclass T:\n    def h():\n        import tools\n    g()\n"),
            id="a name the called function's own scope lacks",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(x: f() = 1) -> f():\n    pass\n"),
            id="an annotation",
        ),
        pytest.param(Prose("def f():\n    import tools\nX: f() = 1\n"), id="a module annotation"),
        pytest.param(
            Prose("def f():\n    import tools\nX = (f() for _ in [1])\n"),
            id="a generator expression",
        ),
        pytest.param(
            Prose("def f():\n    import tools\nclass T:\n    def g(self):\n        f()\n"),
            id="a function a method calls",
        ),
        pytest.param(Prose("import toolsmith\n"), id="another package"),
        pytest.param(Prose("from .tools import x\n"), id="a relative import"),
        pytest.param(Prose("# import tools\nX = 'import tools'\n"), id="text"),
        pytest.param(Prose("if TYPE_CHECKING:\n    import tools\n"), id="TYPE_CHECKING"),
        pytest.param(
            Prose("if typing.TYPE_CHECKING:\n    import tools\n"), id="typing.TYPE_CHECKING"
        ),
    ],
)
def test_an_import_collection_does_not_run_is_not_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, source: Prose
) -> None:
    """An import that does not run when pytest imports the test is not named."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: source})
    assert not check_mutation_setup.every_tools_importing_test_is_ignored()


def test_a_tools_importing_test_the_lane_ignores_is_not_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Of two tests importing ``tools``, the one ``--ignore=`` names is left alone."""
    ignored = TestFile("test_y.py")
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {_TEST: Prose("import tools\n"), ignored: Prose("import tools.check\n")},
        [ignored],
    )
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(_TEST)
    ]


def test_an_import_reaching_tools_through_helpers_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A helper of ``python/tests`` is read as the test is, two modules down included."""
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            TestFile("test_a.py"): Prose("import _near\n"),
            TestFile("test_b.py"): Prose("from _far import x\n"),
            TestFile("test_c.py"): Prose("import _clean\nimport _absent\n"),
            TestFile("_near.py"): Prose("from tools.check import x\n"),
            TestFile("_far.py"): Prose("import _near\n"),
            TestFile("_clean.py"): Prose("import os\n"),
        },
    )
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(TestFile("test_a.py"), Prose(" through tests/_near.py")),
        _not_ignored_import(TestFile("test_b.py"), Prose(" through tests/_far.py, tests/_near.py")),
    ]


def test_an_import_reaching_tools_through_a_helper_package_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A helper package's ``__init__``, and a module of it, are read as a helper module is."""
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            TestFile("test_a.py"): Prose("import _hp\n"),
            TestFile("test_b.py"): Prose("import _hq.sub\n"),
            TestFile("test_c.py"): Prose("from _hq import sub\n"),
            TestFile("test_d.py"): Prose("from _hq import nothing\n"),
            TestFile("_hp/__init__.py"): Prose("import tools\n"),
            TestFile("_hq/__init__.py"): Prose(""),
            TestFile("_hq/sub.py"): Prose("import tools\n"),
        },
    )
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(TestFile("test_a.py"), Prose(" through tests/_hp/__init__.py")),
        _not_ignored_import(TestFile("test_b.py"), Prose(" through tests/_hq/sub.py")),
        _not_ignored_import(TestFile("test_c.py"), Prose(" through tests/_hq/sub.py")),
    ]


def test_a_test_importing_tools_itself_is_named_as_direct(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A test importing ``tools`` after a helper that reaches it is named for its own import."""
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            _TEST: Prose("import _near\nimport tools\n"),
            TestFile("_near.py"): Prose("import tools\n"),
        },
    )
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(_TEST)
    ]


def test_helpers_importing_each_other_end(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A cycle among helpers is read once round, and names nothing when it reaches no ``tools``."""
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            _TEST: Prose("import _ping\n"),
            TestFile("_ping.py"): Prose("import _pong\n"),
            TestFile("_pong.py"): Prose("import _ping\n"),
        },
    )
    assert not check_mutation_setup.every_tools_importing_test_is_ignored()


@pytest.mark.parametrize(
    ("helpers", "through"),
    [
        pytest.param({}, _DIRECT, id="itself"),
        pytest.param(
            {TestFile("_h.py"): Prose("import tools\n")},
            Prose(" through tests/_h.py"),
            id="through a helper",
        ),
    ],
)
def test_a_conftest_reaching_tools_is_named(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    helpers: Mapping[TestFile, Prose],
    through: Prose,
) -> None:
    """A ``conftest.py`` reaching ``tools`` is named alone: no ``--ignore=`` answers it."""
    conftest = Prose("import _h\n" if helpers else "import tools\n")
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {TestFile("conftest.py"): conftest, _TEST: Prose("import os\n"), **helpers},
        [TestFile("conftest.py")],
    )
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _conftest_imports(through)
    ]


def test_a_test_that_is_no_python_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A test the parser refuses stops the gate, naming the file and the parser's reason."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: Prose("def (:\n")})
    assert stderr_of_exit_2(capsys, check_mutation_setup.every_tools_importing_test_is_ignored) == (
        f"ERROR: cannot read {tmp_path / 'python' / 'tests' / _TEST}: invalid syntax at line 1\n"
    )


@pytest.mark.parametrize(
    ("source", "reason"),
    [
        pytest.param(
            Prose("import importlib\nimportlib.import_module(NAME)\n"),
            Prose("names its module by an expression, which this gate reads only spelled"),
            id="an expression",
        ),
        pytest.param(
            Prose("import importlib\nimportlib.import_module('.check', PKG)\n"),
            Prose("names its module relative to a package it does not spell"),
            id="a package that is an expression",
        ),
        pytest.param(
            Prose("import importlib\nimportlib.import_module('.check')\n"),
            Prose("names its module relative to a package it does not spell"),
            id="no package",
        ),
        pytest.param(
            Prose("import importlib\nimportlib.import_module('..check', 'tools')\n"),
            Prose(
                "names its module above its package: attempted relative import beyond "
                + "top-level package"
            ),
            id="a package the name climbs out of",
        ),
    ],
)
def test_a_module_a_test_imports_without_spelling_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    source: Prose,
    reason: Prose,
) -> None:
    """An import naming its module by an expression stops the gate, which reads a name spelled."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: source})
    assert stderr_of_exit_2(capsys, check_mutation_setup.every_tools_importing_test_is_ignored) == (
        f"ERROR: cannot read {tmp_path / 'python' / 'tests' / _TEST}: the import at line 2 "
        + f"{reason}\n"
    )


def test_a_test_the_mutated_tree_cannot_satisfy_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A test reading above ``python/`` is named unless it can skip or is ignored."""
    above = "ROOT = Path(__file__).resolve().parents[2]\n"
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            TestFile("test_a_asserting.py"): Prose(above),
            TestFile("test_b_walking.py"): Prose('DOCS = "../../docs"\n'),
            TestFile("test_c_skip.py"): Prose(f"{above}pytest.skip('absent')\n"),
            TestFile("test_d_skipif.py"): Prose(f"{above}@pytest.mark.skipif(True)\n"),
            TestFile("test_e_importorskip.py"): Prose(f"{above}pytest.importorskip('x')\n"),
            TestFile("test_f_ignored.py"): Prose(above),
            TestFile("test_g_inside.py"): Prose("HERE = Path(__file__).parents[1]\n"),
        },
        [TestFile("test_f_ignored.py")],
    )
    assert check_mutation_setup.every_above_tree_test_skips_or_is_ignored() == [
        _not_ignored_above_tree(TestFile("test_a_asserting.py")),
        _not_ignored_above_tree(TestFile("test_b_walking.py")),
    ]


_PYTHON_TEST_CHECKS: Final = [
    pytest.param(check_mutation_setup.every_tools_importing_test_is_ignored, id="tools imports"),
    pytest.param(check_mutation_setup.every_above_tree_test_skips_or_is_ignored, id="above tree"),
]


@pytest.mark.parametrize("check", _PYTHON_TEST_CHECKS)
def test_a_tests_directory_that_is_missing_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    check: Callable[[], list[Prose]],
) -> None:
    """With no ``python/tests`` neither check can hold anything, so the gate stops."""
    monkeypatch.setattr(check_mutation_setup, "PY_TESTS_DIR", tmp_path / "tests")
    assert (
        stderr_of_exit_2(capsys, check)
        == f"ERROR: cannot read {tmp_path / 'tests'}: No such file or directory\n"
    )


@pytest.mark.skipif(os.geteuid() == 0, reason="root lists through a mode of 000")
@pytest.mark.parametrize("check", _PYTHON_TEST_CHECKS)
def test_a_tests_directory_that_cannot_be_listed_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    check: Callable[[], list[Prose]],
) -> None:
    """A ``python/tests`` that cannot be listed stops the gate rather than listing nothing."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: Prose("import tools\n")})
    tests = tmp_path / "python" / "tests"
    tests.chmod(0)
    try:
        assert stderr_of_exit_2(capsys, check) == f"ERROR: cannot read {tests}: Permission denied\n"
    finally:
        tests.chmod(0o700)


@pytest.mark.parametrize(
    ("pyproject", "reason"),
    [
        pytest.param(None, Prose("No such file or directory"), id="missing"),
        pytest.param(Prose("tool = 1\n"), Prose("its tool is not a mapping"), id="tool no mapping"),
        pytest.param(
            Prose("[tool]\nmutmut = 1\n"),
            Prose("its tool.mutmut is not a mapping"),
            id="mutmut no mapping",
        ),
        pytest.param(
            Prose('[tool.mutmut]\npytest_add_cli_args = "--ignore=tests/test_x.py"\n'),
            Prose("its tool.mutmut.pytest_add_cli_args is not a list of strings"),
            id="the arguments one string",
        ),
        pytest.param(
            Prose("[tool.mutmut]\npytest_add_cli_args = [1]\n"),
            Prose("its tool.mutmut.pytest_add_cli_args is not a list of strings"),
            id="an argument no string",
        ),
        pytest.param(
            Prose("[tool.pytest.ini_options]\n"),
            Prose("it has no [tool.mutmut] section"),
            id="no mutmut",
        ),
        pytest.param(
            Prose("[tool.mutmut\n"),
            Prose("Expected ']' at the end of a table declaration (at line 1, column 13)"),
            id="no TOML",
        ),
    ],
)
def test_a_pyproject_without_the_mutmut_section_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    pyproject: Prose | None,
    reason: Prose,
) -> None:
    """A ``pyproject.toml`` missing, no TOML, or holding no ``[tool.mutmut]`` stops both checks."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: Prose("import os\n")})
    path = tmp_path / "python" / "pyproject.toml"
    if pyproject is None:
        path.unlink()
    else:
        _ = plant(tmp_path, {RelPath("python/pyproject.toml"): pyproject})
    for check in (
        check_mutation_setup.every_tools_importing_test_is_ignored,
        check_mutation_setup.every_above_tree_test_skips_or_is_ignored,
    ):
        assert stderr_of_exit_2(capsys, check) == f"ERROR: cannot read {path}: {reason}\n"


# The ledgers: every row is a mapping naming a file and a text.


def test_a_misshapen_ledger_or_row_is_named() -> None:
    """A ledger no list, a row no mapping and a row without a file or a text are named."""
    assert check_mutation_setup.ledger_rows_still_name_their_line(
        {
            "go": {
                "baseline": {
                    "unobserved_ledger": {"file": "go/aletheia/client.go"},
                    "not_covered_ledger": ["return x + 1", {"file": "go/aletheia/client.go"}],
                }
            },
            "rust": "not a block",
        }
    ) == [
        "[go/unobserved_ledger] must be a list of rows",
        "[go/not_covered_ledger] every row must be a mapping",
        "[go/not_covered_ledger] a row must carry a 'file' and a 'text'",
    ]


# main runs every check, each record-reading one on the record it read.

# Each check, in main's order, and whether it reads the record.
_CHECKS: Final = (
    (CheckName("every_block_names_its_tool_and_hot_paths"), True),
    (CheckName("every_tools_importing_test_is_ignored"), False),
    (CheckName("every_above_tree_test_skips_or_is_ignored"), False),
    (CheckName("cpp_slice_weights_are_of_the_domain"), True),
    (CheckName("every_runner_has_a_block"), True),
    (CheckName("ledger_rows_still_name_their_line"), True),
    (CheckName("python_lane_runs_no_doc_harness"), False),
    (CheckName("go_lane_runs_no_doc_harness"), False),
    (CheckName("rust_lane_runs_no_doc_harness"), False),
    (CheckName("cpp_lane_runs_no_doc_harness"), False),
    (CheckName("go_lane_turns_on_the_default_off_mutators"), False),
    (CheckName("cpp_lane_links_the_library_statically"), False),
    (CheckName("every_block_records_its_counts"), True),
)
# The record the stand-in loader returns, held by identity.
_RECORD: Final = {"python": "a block"}


def _stand_in(monkeypatch: pytest.MonkeyPatch, *, failing: bool) -> list[Mock]:
    """Stand ``_RECORD`` and every check in, each returning its own name if ``failing``."""
    monkeypatch.setattr(sys, "argv", ["check_mutation_setup"])
    monkeypatch.setattr(check_mutation_setup, "_load_bindings", Mock(return_value=_RECORD))
    checks: list[Mock] = []
    for name, _reads_record in _CHECKS:
        check = Mock(return_value=[Prose(name)] if failing else [])
        monkeypatch.setattr(check_mutation_setup, name, check)
        checks.append(check)
    return checks


def _each_called_once_as_main_should(checks: list[Mock]) -> None:
    """Hold every check to one call: on the record ``main`` read, or on nothing."""
    for (_name, reads_record), check in zip(_CHECKS, checks, strict=True):
        if reads_record:
            assert check.call_count == 1
            assert len(check.call_args.args) == 1
            assert check.call_args.args[0] is _RECORD
            assert not check.call_args.kwargs
        else:
            check.assert_called_once_with()


def test_main_runs_every_check_and_names_each_failure(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Every check's diagnostic reaches stderr, in order, and the gate exits 1."""
    checks = _stand_in(monkeypatch, failing=True)
    assert check_mutation_setup.main() == 1
    err = capsys.readouterr().err
    assert [line.removeprefix("  - ") for line in err.splitlines() if line.startswith("  - ")] == [
        name for name, _reads_record in _CHECKS
    ]
    assert f"\n{len(_CHECKS)} issue(s) above." in err
    _each_called_once_as_main_should(checks)


def test_main_passes_when_every_check_does(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With every check clean the gate exits 0 and says so on stdout."""
    checks = _stand_in(monkeypatch, failing=False)
    assert check_mutation_setup.main() == 0
    captured = capsys.readouterr()
    assert captured.err == ""
    assert captured.out.startswith("Mutation-setup coverage gate OK: 1 bindings, 0 hot-path ")
    _each_called_once_as_main_should(checks)
