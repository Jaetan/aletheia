# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Python-test checks of ``tools.check_mutation_setup``, invariants 2 and 3.

Each test plants a ``python/tests`` and a ``[tool.mutmut]`` in a scratch tree,
the module's paths monkeypatched to it, and compares the diagnostics whole: a
test whose collection may import the repository's ``tools``, or that reads
above ``python/`` and cannot skip, is named unless mutmut ignores it.  The
walker's tables hold what collection is read as running, what it is read as
not running, and the forms the walker states it leaves unread.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING, Final, NewType

import pytest
from _gate_exit import stderr_of_exit_2
from _planted_tree import plant

from tools import check_mutation_setup
from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence
    from pathlib import Path

# A file's name under ``python/tests``.
TestFile = NewType("TestFile", str)

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
            Prose("try:\n    import tools\nexcept* ImportError:\n    pass\n"),
            id="a try body under except*",
        ),
        pytest.param(
            Prose("try:\n    import os\nexcept ImportError:\n    import tools\n"), id="a handler"
        ),
        pytest.param(
            Prose("try:\n    import os\nexcept ImportError:\n    pass\nelse:\n    import tools\n"),
            id="the else of a try",
        ),
        pytest.param(
            Prose(
                "from typing import TYPE_CHECKING\nif TYPE_CHECKING:\n    pass\nelse:\n"
                + "    import tools\n"
            ),
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
                "import pytest\ndef f():\n    import tools\n@pytest.mark.skipif(f())\n"
                + "def test_x():\n    pass\n"
            ),
            id="a function called in a decorator's arguments",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(x=f()):\n    pass\n"),
            id="a function called in a default argument",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(x: f() = 1) -> None:\n    pass\n"),
            id="a test's annotation",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x() -> f():\n    pass\n"),
            id="a test's return annotation",
        ),
        pytest.param(
            Prose("def test_x(x: __import__('tools') = 1) -> None:\n    pass\n"),
            id="an import a test's annotation names",
        ),
        pytest.param(
            Prose("def f():\n    import tools\nasync def test_x(x: f() = 1) -> None:\n    pass\n"),
            id="a coroutine test's annotation",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass TestT:\n    def test_x(self, x: f() = 1):\n"
                + "        pass\n"
            ),
            id="a test method's annotation",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass TestT:\n    class TestU:\n"
                + "        def test_x(self, x: f() = 1):\n            pass\n"
            ),
            id="a nested test class's test",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nif True:\n    def test_x(x: f() = 1):\n        pass\n"
            ),
            id="a test defined under an if",
        ),
        pytest.param(
            Prose(
                "import pytest\ndef f():\n    import tools\n@pytest.fixture\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="a fixture's annotation",
        ),
        pytest.param(
            Prose(
                "from pytest import fixture\ndef f():\n    import tools\n"
                + "@fixture(scope='module')\ndef x() -> f():\n    return 1\n"
            ),
            id="a fixture called with arguments",
        ),
        pytest.param(
            Prose(
                "import pytest\ndef f():\n    import tools\nclass TestT:\n"
                + "    @pytest.fixture\n    def x(self, y: f() = 1):\n        return y\n"
            ),
            id="a test class's fixture",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass TestT:\n    def __init__(self):\n        pass\n"
                + "    def test_x(self, x: f() = 1):\n        pass\n"
            ),
            id="a test class pytest passes over",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass TestT:\n    __test__ = False\n"
                + "    def test_x(self, x: f() = 1):\n        pass\n"
            ),
            id="a test class whose __test__ is False",
        ),
        pytest.param(
            Prose(
                "__test__ = False\ndef f():\n    import tools\n"
                + "def test_x(x: f() = 1):\n    pass\n"
            ),
            id="a test module whose __test__ is False",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef test_x(x: f() = 1):\n    pass\n"
                + "test_x.__test__ = False\n"
            ),
            id="a test whose __test__ is False",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(x: f(), /):\n    pass\n"),
            id="a positional-only parameter's annotation",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(*x: f()):\n    pass\n"),
            id="a variadic parameter's annotation",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(*, x: f() = 1):\n    pass\n"),
            id="a keyword-only parameter's annotation",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x(**x: f()):\n    pass\n"),
            id="a keywords parameter's annotation",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\n"
                + "def pytest_generate_tests(metafunc: f()):\n    pass\n"
                + "def test_x():\n    pass\n"
            ),
            id="a hook's annotation",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef pytest_configure(config: f()):\n    pass\n"),
            id="a hook pytest does not call",
        ),
        pytest.param(
            Prose(
                "from pytest import fixture as fx\ndef f():\n    import tools\n@fx\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="a fixture under another name",
        ),
        pytest.param(
            Prose(
                "from __future__ import generator_stop\ndef f():\n    import tools\n"
                + "def test_x(x: f() = 1):\n    pass\n"
            ),
            id="a test's annotation beside another future import",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef test_x(x: f() = 1):\n    pass\n"
                + "def test_x():\n    pass\n"
            ),
            id="a test a later one hides",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef test_x(x: f() = 1):\n    pass\n" + "del test_x\n"
            ),
            id="a test del removes",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef d(g):\n    return d\n@d\n"
                + "def test_x(x: f() = 1):\n    pass\n"
            ),
            id="a test a decorator replaces",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef fixture(g):\n    return g\n@fixture\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="a decorator spelled fixture that is not pytest's",
        ),
        pytest.param(
            Prose(
                "import unittest\ndef f():\n    import tools\n"
                + "class TestT(unittest.TestCase):\n    def test_x(self, x: f() = 1):\n"
                + "        pass\n"
            ),
            id="a unittest test class's test",
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
    """An import of ``tools`` collection may run is named: every branch is read as running."""
    _plant_python_tests(tmp_path, monkeypatch, {_TEST: source})
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(_TEST)
    ]


def test_annotations_another_module_exports_postpone_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Only ``from __future__ import annotations`` postpones a test's annotations."""
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            _TEST: Prose(
                "from _notes import annotations\ndef f():\n    import tools\n"
                + "def test_x(x: f() = 1):\n    pass\n"
            ),
            TestFile("_notes.py"): Prose("annotations = 1\n"),
        },
    )
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
            Prose(
                "from _other import fixture as fx\ndef f():\n    import tools\n@fx\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="a fixture alias another module binds",
        ),
        pytest.param(
            Prose(
                "from pytest import hookimpl as fx\ndef f():\n    import tools\n@fx\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="another pytest name under an alias",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef d(g):\n    return g\n@d\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="a function another name decorates",
        ),
        pytest.param(
            Prose(
                "import functools\ndef f():\n    import tools\n@functools.cache\n"
                + "def x(y: f() = 1):\n    return y\n"
            ),
            id="a function another attribute decorates",
        ),
        pytest.param(
            Prose("def f():\n    pass\nclass T:\n    def f(self):\n        import tools\nf()\n"),
            id="a method sharing a module function's name",
        ),
        pytest.param(
            Prose("def g():\n    h()\nclass T:\n    def h():\n        import tools\n    g()\n"),
            id="a name the called function's own scope lacks",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef g(x: f() = 1) -> f():\n    pass\n"),
            id="a module function's annotation",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass TestT:\n    def g(self, x: f() = 1):\n"
                + "        pass\n"
            ),
            id="a test class's other method's annotation",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass T:\n    def test_x(self, x: f() = 1):\n"
                + "        pass\n"
            ),
            id="a test in a class pytest does not collect",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\nclass T:\n    @pytest.fixture\n"
                + "    def x(self, y: f() = 1):\n        return y\n"
            ),
            id="a fixture in a class pytest does not collect",
        ),
        pytest.param(
            Prose(
                "def f():\n    import tools\ndef g():\n    def test_x(x: f() = 1):\n        pass\n"
                + "g()\n"
            ),
            id="a test a called function defines",
        ),
        pytest.param(
            Prose(
                "from __future__ import annotations\n"
                + "def f():\n    import tools\ndef test_x(x: f() = 1) -> f():\n    pass\n"
            ),
            id="a test's annotation the module postpones",
        ),
        pytest.param(
            Prose(
                "from __future__ import annotations\ndef f():\n    import tools\n"
                + "class TestT:\n    def test_x(self, x: f() = 1):\n        pass\n"
            ),
            id="a test method's annotation the module postpones",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ndef test_x[T: f()](x: T):\n    pass\n"),
            id="a type parameter's bound",
        ),
        pytest.param(
            Prose("def f():\n    import tools\ntype X = f()\n"), id="a type alias's value"
        ),
        pytest.param(
            Prose(
                "class T:\n    def h():\n        import tools\n    def g():\n"
                + "        h()\n    g()\n"
            ),
            id="a class body's name a method calls",
        ),
        pytest.param(
            Prose(
                "class T:\n    def h():\n        import tools\n    if True:\n        def g():\n"
                + "            h()\n    g()\n"
            ),
            id="a class body's name a method under an if calls",
        ),
        pytest.param(Prose("__import__('.check', 'tools')\n"), id="__import__'s second argument"),
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


@pytest.mark.parametrize(
    "files",
    [
        pytest.param(
            {_TEST: Prose("def f():\n    import tools\n(lambda: f())()\n")},
            id="a lambda called",
        ),
        pytest.param(
            {_TEST: Prose("def f():\n    import tools\nX = list(f() for _ in [1])\n")},
            id="a generator expression consumed",
        ),
        pytest.param(
            {_TEST: Prose("import asyncio\nasync def f():\n    import tools\nasyncio.run(f())\n")},
            id="a coroutine driven",
        ),
        pytest.param(
            {_TEST: Prose("class C:\n    def __init__(self):\n        import tools\nC()\n")},
            id="a class constructed",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "class T:\n    @staticmethod\n    def f():\n        import tools\nT.f()\n"
                )
            },
            id="a call through an attribute",
        ),
        pytest.param(
            {_TEST: Prose("def f():\n    import tools\ng = f\ng()\n")},
            id="a call through another name",
        ),
        pytest.param(
            {
                _TEST: Prose("from _helper import f\nf()\n"),
                TestFile("_helper.py"): Prose("def f():\n    import tools\n"),
            },
            id="a helper's function",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "def f():\n    import tools\ndef g(x: f() = 1):\n    pass\ntest_x = g\n"
                )
            },
            id="a function bound to a test's name",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "def f():\n    import tools\nclass Base:\n"
                    + "    def test_x(self, x: f() = 1):\n        pass\nclass TestT(Base):\n"
                    + "    pass\n"
                )
            },
            id="an inherited test",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "def f():\n    import tools\nclass _T:\n"
                    + "    def test_x(self, x: f() = 1):\n        pass\nTestT = _T\n"
                )
            },
            id="a class bound to a test class's name",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "def f():\n    import tools\ndef make():\n    class TestT:\n"
                    + "        def test_x(self, x: f() = 1):\n            pass\n"
                    + "    return TestT\nTestT = make()\n"
                )
            },
            id="a test class a called function builds",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "import pytest\ndef f():\n    import tools\ndef g() -> f():\n"
                    + "    return 1\nx = pytest.fixture(g)\n"
                )
            },
            id="a fixture a call makes",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "class B:\n    def __init_subclass__(cls):\n        import tools\n"
                    + "class C(B):\n    pass\n"
                )
            },
            id="a subclass hook",
        ),
        pytest.param(
            {
                _TEST: Prose(
                    "import pytest\nimport unittest\ndef f():\n    import tools\n"
                    + "class T(unittest.TestCase):\n    @pytest.fixture\n"
                    + "    def x(self, y: f() = 1):\n        return y\n"
                )
            },
            id="a fixture of a unittest class otherwise named",
        ),
        pytest.param(
            {_TEST: Prose("exec('import tools')\n")},
            id="exec",
        ),
        pytest.param(
            {_TEST: Prose("eval(\"__import__('tools')\")\n")},
            id="eval",
        ),
    ],
)
def test_a_form_the_walker_leaves_unread_is_not_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, files: Mapping[TestFile, Prose]
) -> None:
    """A form the walker states it leaves unread is not named, though its import runs.

    Python or pytest runs each one's import at collection: teaching the walker
    one turns this red, and the walker's docstring moves with it.
    """
    _plant_python_tests(tmp_path, monkeypatch, files)
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


def test_a_relative_import_in_a_helper_package_is_read_in_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A helper package's relative import names a module of that package; above its top, none."""
    _plant_python_tests(
        tmp_path,
        monkeypatch,
        {
            TestFile("test_a.py"): Prose("import _hr\n"),
            TestFile("test_b.py"): Prose("import _hq.deep\n"),
            TestFile("test_c.py"): Prose("import _hs\n"),
            TestFile("test_d.py"): Prose("import _hq.inner.deep\n"),
            TestFile("test_e.py"): Prose("import _hq.inner.up\n"),
            TestFile("_hr/__init__.py"): Prose("from . import sub\n"),
            TestFile("_hr/sub.py"): Prose("import tools\n"),
            TestFile("_hq/__init__.py"): Prose(""),
            TestFile("_hq/deep.py"): Prose("from .sub import x\n"),
            TestFile("_hq/sub.py"): Prose("import tools\n"),
            TestFile("_hs/__init__.py"): Prose("from .. import tools\n"),
            TestFile("_hq/inner/__init__.py"): Prose(""),
            TestFile("_hq/inner/deep.py"): Prose("from .leaf import x\n"),
            TestFile("_hq/inner/leaf.py"): Prose("import tools\n"),
            TestFile("_hq/inner/up.py"): Prose("from .. import sub\n"),
        },
    )
    assert check_mutation_setup.every_tools_importing_test_is_ignored() == [
        _not_ignored_import(
            TestFile("test_a.py"), Prose(" through tests/_hr/__init__.py, tests/_hr/sub.py")
        ),
        _not_ignored_import(
            TestFile("test_b.py"), Prose(" through tests/_hq/deep.py, tests/_hq/sub.py")
        ),
        _not_ignored_import(
            TestFile("test_d.py"),
            Prose(" through tests/_hq/inner/deep.py, tests/_hq/inner/leaf.py"),
        ),
        _not_ignored_import(
            TestFile("test_e.py"), Prose(" through tests/_hq/inner/up.py, tests/_hq/sub.py")
        ),
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
