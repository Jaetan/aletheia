# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every runnable Python file parses its arguments, so ``--help`` describes it and runs nothing.

A program that reads no argument takes ``--help``, or a mistyped flag, as
nothing and does its job: a mutation sweep, the git hooks installed, minutes
of work where the reader asked what the tool does.  An ``argparse`` parser
answers ``--help`` with its description and refuses an argument it does not
know with exit 2.  A file is runnable when its module body holds an
``if __name__ == "__main__":`` block, and it parses its arguments when it
calls a parser's ``parse_args`` or ``parse_known_args``.  The exemptions hand
their arguments to another parser, or read them by position, where ``--help``
names nothing they can use and they exit non-zero; ``.archive/`` holds review
records no lane runs.
"""

from __future__ import annotations

import ast
from typing import TYPE_CHECKING, Final

from tools._common import RelPath, git_ls_files, git_toplevel

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

_REPO: Final = git_toplevel()

# Every runnable file that reads its arguments without a parser of its own, and why.
_EXEMPT: Final[dict[RelPath, Prose]] = {
    RelPath("benchmarks/compare.py"): Prose(
        "its arguments are result files: --help names none it can read, so it exits 1"
    ),
    RelPath("python/tests/_residency_child.py"): Prose(
        "a test's child: --help alone stops on the missing second argument"
    ),
    RelPath("python/tests/fuzz/fuzz_dbc_to_json.py"): Prose("libFuzzer parses its flags"),
    RelPath("python/tests/fuzz/fuzz_iter_can_log.py"): Prose("libFuzzer parses its flags"),
    RelPath("python/tests/fuzz/fuzz_parse_response.py"): Prose("libFuzzer parses its flags"),
    RelPath("tools/_guarded_run.py"): Prose(
        "its first argument is a list of descriptors, which --help is not"
    ),
    RelPath("tools/warm_check_properties.py"): Prose(
        "its arguments are modules: --help is one agda cannot load, so it exits 1"
    ),
}

_PARSE_CALLS: Final = frozenset({"parse_args", "parse_known_args"})


def _is_runnable(module: ast.Module) -> bool:
    """Say whether the module body holds an ``if __name__ == "__main__":`` block."""
    for node in module.body:
        if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare):
            continue
        sides = [node.test.left, *node.test.comparators]
        names = {side.id for side in sides if isinstance(side, ast.Name)}
        values = {side.value for side in sides if isinstance(side, ast.Constant)}
        if names == {"__name__"} and values == {"__main__"}:
            return True
    return False


def _parses_arguments(module: ast.Module) -> bool:
    """Say whether the module calls a parser's ``parse_args`` or ``parse_known_args``."""
    return any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in _PARSE_CALLS
        for node in ast.walk(module)
    )


def _findings(
    modules: Mapping[RelPath, ast.Module], exempt: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Name each runnable file without a parser, and each exemption no file needs."""
    found: list[Prose] = []
    runnable: set[RelPath] = set()
    for rel, module in sorted(modules.items()):
        if not _is_runnable(module):
            continue
        runnable.add(rel)
        parses = _parses_arguments(module)
        if rel in exempt and parses:
            found.append(Prose(f"{rel}: exempt, yet it parses its arguments: drop its row"))
        elif rel not in exempt and not parses:
            found.append(Prose(f"{rel}: runs on any argument, --help included: give it a parser"))
    found.extend(
        Prose(f"{rel}: exempt, yet no runnable file of the tree: drop its row")
        for rel in sorted(set(exempt) - runnable)
    )
    return found


def test_every_runnable_file_parses_its_arguments() -> None:
    """Over the tracked tree, every runnable file parses its arguments or has an exemption."""
    files = [rel for rel in git_ls_files(_REPO, "*.py") if not rel.startswith(".archive/")]
    modules = {rel: ast.parse((_REPO / rel).read_text(encoding="utf-8"), rel) for rel in files}
    assert not _findings(modules, _EXEMPT)


_RUNS: Final = 'import sys\n\nif __name__ == "__main__":\n    sys.exit(0)\n'
_PARSES: Final = (
    'import argparse\n\nif __name__ == "__main__":\n    argparse.ArgumentParser().parse_args()\n'
)


def test_a_runnable_file_without_a_parser_is_named() -> None:
    """A parser named in a comment or a string does not count; a library file is not runnable."""
    modules = {
        RelPath("bare.py"): ast.parse(_RUNS),
        RelPath("comment.py"): ast.parse(_RUNS + "# p.parse_args()\nNOTE = 'p.parse_args()'\n"),
        RelPath("library.py"): ast.parse("def main() -> int:\n    return 0\n"),
        RelPath("parses.py"): ast.parse(_PARSES),
        RelPath("known.py"): ast.parse(_PARSES.replace("parse_args", "parse_known_args")),
        RelPath("reversed.py"): ast.parse(
            _RUNS.replace('__name__ == "__main__"', '"__main__" == __name__')
        ),
    }
    assert _findings(modules, {}) == [
        "bare.py: runs on any argument, --help included: give it a parser",
        "comment.py: runs on any argument, --help included: give it a parser",
        "reversed.py: runs on any argument, --help included: give it a parser",
    ]


def test_a_main_block_in_a_string_or_a_function_makes_no_runnable_file() -> None:
    """A hook body a file writes out, or a block nested in a function, is not the file's own."""
    nested = "def run() -> None:\n" + "".join(f"    {line}\n" for line in _RUNS.splitlines())
    modules = {
        RelPath("template.py"): ast.parse(f'HOOK = """\n{_RUNS}"""\n'),
        RelPath("nested.py"): ast.parse(nested),
    }
    assert not _findings(modules, {})


def test_an_exemption_no_file_needs_is_named() -> None:
    """A row for a file that parses its arguments, or for no runnable file, is stale."""
    modules = {RelPath("bare.py"): ast.parse(_RUNS), RelPath("parses.py"): ast.parse(_PARSES)}
    exempt = {
        RelPath("bare.py"): Prose("reads its arguments by hand"),
        RelPath("parses.py"): Prose("parses them after all"),
        RelPath("gone.py"): Prose("was deleted"),
    }
    assert _findings(modules, exempt) == [
        "parses.py: exempt, yet it parses its arguments: drop its row",
        "gone.py: exempt, yet no runnable file of the tree: drop its row",
    ]
