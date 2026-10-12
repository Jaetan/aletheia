# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_proof_coverage.py — proof-gate exhaustiveness gate.

Every Agda module under ``src/`` must be type-checked by one of the two
dedicated type-checking gates:

  * ``build``            — type-checks Main.agda's runtime closure (the .so).
  * ``check-properties`` — type-checks the ``proofModules`` walk roots
    (``shake/Rules/Proofs.hs``) and everything they transitively import.

A module in NEITHER closure is type-checked only as a side effect of the
whole-tree ``iwyu --all`` import pass — so it is silently skipped by the
documented proof gate (``cabal run shake -- check-properties``), and a broken
proof in it would pass a local proof run.  This gate fails when any such module
exists, forcing it into ``proofModules`` (or, for a runtime module, onto Main's
import path).

``proofModules`` is read straight from the build program (``Shakefile.hs`` and
the modules under ``shake/``), the single source of truth, with no second copy
to drift.

Exit codes:
  0 — every src module is covered by ``build`` and ``check-properties``.
  1 — one or more modules are covered only by the ``iwyu --all`` backstop.
  2 — usage / parse error (the ``proofModules`` block could not be parsed).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tools._common import emit, read_shake_program

SRC = Path("src")

# The .so is compiled from Main plus the two Main submodules the FFI shim drives
# (Main.JSON / Main.Binary); their import closure is the runtime surface that
# `cabal run shake -- build` type-checks.
BUILD_ROOTS = ("Aletheia.Main", "Aletheia.Main.JSON", "Aletheia.Main.Binary")

PARSE_ERROR_EXIT = 2

_IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([\w.]+)", re.MULTILINE)
_PROOFMOD_RE = re.compile(r'"(Aletheia/[\w/]+\.agda)"')
_LIST_END = "\n    ]\n"
_DEFINITION_RE = re.compile(r"^proofModules =", re.MULTILINE)


def _findall(pattern: re.Pattern[str], text: str) -> list[str]:
    """`pattern.findall` narrowed to ``list[str]`` (one capture group, so each match is a str)."""
    return pattern.findall(text)


def _module_of(path: Path) -> str:
    return ".".join(path.relative_to(SRC).with_suffix("").parts)


def _proof_roots(text: str) -> list[str]:
    """Parse the ``proofModules`` list entries (as module names) from the build program.

    The list runs from its definition, which the program holds once, to the
    first line closing a bracket at its indent; a module path quoted anywhere
    after it is not a root.  No roots are read when there is no single list.
    """
    definitions = [match.start() for match in _DEFINITION_RE.finditer(text)]
    if len(definitions) != 1:
        return []
    start = definitions[0]
    end = text.find(_LIST_END, start)
    if end < 0:
        return []
    return [entry[:-5].replace("/", ".") for entry in _findall(_PROOFMOD_RE, text[start:end])]


def _closure(roots: set[str], edges: dict[str, set[str]]) -> set[str]:
    """Transitive import closure of ``roots`` over the intra-src import graph."""
    seen: set[str] = set()
    stack = [r for r in roots if r in edges]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        stack.extend(edges[node])
    return seen


def main() -> int:
    """Fail when a src module is covered by neither ``build`` nor ``check-properties``."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    files = sorted(SRC.rglob("*.agda"))
    modules = {_module_of(p): p for p in files}
    modset = set(modules)
    edges: dict[str, set[str]] = {
        name: {
            dep for dep in _findall(_IMPORT_RE, path.read_text(encoding="utf-8")) if dep in modset
        }
        for name, path in modules.items()
    }

    try:
        program = read_shake_program(Path())
    except OSError as exc:
        _ = sys.stderr.write(f"check-proof-coverage: cannot read the build program: {exc}\n")
        return PARSE_ERROR_EXIT
    roots = _proof_roots(program)
    if not roots:
        _ = sys.stderr.write(
            "check-proof-coverage: could not parse one proofModules list from the build program\n"
        )
        return PARSE_ERROR_EXIT
    unknown = [r for r in roots if r not in modset]
    if unknown:
        _ = sys.stderr.write(
            "check-proof-coverage: proofModules lists module(s) with no source file:\n"
            + "".join(f"  {r}\n" for r in unknown)
        )
        return PARSE_ERROR_EXIT

    covered = _closure(set(roots), edges) | _closure(set(BUILD_ROOTS), edges)
    gap = sorted(modset - covered)
    if gap:
        _ = sys.stderr.write(
            "check-proof-coverage: FAIL — module(s) type-checked only by the "
            + "iwyu --all backstop, not by check-properties or build:\n\n"
            + "".join(f"  {m}\n" for m in gap)
            + "\nAdd each to `proofModules` in shake/Rules/Proofs.hs (or, for a runtime "
            + "module, make it reachable from Aletheia.Main).\n"
        )
        return 1

    emit(
        f"check-proof-coverage: ok ({len(modset)} modules; "
        + "all covered by build and check-properties)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
