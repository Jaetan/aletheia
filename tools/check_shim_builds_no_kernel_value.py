# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_shim_builds_no_kernel_value.py — the Haskell shim builds no kernel value.

Every kernel value carries the invariants its type states (a CAN ID's range, a
DLC's bound, a frame's byte range, a rational's normal form), and the kernel's
parsers are what decide them.  A MAlonzo constructor applied in the shim would
build such a value with its proof assumed rather than decided, so the shim
hands the kernel builtins only (Integer, Bool, lists, Maybe, Text) and names a
generated constructor only to read a result: in a pattern, heading a case
alternative, a lambda or a function clause.  This check fails on every other
occurrence of a generated constructor (``C_<name>_<n>``) in
``haskell-shim/src``.

An occurrence is a pattern when the text before it on its line holds only
names, parentheses, wildcards and a lambda's backslash, or ends in a lambda's
backslash and its parentheses, and what follows it on
the same line, through variables, wildcards, parentheses and nested
constructors, is the ``->`` of an alternative or lambda or the ``=`` of a
clause.  Comments are removed first.

Exit codes:
  0 — every generated constructor the shim names is in a pattern.
  1 — at least one is applied.
  2 — no shim source was found, or none names a generated constructor (a
      renamed import would read as a clean shim).
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NewType

from tools._common import emit

from aletheia.common_types import ExitStatus

HaskellSource = NewType("HaskellSource", str)
GeneratedName = NewType(
    "GeneratedName", str
)  # as MAlonzo spells it, `C_<name>_<n>`, maybe qualified
LineNumber = NewType("LineNumber", int)

BUILDS_NONE, BUILDS, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

REPO_ROOT = Path(__file__).resolve().parent.parent
SHIM_SRC = REPO_ROOT / "haskell-shim" / "src"

_CONSTRUCTOR = re.compile(r"(?<![\w'])(?:[A-Z][\w']*\.)*C_[\w']+")
_KEYWORDS = r"(?:where|let|in|do|of|case|if|then|else)\b"
_HEAD = re.compile(r"[ \t\w'.()\\]*")
_LAMBDA = re.compile(r"\\[ \t(]*$")
_TAIL = re.compile(
    rf"(?:[ \t]|\(|\)|\b(?!{_KEYWORDS})[a-z_][\w']*\b|(?:[A-Z][\w']*\.)*C_[\w']+)*(?:->|=(?!=))"
)


@dataclass(frozen=True)
class Construction:
    """A generated constructor the shim applies: where, and which."""

    path: Path
    line: LineNumber
    name: GeneratedName


def without_comments(text: HaskellSource) -> HaskellSource:
    """Blank the line and block comments, keeping line numbers."""
    blanked = re.sub(
        r"\{-.*?-\}", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.DOTALL
    )
    return HaskellSource(re.sub(r"--[^\n]*", "", blanked))


def constructions(path: Path, text: HaskellSource) -> list[Construction]:
    """Return the applied generated constructors in one source."""
    code = str(without_comments(text))
    found: list[Construction] = []
    for m in _CONSTRUCTOR.finditer(code):
        line_start = code.rfind("\n", 0, m.start()) + 1
        head = code[line_start : m.start()]
        if (_HEAD.fullmatch(head) or _LAMBDA.search(head)) and _TAIL.match(code, m.end()):
            continue
        found.append(
            Construction(
                path, LineNumber(code.count("\n", 0, m.start()) + 1), GeneratedName(m.group(0))
            )
        )
    return found


def run(shim_src: Path) -> ExitStatus:
    """Run the check over one shim tree and return its exit status."""
    sources = sorted([*shim_src.rglob("*.hs"), *shim_src.rglob("*.hsc")])
    if not sources:
        sys.stderr.write(f"check-shim-builds-no-kernel-value: no Haskell source under {shim_src}\n")
        return UNREADABLE
    texts = {p: HaskellSource(p.read_text(encoding="utf-8")) for p in sources}
    if not any(_CONSTRUCTOR.search(without_comments(t)) for t in texts.values()):
        sys.stderr.write(
            f"check-shim-builds-no-kernel-value: no generated constructor named under {shim_src}\n"
        )
        return UNREADABLE
    applied = [c for p, t in texts.items() for c in constructions(p, t)]
    for c in applied:
        sys.stderr.write(
            f"check-shim-builds-no-kernel-value: {c.path}:{c.line}: "
            + f"{c.name} is applied, not matched\n"
        )
    if applied:
        return BUILDS
    emit(
        f"check-shim-builds-no-kernel-value: {len(sources)} shim sources name "
        + "generated constructors only in patterns"
    )
    return BUILDS_NONE


def main() -> ExitStatus:
    """Fail when the shim applies a generated constructor."""
    argparse.ArgumentParser(description=__doc__).parse_args()
    return run(SHIM_SRC)


if __name__ == "__main__":
    sys.exit(main())
