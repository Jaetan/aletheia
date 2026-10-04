# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_wire_code_emitters.py — every wire code names a constructor the runtime builds.

Each kernel wire vocabulary is spelled by one formatter arm per constructor:
``parseErrorCode (MissingField _) = "parse_missing_field"``, ``boundKindCode
NestingDepth = "nesting_depth"``, ``extractionErrorCodeToℕ NotInDBC = 0`` for
the binary wire's u8 reason codes, and so on.  A constructor nothing in the
runtime builds gives a code no response can carry, a dead word every binding
still mirrors.  This check reads the generated Haskell (``build/MAlonzo``,
written by ``cabal run shake -- build``) rather than the Agda source, because
there types and proofs are erased: a constructor applied under ``coe`` is a
construction, one heading a case alternative is a match, and a lemma's
statement leaves no trace.

Strategy:

1. For each formatter in ``FORMATTERS``, read its arms in the Agda source: the
   constructor and the literal code it returns.  An arm whose right-hand side
   is a call (``InContext``, a family wrapper) carries no code of its own.
2. Map each constructor to its generated name (``C_<name>_<n>``) from the data
   declaration in the generated module of the constructor's Agda module.
3. Over every generated ``Aletheia`` module of the runtime closure
   (``haskell-shim/runtime-closure.snapshot``), with data declarations
   removed, count the occurrences of each generated name that are not a
   pattern: an occurrence is a pattern when no ``coe`` precedes it and what
   follows it, through variables, wildcards, parentheses and nested
   constructors, is the alternative's ``->``.
4. Fail naming every constructor with no construction.

Exit codes:
  0 — every wire code's constructor has a construction.
  1 — at least one has none.
  2 — the generated tree, the snapshot or a formatter could not be read.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NewType

from tools._common import emit

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent

AgdaModule = NewType("AgdaModule", str)  # dotted, as in `Aletheia.Error`
FunctionName = NewType("FunctionName", str)
TypeName = NewType("TypeName", str)
ConstructorName = NewType("ConstructorName", str)  # as written in Agda
GeneratedName = NewType("GeneratedName", str)  # as MAlonzo spells it, `C_<name>_<n>`
WireCode = NewType("WireCode", str)  # the literal an arm returns, `u8 <n>` for a number
SourceText = NewType("SourceText", str)
Occurrences = NewType("Occurrences", int)

CLEAN, UNBUILT, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)
NO_HINT = Prose("")


@dataclass(frozen=True)
class Formatter:
    """A wire-code formatter, the data type it reads, and both modules."""

    module: AgdaModule
    function: FunctionName
    data_type: TypeName
    data_module: AgdaModule


FORMATTERS: tuple[Formatter, ...] = (
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("parseErrorCode"),
        TypeName("ParseError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("extractionErrorCode"),
        TypeName("ExtractionError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("frameErrorCode"),
        TypeName("FrameError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("routeErrorCode"),
        TypeName("RouteError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("handlerErrorCode"),
        TypeName("HandlerError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("dispatchErrorCode"),
        TypeName("DispatchError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("dbcTextParseErrorCode"),
        TypeName("DBCTextParseError"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Error"),
        FunctionName("errorCode"),
        TypeName("Error"),
        AgdaModule("Aletheia.Error"),
    ),
    Formatter(
        AgdaModule("Aletheia.Limits"),
        FunctionName("boundKindCode"),
        TypeName("BoundKind"),
        AgdaModule("Aletheia.Limits"),
    ),
    Formatter(
        AgdaModule("Aletheia.Protocol.ResponseFormat"),
        FunctionName("formatIssueCode"),
        TypeName("IssueCode"),
        AgdaModule("Aletheia.DBC.Types"),
    ),
    Formatter(
        AgdaModule("Aletheia.CAN.BatchExtraction"),
        FunctionName("extractionErrorCodeToℕ"),
        TypeName("ExtractionErrorCode"),
        AgdaModule("Aletheia.CAN.BatchExtraction"),
    ),
)


@dataclass(frozen=True)
class Code:
    """One wire code and the constructor its formatter arm reads."""

    formatter: Formatter
    constructor: ConstructorName
    code: WireCode


@dataclass(frozen=True)
class Tree:
    """Where the inputs live: the Agda sources, the generated Haskell, the closure snapshot."""

    src: Path
    generated: Path
    snapshot: Path

    @classmethod
    def of_repo(cls, root: Path) -> Tree:
        """Return the inputs of a checkout rooted at ``root``."""
        return cls(
            root / "src",
            root / "build" / "MAlonzo" / "Code",
            root / "haskell-shim" / "runtime-closure.snapshot",
        )


class ReadError(Exception):
    """An input this check depends on is missing or not in the expected shape."""


def _module_file(root: Path, module: AgdaModule, suffix: Prose) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(suffix)


def _read(path: Path, hint: Prose = NO_HINT) -> SourceText:
    try:
        return SourceText(path.read_text(encoding="utf-8"))
    except OSError as exc:
        msg = f"cannot read {path}{hint}: {exc}"
        raise ReadError(msg) from exc


def formatter_codes(tree: Tree, formatter: Formatter) -> list[Code]:
    """Return the constructor and literal code of every arm of one formatter."""
    path = _module_file(tree.src, formatter.module, Prose(".agda"))
    arm = re.compile(
        rf"^{re.escape(formatter.function)}\s+(?:\((\w+)[^)]*\)|(\w+))"
        + r"\s*=\s*(?:\"([a-z0-9_]+)\"|(\d+))\s*$",
        re.MULTILINE,
    )
    codes = [
        Code(
            formatter,
            ConstructorName(m.group(1) or m.group(2)),
            WireCode(m.group(3) or f"u8 {m.group(4)}"),
        )
        for m in arm.finditer(_read(path))
    ]
    if not codes:
        msg = f"no literal arms of {formatter.function} in {path}"
        raise ReadError(msg)
    return codes


def generated_names(tree: Tree, formatter: Formatter) -> dict[ConstructorName, GeneratedName]:
    """Each constructor of the formatter's data type, mapped to its generated name."""
    path = _module_file(tree.generated, formatter.data_module, Prose(".hs"))
    text = _read(path, Prose(" (run `cabal run shake -- build` first)"))
    block = re.search(
        rf"^data T_{re.escape(formatter.data_type)}_\d+\n((?:[ \t].*\n)*)", text, re.MULTILINE
    )
    if block is None:
        msg = f"no `data T_{formatter.data_type}_<n>` in {path}"
        raise ReadError(msg)
    return {
        ConstructorName(m.group(1)): GeneratedName(m.group(0))
        for m in re.finditer(r"\bC_([A-Za-z0-9']+(?:_[A-Za-z0-9']+)*?)_\d+\b", block.group(1))
    }


_PATTERN_TAIL = re.compile(r"(?:\s|\(|\)|\bv\d+\b|\b_\b|(?:[\w']+\.)*C_[\w']+)*->")
_COE_BEFORE = re.compile(r"\bcoe[\s(]*$")
_QUALIFIER = re.compile(r"(?:[\w']+\.)+$")


def constructions(name: GeneratedName, text: SourceText) -> Occurrences:
    """Occurrences of a generated constructor in one module that build a value."""
    count = 0
    for m in re.finditer(rf"(?<![\w']){re.escape(name)}(?![\w'])", text):
        before = _QUALIFIER.sub("", text[max(0, m.start() - 128) : m.start()])
        if _COE_BEFORE.search(before) or not _PATTERN_TAIL.match(text, m.end()):
            count += 1
    return Occurrences(count)


def without_data_declarations(text: SourceText) -> SourceText:
    """Return the module with every data declaration removed."""
    return SourceText(re.sub(r"^data .*\n(?:[ \t].*\n)*", "", text, flags=re.MULTILINE))


def runtime_modules(tree: Tree) -> dict[Path, SourceText]:
    """Return the runtime closure's generated `Aletheia` modules, data declarations removed."""
    prefix = "MAlonzo.Code."
    modules = [
        AgdaModule(m.removeprefix(prefix))
        for m in str(_read(tree.snapshot)).split()
        if m.startswith(prefix + "Aletheia")
    ]
    if not modules:
        msg = f"no Aletheia modules listed in {tree.snapshot}"
        raise ReadError(msg)
    paths = [_module_file(tree.generated, module, Prose(".hs")) for module in modules]
    return {
        p: without_data_declarations(_read(p, Prose(" (run `cabal run shake -- build` first)")))
        for p in paths
    }


def unbuilt(
    tree: Tree, formatters: tuple[Formatter, ...] = FORMATTERS
) -> tuple[list[Code], list[Code]]:
    """Every wire code read, and those whose constructor no runtime module builds."""
    codes = [code for formatter in formatters for code in formatter_codes(tree, formatter)]
    names = {formatter: generated_names(tree, formatter) for formatter in formatters}
    modules = runtime_modules(tree)
    dead: list[Code] = []
    for code in codes:
        name = names[code.formatter].get(code.constructor)
        if name is None:
            msg = (
                f"{code.constructor} (arm of {code.formatter.function}) "
                + f"is not a constructor of {code.formatter.data_type}"
            )
            raise ReadError(msg)
        if not any(constructions(name, text) for text in modules.values()):
            dead.append(code)
    return codes, dead


def run(tree: Tree, formatters: tuple[Formatter, ...] = FORMATTERS) -> ExitStatus:
    """Run the check over one tree and return its exit status."""
    try:
        codes, dead = unbuilt(tree, formatters)
    except ReadError as exc:
        sys.stderr.write(f"check-wire-code-emitters: {exc}\n")
        return UNREADABLE
    if dead:
        sys.stderr.write(
            "check-wire-code-emitters: wire codes whose constructor the runtime never builds:\n"
        )
        for code in dead:
            sys.stderr.write(f"  - {code.code} ({code.formatter.data_type}.{code.constructor})\n")
        return UNBUILT
    emit(
        f"check-wire-code-emitters: all {len(codes)} wire codes have a construction "
        + "in the runtime closure"
    )
    return CLEAN


def main() -> ExitStatus:
    """Fail when a wire code names a constructor the runtime never builds."""
    argparse.ArgumentParser(description=__doc__).parse_args()
    return run(Tree.of_repo(REPO_ROOT))


if __name__ == "__main__":
    sys.exit(main())
