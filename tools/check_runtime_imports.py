# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_runtime_imports.py: the runtime's code reaches no proof the kernel erases.

The runtime's code needs none of these proofs, which its results carry erased
or not at all: that an encodable raw value fits its bits and the range
arithmetic beneath it, the DBC validity theorem and its parts, the size bounds'
proofs, and the AVL membership proofs a name lookup's evidence comes from.
MAlonzo writes a Haskell module for every module Main.agda imports and the
foreign library compiles each of them, but a generated module need not import
every module its Agda module reaches, while each definition of another module
it uses comes through an import of that module.  So the import closure
of the generated Haskell, from the generated modules the shim's own modules
import, holds all the runtime's code can reach, and this check refuses it
reaching one of those proofs, or missing a layer they are about (the signal
value encoder, the validator, the bounds checker, the name lookups).

The shim's modules are those the foreign library's stanza in
``haskell-shim/aletheia.cabal`` lists in ``other-modules`` but MAlonzo's own
(the generated modules, and its runtime, which imports none), each read from
the one ``.hs`` or ``.hsc`` file its name gives under the stanza's
``hs-source-dirs``.  Every import of a generated module is read in the one form
the shim and MAlonzo write, ``import qualified MAlonzo.Code.<module>`` with an
optional ``as <alias>``.  What would cut the closure short is refused
rather than skipped: an import of a generated module in another form, an import
naming no module on its line, which the next could finish with one, a line
holding the word ``import`` other than once at its start, an ``#include`` in a
``.hs`` file (CPP pastes it into the Haskell; in a ``.hsc`` file hsc2hs gives it
to the C program it runs), a stanza line the reader does not read, an
``import`` of a common stanza, a listed module with no such file or two, and a
reached module whose generated file is missing.  A refused proof that neither
``src/`` nor the build holds is refused too, being a row that cannot fire.

Exit codes:
  0: the closure reaches every required layer and none of the refused proofs.
  1: it reaches a refused proof or misses a required layer, or a refused proof
     exists nowhere.
  2: the closure cannot be read: a file it reads is missing or not UTF-8, the
     shim imports no generated module, or it meets one of the refusals above.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import deque
from pathlib import Path
from typing import Literal, NamedTuple, NewType

from tools._common import RelPath, emit

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent
SHIM = RelPath("haskell-shim")
CABAL = RelPath("haskell-shim/aletheia.cabal")
STANZA = "foreign-library aletheia-ffi"
GENERATED = RelPath("build/MAlonzo/Code")
SOURCE = RelPath("src")

HaskellModule = NewType(
    "HaskellModule", str
)  # dotted: `MAlonzo.Code.Aletheia.Error`, `AletheiaFFI`
HaskellSource = NewType("HaskellSource", str)
ImportLine = NewType("ImportLine", str)
CabalText = NewType("CabalText", str)
CabalField = NewType("CabalField", str)  # a field's name, lower-cased: `other-modules`
CabalWord = NewType("CabalWord", str)  # one word of a field's value
Column = NewType("Column", int)
Fields = dict[CabalField, list[CabalWord]]


class ShimSource(NamedTuple):
    """A shim module's source file and its text."""

    path: RelPath
    text: HaskellSource


PASSED, REFUSED, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

_PREFIX = "MAlonzo.Code."
_IMPORT = re.compile(r"import qualified (MAlonzo\.Code\.[\w.']+)(?: as [\w.']+)?")
# Any other import naming its module on its line, as GHC spells one.
_NAMED = re.compile(
    r"""import(?:\s+\{-#\s*SOURCE\s*#-\})?(?:\s+safe)?(?:\s+qualified)?(?:\s+"[^"]*")?"""
    + r"""\s+[A-Z][\w.']*(?:[\s(]|$)"""
)
_WORD = re.compile(r"\bimport\b")
_FOREIGN = re.compile(r"foreign\s+import\b")
_INCLUDE = re.compile(r"#\s*include\b")
_FIELD = re.compile(r"(\s+)([A-Za-z-]+):(.*)")

REQUIRED: tuple[HaskellModule, ...] = (
    HaskellModule("MAlonzo.Code.Aletheia.CAN.Encoding.Value"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Validator"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Bounds"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Validator.Targets"),
)
ERASED_PROOFS: tuple[HaskellModule, ...] = (
    HaskellModule("MAlonzo.Code.Aletheia.CAN.Encoding.Properties.Fits"),
    HaskellModule("MAlonzo.Code.Aletheia.CAN.Encoding.Arithmetic.Range"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Validity.Theorem"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Validity.Composition"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Validity.ErrorChecks"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Validity.WarningChecks"),
    HaskellModule("MAlonzo.Code.Aletheia.DBC.Bounds.Properties"),
    HaskellModule("MAlonzo.Code.Data.Tree.AVL.Sets.Membership.Properties"),
)


def generated_imports(
    text: HaskellSource, *, hsc: bool = False
) -> tuple[list[HaskellModule], list[ImportLine]]:
    """Return the generated modules ``text`` imports, and the lines it holds that are refused.

    A line is refused when it imports a generated module other than as
    ``_IMPORT`` reads, imports a module it does not name, or holds ``import``
    other than once at its start (a line comment and a ``foreign import``
    aside), and, unless ``text`` is hsc2hs source, when it includes a file.
    """
    found: list[HaskellModule] = []
    refused: list[ImportLine] = []
    for line in text.splitlines():
        words = line.strip()
        if words.startswith("--"):
            continue
        if _INCLUDE.match(words):
            if not hsc:
                refused.append(ImportLine(line))
            continue
        if not _WORD.search(words) or _FOREIGN.match(words):
            continue
        if match := _IMPORT.fullmatch(words):
            found.append(HaskellModule(match.group(1)))
        elif _PREFIX in words or not _NAMED.match(words) or len(_WORD.findall(words)) > 1:
            refused.append(ImportLine(line))
    return found, refused


def _stanza_fields(text: CabalText) -> tuple[Fields, Prose | None]:
    """Return the foreign library stanza's fields by name, each a list of words, or why not."""
    lines = [line.rstrip() for line in text.splitlines()]
    if STANZA not in lines:
        return {}, Prose(f"{CABAL} has no `{STANZA}` stanza")
    fields: Fields = {}
    current: list[CabalWord] | None = None
    indent: Column | None = None
    for line in lines[lines.index(STANZA) + 1 :]:
        if not line.strip() or line.strip().startswith("--"):
            continue
        depth = Column(len(line) - len(line.lstrip()))
        if depth == 0:
            break
        indent = indent or depth
        if (field := _FIELD.fullmatch(line)) and depth == indent:
            current = fields.setdefault(CabalField(field.group(2).lower()), [])
            current += [CabalWord(w) for w in field.group(3).replace(",", " ").split()]
        elif current is not None and depth > indent:
            current += [CabalWord(w) for w in line.replace(",", " ").split()]
        else:
            return {}, Prose(f"{CABAL}: a line of the stanza the reader does not read: {line}")
    return fields, None


def _shim_sources(root: Path) -> tuple[list[ShimSource], list[Prose]]:
    """Return the source of each shim module the stanza lists, and what could not be read."""
    fields, why = _stanza_fields(CabalText((root / CABAL).read_text(encoding="utf-8")))
    if why:
        return [], [why]
    if CabalField("import") in fields:
        return [], [Prose(f"{CABAL}: the stanza imports a common stanza the reader does not read")]
    listed = fields.get(CabalField("other-modules"), [])
    modules = [HaskellModule(word) for word in listed if not word.startswith("MAlonzo.")]
    directories = [RelPath(word) for word in fields.get(CabalField("hs-source-dirs"), [])]
    if not modules or not directories:
        return [], [Prose(f"{CABAL}: the stanza lists no shim module or no hs-source-dirs")]
    sources: list[ShimSource] = []
    unreadable: list[Prose] = []
    for module in modules:
        *parents, name = module.split(".")
        candidates = [
            path
            for directory in directories
            for suffix in (".hs", ".hsc")
            if (path := root.joinpath(SHIM, directory, *parents, name + suffix)).is_file()
        ]
        if len(candidates) != 1:
            unreadable.append(
                Prose(f"{module} has {len(candidates)} .hs or .hsc sources under {directories}")
            )
            continue
        path = RelPath(candidates[0].relative_to(root).as_posix())
        sources.append(ShimSource(path, HaskellSource(candidates[0].read_text(encoding="utf-8"))))
    return sources, unreadable


def _path(
    root: Path, base: RelPath, module: HaskellModule, suffix: Literal[".hs", ".agda"]
) -> Path:
    *directories, name = module.removeprefix(_PREFIX).split(".")
    return root.joinpath(base, *directories, name + suffix)


def generated_file(root: Path, module: HaskellModule) -> Path:
    """Return the file MAlonzo writes ``module`` to under ``root``."""
    return _path(root, GENERATED, module, ".hs")


def _exists(root: Path, module: HaskellModule) -> bool:
    """Whether the build or src/ holds ``module``, so that something could import it."""
    return generated_file(root, module).is_file() or _path(root, SOURCE, module, ".agda").is_file()


Reached = dict[HaskellModule, HaskellModule | RelPath]  # each module, from its first importer


def _chain(reached: Reached, module: HaskellModule) -> Prose:
    links: list[HaskellModule | RelPath] = [module]
    while (link := links[-1]) in reached:
        links.append(reached[HaskellModule(link)])
    return Prose(" <- ".join(link.removeprefix(_PREFIX) for link in links))


def _read(
    importer: HaskellModule | RelPath,
    text: HaskellSource,
    reached: Reached,
    pending: deque[HaskellModule],
) -> list[Prose]:
    """Queue the modules ``text`` is first to import, returning the lines it refuses."""
    found, refused = generated_imports(text, hsc=importer.endswith(".hsc"))
    for module in found:
        if module not in reached:
            reached[module] = importer
            pending.append(module)
    return [Prose(f"{importer}: a line the reader refuses: {line}") for line in refused]


def _closure(root: Path) -> tuple[Reached, list[Prose]]:
    """Return every module the shim's generated imports reach, and what could not be read."""
    reached: Reached = {}
    pending: deque[HaskellModule] = deque()
    sources, unreadable = _shim_sources(root)
    for source in sources:
        unreadable += _read(source.path, source.text, reached, pending)
    if not reached and not unreadable:
        unreadable.append(Prose("the shim's modules import no generated module"))
    while pending:
        module = pending.popleft()
        path = generated_file(root, module)
        if path.is_file():
            text = HaskellSource(path.read_text(encoding="utf-8"))
            unreadable += _read(module, text, reached, pending)
        else:
            unreadable.append(Prose(f"{_chain(reached, module)}: no generated file {path}"))
    return reached, unreadable


def run(
    root: Path, required: tuple[HaskellModule, ...], refused: tuple[HaskellModule, ...]
) -> ExitStatus:
    """Walk the generated imports from the shim under ``root`` and return the exit status."""
    try:
        reached, unreadable = _closure(root)
    except (OSError, UnicodeDecodeError) as error:
        reached, unreadable = {}, [Prose(str(error))]
    if unreadable:
        for line in unreadable:
            _ = sys.stderr.write(f"check-runtime-imports: cannot read the closure: {line}\n")
        return UNREADABLE
    failures = [
        Prose(f"{module} exists neither in {SOURCE}/ nor in {GENERATED}/")
        for module in refused
        if not _exists(root, module)
    ]
    failures += [
        Prose(f"the runtime reaches {_chain(reached, m)}") for m in refused if m in reached
    ]
    failures += [Prose(f"the runtime does not reach {m}") for m in required if m not in reached]
    for line in failures:
        _ = sys.stderr.write(f"check-runtime-imports: {line}\n")
    if failures:
        return REFUSED
    emit(
        f"check-runtime-imports: the shim's generated imports reach {len(reached)} modules, "
        + f"the {len(required)} required among them and none of the {len(refused)} erased proofs"
    )
    return PASSED


def main() -> ExitStatus:
    """Refuse a runtime import closure that reaches a proof the kernel uses erased."""
    argparse.ArgumentParser(description=__doc__).parse_args()
    return run(REPO_ROOT, REQUIRED, ERASED_PROOFS)


if __name__ == "__main__":
    sys.exit(main())
