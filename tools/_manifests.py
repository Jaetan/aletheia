# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The readers of the bindings' dependency manifests, each manifest read one way.

The SBOM emitter (``tools/sbom_generate.py``) bills what the manifests declare,
and the documentation gate's ledger arm holds the building guide's tables to
them, so both read a go.mod ``require``, a FetchContent declaration and a PEP 508
requirement here.  An entry a reader cannot read raises ``ManifestError`` naming
where it is, rather than dropping out of what the manifest is read to declare.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple, NewType

if TYPE_CHECKING:
    from aletheia.common_types import Prose

# The text of a manifest, or of one of its lines, as the work tree gives it.
ManifestText = NewType("ManifestText", str)
# A Go module path and a module version, as a go.mod spells them, and a module
# directory a go.work uses, relative to the go.work.
GoModule = NewType("GoModule", str)
GoVersion = NewType("GoVersion", str)
GoUse = NewType("GoUse", str)
# A FetchContent content name, the URL it fetches and the SHA-256 that pins it.
FetchName = NewType("FetchName", str)
FetchUrl = NewType("FetchUrl", str)
FetchSha256 = NewType("FetchSha256", str)
# A Python distribution's name as a requirement spells it, an extra of it, and
# the version specifier beside it, empty when there is none.
DistributionName = NewType("DistributionName", str)
ExtraName = NewType("ExtraName", str)
VersionSpec = NewType("VersionSpec", str)


class ManifestError(Exception):
    """A binding manifest is missing or carries an entry its reader cannot read."""


class GoRequire(NamedTuple):
    """One ``require`` of a go.mod: the module, its version, and whether go marks it indirect."""

    module: GoModule
    version: GoVersion
    indirect: bool


class FetchDeclare(NamedTuple):
    """One FetchContent declaration: its content name, its URL and the SHA-256 pinning it."""

    name: FetchName
    url: FetchUrl
    sha256: FetchSha256


class Requirement(NamedTuple):
    """The distribution a PEP 508 requirement names, the extras it asks for and its specifier."""

    name: DistributionName
    extras: tuple[ExtraName, ...]
    spec: VersionSpec


class _Entry(NamedTuple):
    """One entry of a go.mod or go.work directive: as written, its fields unquoted, its comment."""

    text: ManifestText
    fields: tuple[ManifestText, ...]
    note: ManifestText


_GO_REQUIRE_FIELDS = 2  # "<module> <version>"
# A field go reads as a string: in double quotes or in backquotes.
_GO_QUOTED = re.compile(r'"([^"]*)"|`([^`]*)`')

# The one FetchContent shape the C++ binding uses: URL + URL_HASH SHA256=.
_FETCH_DECLARE = re.compile(
    r"FetchContent_Declare\(\s*([A-Za-z0-9_-]+)"
    + r'\s+URL\s+(?:"([^"]+)"|(\S+))'
    + r"\s+URL_HASH\s+SHA256=([0-9a-fA-F]{64})\b"
)
_FETCH_OPENING = re.compile(r"FetchContent_Declare\s*\(")

# A dependency that fetches its own dependencies is pinned first, under the
# content name that dependency's helper expects, which appends `_fetch`.
_FETCH_NAME_SUFFIX = "_fetch"

# A PEP 508 requirement head: name, optional [extras], optional version spec.
# Environment markers (``; ...``) are not matched: none of the binding's
# requirements carry one, and an entry the pattern does not match is refused by
# its caller rather than misread.
_REQUIREMENT = re.compile(
    r"^(?P<name>[A-Za-z0-9](?:[A-Za-z0-9._-]*[A-Za-z0-9])?)"
    + r"(?:\[(?P<extras>[^\]]+)\])?"
    + r"(?P<spec>\s*[<>=!~][^;]*)?$"
)


def _entry(text: ManifestText, note: ManifestText) -> _Entry:
    """Return the entry ``text`` with its fields, each quoted one read as the string it quotes."""
    fields = tuple(
        ManifestText(next((group for group in quoted.groups() if group is not None), word))
        if (quoted := _GO_QUOTED.fullmatch(word))
        else ManifestText(word)
        for word in text.split()
    )
    return _Entry(text, fields, note)


def _entries(text: ManifestText, verb: ManifestText, context: Prose) -> list[_Entry]:
    """Return every entry of the directive ``verb`` in the go.mod or go.work ``text``.

    The single-line form and the block form are both read, as go reads them: the
    verb is apart from its entry by any blank, and from a block's ``(`` by any or
    none.  A ``//`` comment ends each line's entry.  A block never closed, or the
    verb alone on its line, raises ``ManifestError`` naming ``context``.
    """
    opening = re.compile(rf"{re.escape(verb)}\s*\(")
    entries: list[_Entry] = []
    in_block = False
    for raw in text.splitlines():
        code, _, note = raw.partition("//")
        line = code.strip()
        if not line:
            continue
        words = line.split(None, 1)
        if in_block:
            if line == ")":
                in_block = False
            else:
                entries.append(_entry(ManifestText(line), ManifestText(note)))
        elif opening.fullmatch(line):
            in_block = True
        elif words[0] == verb:
            if len(words) == 1:
                message = f"{context}: a {verb} directive names no entry"
                raise ManifestError(message)
            entries.append(_entry(ManifestText(words[1]), ManifestText(note)))
    if in_block:
        message = f"{context}: unterminated {verb} block"
        raise ManifestError(message)
    return entries


def _go_require(entry: _Entry, context: Prose) -> GoRequire:
    """Read one require entry and the comment after it, or raise naming ``context``.

    The comment marks the entry indirect as go's own reader decides: its fields
    are ``indirect`` alone, or open on ``indirect;`` with more after it.
    """
    parts = entry.fields
    if len(parts) != _GO_REQUIRE_FIELDS or not parts[1].startswith("v"):
        message = f"{context}: cannot parse require entry {entry.text!r}"
        raise ManifestError(message)
    fields = entry.note.split()
    indirect = fields == ["indirect"] or (len(fields) > 1 and fields[0] == "indirect;")
    return GoRequire(GoModule(parts[0]), GoVersion(parts[1]), indirect)


def go_requires(text: ManifestText, context: Prose) -> list[GoRequire]:
    """Return every ``require`` of the go.mod ``text``, each read for go's indirect mark.

    An entry that is not a module and a version, or a block never closed,
    raises ``ManifestError`` naming ``context``.
    """
    return [
        _go_require(entry, context) for entry in _entries(text, ManifestText("require"), context)
    ]


def go_module(text: ManifestText, context: Prose) -> GoModule:
    """Return the module path the go.mod ``text`` declares, raising unless it declares one."""
    paths = [entry.fields for entry in _entries(text, ManifestText("module"), context)]
    match paths:
        case [(path,)]:
            return GoModule(path)
        case _:
            message = f"{context}: declares {len(paths)} module directive(s), not one module path"
            raise ManifestError(message)


def go_uses(text: ManifestText, context: Prose) -> list[GoUse]:
    """Return every module directory the go.work ``text`` uses, raising on an entry not one path."""
    uses: list[GoUse] = []
    for entry in _entries(text, ManifestText("use"), context):
        match entry.fields:
            case (path,):
                uses.append(GoUse(path))
            case _:
                message = f"{context}: cannot parse use entry {entry.text!r}"
                raise ManifestError(message)
    return uses


def fetch_declares(text: ManifestText, context: Prose) -> list[FetchDeclare]:
    """Return every FetchContent declaration of the CMake ``text``, in order.

    A line whose first character after blanks is ``#`` is a comment, as CMake
    reads it, and is not read; a quoted ``URL`` is read as the string it quotes.
    Each declaration must read as the ``URL`` + ``URL_HASH SHA256=`` shape: the
    declarations read are counted against every ``FetchContent_Declare(`` the
    text opens, so one in another shape raises ``ManifestError`` naming
    ``context`` rather than dropping a pin.
    """
    code = "\n".join(line for line in text.splitlines() if not line.lstrip().startswith("#"))
    declares = [
        FetchDeclare(FetchName(found[1]), FetchUrl(found[2] or found[3]), FetchSha256(found[4]))
        for found in _FETCH_DECLARE.finditer(code)
    ]
    total = len(_FETCH_OPENING.findall(code))
    if len(declares) != total:
        parsed = ", ".join(declare.name for declare in declares) or "none"
        message = (
            f"{context}: found {total} FetchContent_Declare occurrence(s) but read "
            f"{len(declares)} ({parsed}); a declaration of another shape would drop out "
            "of what the file is read to fetch, so teach the reader its shape or fix it"
        )
        raise ManifestError(message)
    return declares


def fetched_package(name: FetchName) -> FetchName:
    """Return the package behind the FetchContent content name ``name``."""
    return FetchName(name.removesuffix(_FETCH_NAME_SUFFIX))


def requirement(entry: ManifestText) -> Requirement | None:
    """Return what the PEP 508 requirement ``entry`` names and states, or None if it is none."""
    found = _REQUIREMENT.match(entry.strip())
    if found is None:
        return None
    extras = tuple(
        ExtraName(extra.strip()) for extra in (found["extras"] or "").split(",") if extra.strip()
    )
    return Requirement(
        DistributionName(found["name"]), extras, VersionSpec((found["spec"] or "").strip())
    )


def normalized(name: DistributionName) -> DistributionName:
    """Return ``name`` as PEP 503 normalises it: lowered, a run of ``-``, ``_``, ``.`` one ``-``."""
    return DistributionName(re.sub(r"[-_.]+", "-", name).lower())
