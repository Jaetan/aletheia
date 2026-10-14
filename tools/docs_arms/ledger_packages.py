# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Each table of the building guide's dependency ledger names what the tree's manifests declare.

The manifests are read as the SBOM emitter reads them (``tools._manifests``,
and its Cargo dependency reader), and each table is held to them both ways
but the build-time one:

* ``### Runtime, C++ layer``: the packages ``cpp/CMakeLists.txt`` fetches
  through FetchContent, a ``_fetch`` content name read as its package, against
  the names of the table's first column, a cell naming several between commas
  and ``owner/name`` read as ``name``, case aside;
* ``### Runtime, Go layer``: the modules required directly by the go.mod of
  every module ``go/go.work`` uses, go's indirect requirements and the
  workspace's own modules aside;
* ``### Runtime, Rust layer``: the crates the ``[dependencies]`` tables of
  every tracked ``Cargo.toml`` under ``rust/`` declare, the tree's own crates
  aside, against both tables of the section;
* ``### Runtime, Python layer``: the distributions of the extras
  ``aletheia[all]`` gathers in ``python/pyproject.toml``, each row's extra the
  one its distribution sits under, names compared as PEP 503 normalises them;
* ``### Build-time only``: every ``[build-system]`` requirement, a name of the
  table's first column; this direction alone, since the table's other rows
  are the toolchain, which no manifest lists.

A name a manifest declares and its table lacks is a finding, as is a row naming
what no manifest declares; so is a manifest untracked, unread or holding an
entry its reader cannot read, and a section the guide lacks, since each leaves
a table with nothing to hold it to.
"""

from __future__ import annotations

import tomllib
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NewType, TypedDict, cast

from tools._common import RelPath
from tools._manifests import (
    DistributionName,
    ExtraName,
    FetchName,
    ManifestError,
    ManifestText,
    fetch_declares,
    fetched_package,
    go_module,
    go_requires,
    go_uses,
    normalized,
    requirement,
)
from tools.docs_arms import BUILDING_GUIDE, Unread, missing, read_tracked, section_rows
from tools.sbom_generate import rust_direct_dep

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping, Sequence
    from pathlib import Path

    from tools import _markdown

# A Rust crate's name, as a Cargo manifest spells it.
CrateName = NewType("CrateName", str)

CMAKE = RelPath("cpp/CMakeLists.txt")
GO_WORK = RelPath("go/go.work")
PYPROJECT = RelPath("python/pyproject.toml")
RUST_DIR = PurePosixPath("rust")

CPP_LAYER = Prose("### Runtime, C++ layer")
GO_LAYER = Prose("### Runtime, Go layer")
RUST_LAYER = Prose("### Runtime, Rust layer")
PYTHON_LAYER = Prose("### Runtime, Python layer")
BUILD_TIME = Prose("### Build-time only")

# The extra that gathers the runtime extras, by naming the project with them.
GATHERING_EXTRA = ExtraName("all")

_UNCHECKED = Prose("the dependency ledger's tables are unchecked")
_PYTHON_EXTRA_CELL = 1


class _CargoDependency(TypedDict, total=False):
    package: CrateName
    path: ManifestText
    optional: bool


class _CargoPackage(TypedDict, total=False):
    name: CrateName


class _Cargo(TypedDict, total=False):
    package: _CargoPackage
    dependencies: dict[CrateName, ManifestText | _CargoDependency]


class _BuildSystem(TypedDict, total=False):
    requires: list[ManifestText]


_Project = TypedDict(
    "_Project",
    {"name": DistributionName, "optional-dependencies": dict[ExtraName, list[ManifestText]]},
    total=False,
)
_PyManifest = TypedDict(
    "_PyManifest", {"build-system": _BuildSystem, "project": _Project}, total=False
)


def _read(root: Path, tracked: Sequence[RelPath], rel: RelPath) -> ManifestText | Unread:
    """Return the text of the tracked manifest ``rel``, or the ``Unread`` saying why it has none."""
    if rel not in tracked:
        return Unread(missing(rel, tracked, _UNCHECKED))
    text = read_tracked(root, rel, _UNCHECKED)
    return text if isinstance(text, Unread) else ManifestText(text)


def _first_names(rows: Iterable[_markdown.Row]) -> set[Prose]:
    """Return the names the first cells of ``rows`` hold, a cell naming several between commas."""
    return {Prose(name.strip()) for row in rows for name in row.shown[0].split(",") if name.strip()}


def _compared(layer: Prose, declared: set[Prose], listed: set[Prose]) -> list[Prose]:
    """Return a finding per name ``declared`` the table ``layer`` lacks, then per name it adds."""
    return [
        *(
            Prose(f"{BUILDING_GUIDE}: the {layer} table lacks {name}, which the manifests declare")
            for name in sorted(declared - listed)
        ),
        *(
            Prose(f"{BUILDING_GUIDE}: the {layer} table names {name}, which no manifest declares")
            for name in sorted(listed - declared)
        ),
    ]


def _no_section(heading: Prose) -> list[Prose]:
    """Return the finding for a ledger section the guide lacks."""
    return [Prose(f"{BUILDING_GUIDE}: has no {heading} section")]


def _case_aside(name: FetchName | Prose) -> Prose:
    """Return ``name`` lowered, the form the C++ table and CMake's names are compared in."""
    return Prose(name.lower())


def _cpp(root: Path, tracked: Sequence[RelPath], guide: Prose) -> list[Prose]:
    """Hold the C++ table to the packages CMake fetches."""
    rows = section_rows(guide, CPP_LAYER)
    if rows is None:
        return _no_section(CPP_LAYER)
    text = _read(root, tracked, CMAKE)
    if isinstance(text, Unread):
        return [text.finding]
    try:
        declares = fetch_declares(text, Prose(CMAKE))
    except ManifestError as exc:
        return [Prose(str(exc))]
    fetched = {_case_aside(fetched_package(declare.name)) for declare in declares}
    listed = {_case_aside(Prose(PurePosixPath(name).name)) for name in _first_names(rows)}
    return _compared(CPP_LAYER, fetched, listed)


def _go(root: Path, tracked: Sequence[RelPath], guide: Prose) -> list[Prose]:
    """Hold the Go table to the direct requirements of the workspace's modules."""
    rows = section_rows(guide, GO_LAYER)
    if rows is None:
        return _no_section(GO_LAYER)
    work = _read(root, tracked, GO_WORK)
    if isinstance(work, Unread):
        return [work.finding]
    own: set[Prose] = set()
    required: set[Prose] = set()
    try:
        for use in go_uses(work, Prose(GO_WORK)):
            rel = RelPath((PurePosixPath(GO_WORK).parent / use / "go.mod").as_posix())
            text = _read(root, tracked, rel)
            if isinstance(text, Unread):
                return [text.finding]
            own.add(Prose(go_module(text, Prose(rel))))
            required.update(
                Prose(found.module) for found in go_requires(text, Prose(rel)) if not found.indirect
            )
    except ManifestError as exc:
        return [Prose(str(exc))]
    return _compared(GO_LAYER, required - own, _first_names(rows))


def rust_manifests(tracked: Iterable[RelPath]) -> list[RelPath]:
    """Return every tracked ``Cargo.toml`` under ``rust/``, in the order of ``tracked``."""
    return [
        rel
        for rel in tracked
        if PurePosixPath(rel).name == "Cargo.toml" and RUST_DIR in PurePosixPath(rel).parents
    ]


def _rust(root: Path, tracked: Sequence[RelPath], guide: Prose) -> list[Prose]:
    """Hold the Rust tables to the crates the Cargo manifests declare."""
    rows = section_rows(guide, RUST_LAYER)
    if rows is None:
        return _no_section(RUST_LAYER)
    manifests = rust_manifests(tracked)
    if not manifests:
        return [Prose(f"{RUST_DIR}: tracks no Cargo.toml, so the Rust table is unchecked")]
    own: set[Prose] = set()
    declared: set[Prose] = set()
    for rel in manifests:
        text = _read(root, tracked, rel)
        if isinstance(text, Unread):
            return [text.finding]
        try:
            cargo = cast("_Cargo", tomllib.loads(text))
            own.add(Prose(cargo.get("package", {}).get("name", "")))
            declared.update(
                Prose(rust_direct_dep(key, spec, root / rel)[0])
                for key, spec in cargo.get("dependencies", {}).items()
            )
        except (tomllib.TOMLDecodeError, ManifestError) as exc:
            return [Prose(f"{rel}: cannot be read as a Cargo manifest: {exc}")]
    return _compared(RUST_LAYER, declared - own, _first_names(rows))


def _gathered(project: _Project) -> list[ExtraName] | None:
    """Return the extras the gathering extra names the project with, or None when it names none."""
    own = normalized(project.get("name", DistributionName("")))
    for entry in project.get("optional-dependencies", {}).get(GATHERING_EXTRA, []):
        read = requirement(entry)
        if read is not None and normalized(read.name) == own and read.extras:
            return list(read.extras)
    return None


def _runtime(project: _Project, rows: list[_markdown.Row]) -> list[Prose]:
    """Hold the Python table to the distributions of the runtime extras, each under its extra."""
    extras = _gathered(project)
    if extras is None:
        return [Prose(f"{PYPROJECT}: no [{GATHERING_EXTRA}] extra gathers the runtime extras")]
    out: list[Prose] = []
    under: dict[Prose, ExtraName] = {}
    defined = project.get("optional-dependencies", {})
    for extra in extras:
        for entry in defined.get(extra, []):
            read = requirement(entry)
            if read is None:
                out.append(
                    Prose(f"{PYPROJECT}: cannot read the requirement {entry!r} of [{extra}]")
                )
            else:
                under[Prose(normalized(read.name))] = extra
    listed = {Prose(normalized(DistributionName(row.shown[0]))): row for row in rows}
    out.extend(_compared(PYTHON_LAYER, set(under), set(listed)))
    out.extend(
        Prose(f"{BUILDING_GUIDE}:{listed[name].line}: {name} sits under [{extra}] in {PYPROJECT}")
        for name, extra in sorted(under.items())
        if name in listed
        and listed[name].shown[_PYTHON_EXTRA_CELL : _PYTHON_EXTRA_CELL + 1] != (f"[{extra}]",)
    )
    return out


def _build_time(manifest: _PyManifest, rows: list[_markdown.Row]) -> list[Prose]:
    """Hold the build-time table to every ``[build-system]`` requirement."""
    backend = {Prose(normalized(DistributionName(name))) for name in _first_names(rows)}
    out: list[Prose] = []
    for entry in manifest.get("build-system", {}).get("requires", []):
        read = requirement(entry)
        if read is None:
            out.append(Prose(f"{PYPROJECT}: cannot read the build requirement {entry!r}"))
        elif Prose(normalized(read.name)) not in backend:
            out.append(
                Prose(
                    f"{BUILDING_GUIDE}: the {BUILD_TIME} table lacks {read.name}, "
                    + "a [build-system] requirement"
                )
            )
    return out


def _python(root: Path, tracked: Sequence[RelPath], guide: Prose) -> list[Prose]:
    """Hold the Python table to the runtime extras, and the build-time table to the backend."""
    rows = section_rows(guide, PYTHON_LAYER)
    build_rows = section_rows(guide, BUILD_TIME)
    if rows is None or build_rows is None:
        return _no_section(PYTHON_LAYER if rows is None else BUILD_TIME)
    text = _read(root, tracked, PYPROJECT)
    if isinstance(text, Unread):
        return [text.finding]
    try:
        manifest = cast("_PyManifest", tomllib.loads(text))
    except tomllib.TOMLDecodeError as exc:
        return [Prose(f"{PYPROJECT}: cannot be read as TOML: {exc}")]
    return [*_runtime(manifest.get("project", {}), rows), *_build_time(manifest, build_rows)]


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per name a ledger table and the manifests it lists disagree on.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings of the C++, Go, Rust and Python tables in that order, each
        table's names it lacks then the names it adds, in name order, then a
        Python row's misplaced extra and a build requirement the build-time
        table lacks; for a table, its section missing or its manifest untracked,
        unread or unreadable instead; alone, the guide untracked or unread.

    """
    if BUILDING_GUIDE not in documents:
        return [missing(BUILDING_GUIDE, tracked, _UNCHECKED)]
    guide = documents[BUILDING_GUIDE]
    return [
        *_cpp(root, tracked, guide),
        *_go(root, tracked, guide),
        *_rust(root, tracked, guide),
        *_python(root, tracked, guide),
    ]
