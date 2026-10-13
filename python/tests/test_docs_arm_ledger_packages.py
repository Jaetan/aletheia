# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate's arm holding the building guide's dependency tables to the manifests.

A ledger whose every table names what the manifests declare is clean.  Per
layer, a name a manifest declares and its table lacks is a finding, as is a row
naming what no manifest declares: the C++ table against what CMake fetches (a
``_fetch`` content name read as its package, ``owner/name`` as ``name``, case
aside), the Go table against the direct requirements of the modules go.work
uses (the indirect ones and the workspace's own modules aside), the Rust tables
against every ``[dependencies]`` table under ``rust/`` (the tree's own crates
aside, a renamed dependency read as its package), the Python table against the
extras ``aletheia[all]`` gathers (names PEP 503 normalised, each row under its
own extra, an extra outside ``all`` not held), and the build-time table against
every ``[build-system]`` requirement, in that direction alone.  A section the
guide lacks, a manifest untracked, unread or unreadable, and the guide itself
untracked or unread are findings, each in place of what it leaves unchecked.
"""

from __future__ import annotations

import tomllib
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.ledger_packages import (
    BUILD_TIME,
    CPP_LAYER,
    GO_LAYER,
    PYTHON_LAYER,
    RUST_LAYER,
    findings,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping
    from pathlib import Path

GUIDE = RelPath("docs/development/BUILDING.md")
CMAKE = RelPath("cpp/CMakeLists.txt")
GO_WORK = RelPath("go/go.work")
GO_MOD = RelPath("go/go.mod")
GO_EXCEL_MOD = RelPath("go/excel/go.mod")
CARGO = RelPath("rust/Cargo.toml")
CARGO_EXCEL = RelPath("rust/excel/Cargo.toml")
PYPROJECT = RelPath("python/pyproject.toml")

_UNCHECKED = "the dependency ledger's tables are unchecked"
_PIN = "0123456789abcdef" * 4

_SECTIONS: dict[Prose, Prose] = {
    BUILD_TIME: Prose("""| Dependency | License | Role |
|---|---|---|
| Agda | MIT | Compiler |
| GHC | BSD-3-Clause | Compiler |
| setuptools, wheel | MIT | Python build backend and wheel packaging |
"""),
    CPP_LAYER: Prose("""| Package | License | Purpose |
|---|---|---|
| nlohmann/json | MIT | JSON serialization |
| OpenXLSX | BSD-3-Clause | Excel template loader |
| miniz, pugixml | MIT | OpenXLSX's own dependencies |
"""),
    GO_LAYER: Prose("""| Module | License | Pulled in by |
|---|---|---|
| gopkg.in/yaml.v3 | Apache-2.0, with files under MIT | `go/aletheia` |
| github.com/xuri/excelize/v2 | BSD-3-Clause | `go/excel` |
"""),
    RUST_LAYER: Prose("""| Crate | License | Role |
|---|---|---|
| libloading | ISC | Runtime `dlopen` |
| serde_json | MIT OR Apache-2.0 | JSON protocol |
| yaml-rust2 | MIT OR Apache-2.0 | YAML check-rule loader |
| futures-channel | MIT OR Apache-2.0 | Async reply channel |

The optional crate's own:

| Crate | License | Role |
|---|---|---|
| calamine | MIT | Spreadsheet reader |
"""),
    PYTHON_LAYER: Prose("""| Package | Extra | License |
|---|---|---|
| **python-can** | `[can]` | **LGPL-3.0-only** |
| pyyaml | `[yaml]` | MIT |
| openpyxl | `[excel]` | MIT |
"""),
}


def _guide(drop: Collection[Prose] = ()) -> Prose:
    """Return the building guide holding every ledger section but those headed in ``drop``."""
    body = "".join(
        f"{heading}\n\n{table}\n" for heading, table in _SECTIONS.items() if heading not in drop
    )
    return Prose(f"# Building\n\n## Licences\n\n{body}## Afterwards\n\nNo table here.\n")


_GUIDE = _guide()

_CMAKE_TEXT = Prose(f"""cmake_minimum_required(VERSION 3.25)
include(FetchContent)

FetchContent_Declare(json
    URL https://example.com/json.tar.xz
    URL_HASH SHA256={_PIN})

FetchContent_Declare(openxlsx
    URL https://example.com/openxlsx.tar.gz
    URL_HASH SHA256={_PIN})

FetchContent_Declare(miniz_fetch
    URL https://example.com/miniz.tar.gz
    URL_HASH SHA256={_PIN}
    DOWNLOAD_EXTRACT_TIMESTAMP OFF)

FetchContent_Declare(pugixml_fetch
    URL https://example.com/pugixml.tar.gz
    URL_HASH SHA256={_PIN}
    DOWNLOAD_EXTRACT_TIMESTAMP OFF)
""")

_GO_WORK_TEXT = Prose("""go 1.24.0

use (
\t.
\t./excel
)
""")
_GO_MOD_TEXT = Prose("""module example.com/aletheia/go

go 1.24.0

require gopkg.in/yaml.v3 v3.0.1

require github.com/kr/pretty v0.3.1 // indirect
""")
_GO_EXCEL_MOD_TEXT = Prose("""module example.com/aletheia/go/excel

go 1.24.0

require (
\texample.com/aletheia/go v0.0.0
\tgithub.com/xuri/excelize/v2 v2.9.1
\tgolang.org/x/text v0.21.0 // indirect
)
""")

_CARGO_TEXT = Prose("""[package]
name = "aletheia"
version = "5.0.0"

[dependencies]
libloading = "0.8"
serde_json = "1"
yaml = { package = "yaml-rust2", version = "0.10", optional = true }
futures-channel = { version = "0.3", optional = true }

[dev-dependencies]
futures = "0.3"
""")
_CARGO_EXCEL_TEXT = Prose("""[package]
name = "aletheia-excel"
version = "0.1.0"

[dependencies]
aletheia = { path = ".." }
calamine = "0.26"
""")

_PYPROJECT_TEXT = Prose("""[build-system]
requires = ["setuptools>=68", "wheel"]
build-backend = "setuptools.build_meta"

[project]
name = "aletheia"

[project.optional-dependencies]
can = ["python-can>=4.4"]
yaml = ["PyYAML>=6.0"]
excel = ["openpyxl>=3.1"]
all = ["aletheia[can,yaml,excel]"]
dev = ["pytest>=8", "aletheia[all]"]
""")

_FILES: dict[RelPath, Prose] = {
    GUIDE: _GUIDE,
    CMAKE: _CMAKE_TEXT,
    GO_WORK: _GO_WORK_TEXT,
    GO_MOD: _GO_MOD_TEXT,
    GO_EXCEL_MOD: _GO_EXCEL_MOD_TEXT,
    CARGO: _CARGO_TEXT,
    CARGO_EXCEL: _CARGO_EXCEL_TEXT,
    PYPROJECT: _PYPROJECT_TEXT,
}


def _edited(text: Prose, old: Prose, new: Prose) -> Prose:
    """Return ``text`` with ``old`` replaced by ``new``, refusing an ``old`` it does not hold."""
    assert old in text, f"{old!r} is not in the planted text"
    return Prose(text.replace(old, new))


def _repo(
    tmp_path: Path, edits: Mapping[RelPath, Prose] | None = None, drop: Collection[RelPath] = ()
) -> Path:
    """Plant the ledger's tree, ``edits`` replacing planted files, ``drop`` left out."""
    files = {**_FILES, **(edits or {})}
    return plant(
        tmp_path / "repo", {rel: text for rel, text in files.items() if rel not in drop}
    ).resolve()


def _run(
    repo: Path, *, untracked: Collection[RelPath] = (), absent: Collection[RelPath] = ()
) -> list[Prose]:
    """Run the arm over ``repo`` as the gate runs it, the tracked paths as named."""
    return run_planted(findings, repo, untracked=untracked, absent=absent)


def _lacks(layer: Prose, name: Prose) -> Prose:
    """Return the finding for ``name``, which a manifest declares and the ``layer`` table lacks."""
    return Prose(f"{GUIDE}: the {layer} table lacks {name}, which the manifests declare")


def _names(layer: Prose, name: Prose) -> Prose:
    """Return the finding for ``name``, which the ``layer`` table names and no manifest declares."""
    return Prose(f"{GUIDE}: the {layer} table names {name}, which no manifest declares")


def _misplaced(guide: Prose, row: Prose, name: Prose, extra: Prose) -> Prose:
    """Return the finding for the Python row opening ``row``: ``name`` sits under ``extra``."""
    line = next(i for i, text in enumerate(guide.splitlines(), 1) if text.startswith(row))
    return Prose(f"{GUIDE}:{line}: {name} sits under [{extra}] in {PYPROJECT}")


def _toml_error(text: Prose) -> Prose:
    """Return what tomllib says of ``text``, which is not TOML."""
    with pytest.raises(tomllib.TOMLDecodeError) as caught:
        _ = tomllib.loads(text)
    return Prose(str(caught.value))


def test_a_ledger_naming_what_every_manifest_declares_has_no_finding(tmp_path: Path) -> None:
    """Every table names what its manifests declare, the asides and spellings each layer allows."""
    assert _run(_repo(tmp_path)) == list[Prose]()


@pytest.mark.parametrize(
    ("content", "package"),
    [(Prose("Catch2"), Prose("catch2")), (Prose("zlib_fetch"), Prose("zlib"))],
    ids=["case-lowered", "fetch-suffix"],
)
def test_a_package_cmake_fetches_and_the_cpp_table_lacks_is_a_finding(
    tmp_path: Path, content: Prose, package: Prose
) -> None:
    """A FetchContent declaration no row names is a finding naming its package, lowered."""
    cmake = Prose(
        f"{_CMAKE_TEXT}\nFetchContent_Declare({content}\n"
        + f"    URL https://example.com/x.tar.gz\n    URL_HASH SHA256={_PIN})\n"
    )
    assert _run(_repo(tmp_path, {CMAKE: cmake})) == [_lacks(CPP_LAYER, package)]


def test_a_cpp_row_naming_what_cmake_does_not_fetch_is_a_finding(tmp_path: Path) -> None:
    """A row of the C++ table naming a package nothing fetches is a finding naming it, lowered."""
    guide = _edited(_GUIDE, Prose("| OpenXLSX |"), Prose("| fmt/FMT | MIT | x |\n| OpenXLSX |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == [_names(CPP_LAYER, Prose("fmt"))]


def test_an_owner_cell_is_compared_by_its_name_alone(tmp_path: Path) -> None:
    """``nlohmann/json`` is read as ``json``, so a content name spelling the owner differs."""
    cmake = _edited(
        _CMAKE_TEXT, Prose("FetchContent_Declare(json"), Prose("FetchContent_Declare(nlohmann_json")
    )
    assert _run(_repo(tmp_path, {CMAKE: cmake})) == [
        _lacks(CPP_LAYER, Prose("nlohmann_json")),
        _names(CPP_LAYER, Prose("json")),
    ]


def test_a_cmake_declaration_of_another_shape_is_the_readers_finding(tmp_path: Path) -> None:
    """A FetchContent declaration the reader cannot read is reported in its own words."""
    cmake = Prose(
        f"{_CMAKE_TEXT}\nFetchContent_Declare(Catch2\n"
        + "    GIT_REPOSITORY https://example.com/catch2.git\n    GIT_TAG v3.16.0)\n"
    )
    assert _run(_repo(tmp_path, {CMAKE: cmake})) == [
        Prose(
            "cpp/CMakeLists.txt: found 5 FetchContent_Declare occurrence(s) but read 4 "
            + "(json, openxlsx, miniz_fetch, pugixml_fetch); a declaration of another shape "
            + "would drop out of what the file is read to fetch, so teach the reader its "
            + "shape or fix it"
        )
    ]


def test_a_direct_go_requirement_the_table_lacks_is_a_finding(tmp_path: Path) -> None:
    """A module a used go.mod requires directly and no row names is a finding naming it."""
    go_mod = Prose(f"{_GO_MOD_TEXT}\nrequire github.com/google/uuid v1.6.0\n")
    assert _run(_repo(tmp_path, {GO_MOD: go_mod})) == [
        _lacks(GO_LAYER, Prose("github.com/google/uuid"))
    ]


def test_a_go_row_naming_what_no_go_mod_requires_is_a_finding(tmp_path: Path) -> None:
    """A row of the Go table naming a module no used go.mod requires is a finding naming it."""
    guide = _edited(
        _GUIDE,
        Prose("| gopkg.in/yaml.v3 |"),
        Prose("| github.com/stretchr/testify | MIT | x |\n| gopkg.in/yaml.v3 |"),
    )
    assert _run(_repo(tmp_path, {GUIDE: guide})) == [
        _names(GO_LAYER, Prose("github.com/stretchr/testify"))
    ]


def test_an_indirect_go_requirement_made_direct_is_held(tmp_path: Path) -> None:
    """Only go's indirect mark sets a requirement aside: without it the module is owed a row."""
    go_mod = _edited(
        _GO_MOD_TEXT,
        Prose("github.com/kr/pretty v0.3.1 // indirect"),
        Prose("github.com/kr/pretty v0.3.1"),
    )
    assert _run(_repo(tmp_path, {GO_MOD: go_mod})) == [
        _lacks(GO_LAYER, Prose("github.com/kr/pretty"))
    ]


def test_a_requirement_of_a_module_the_workspace_no_longer_holds_is_held(tmp_path: Path) -> None:
    """The workspace's own modules are set aside: renamed away, the requirement is owed a row."""
    go_mod = _edited(
        _GO_MOD_TEXT,
        Prose("module example.com/aletheia/go\n"),
        Prose("module example.com/other/go\n"),
    )
    assert _run(_repo(tmp_path, {GO_MOD: go_mod})) == [
        _lacks(GO_LAYER, Prose("example.com/aletheia/go"))
    ]


def test_a_module_go_work_does_not_use_is_not_read(tmp_path: Path) -> None:
    """A go.mod the workspace does not use declares nothing, so its module's row names nothing."""
    go_work = _edited(_GO_WORK_TEXT, Prose("\t./excel\n"), Prose(""))
    assert _run(_repo(tmp_path, {GO_WORK: go_work})) == [
        _names(GO_LAYER, Prose("github.com/xuri/excelize/v2"))
    ]


@pytest.mark.parametrize(
    ("rel", "text", "finding"),
    [
        (
            GO_EXCEL_MOD,
            Prose(
                "module example.com/aletheia/go/excel\n\nrequire (\n\tgolang.org/x/text v0.21.0\n"
            ),
            Prose("go/excel/go.mod: unterminated require block"),
        ),
        (GO_WORK, Prose("use ./a ./b\n"), Prose("go/go.work: cannot parse use entry './a ./b'")),
        (
            GO_MOD,
            Prose("go 1.24.0\n\nrequire gopkg.in/yaml.v3 v3.0.1\n"),
            Prose("go/go.mod: declares 0 module directive(s), not one module path"),
        ),
    ],
    ids=["unterminated-block", "bad-use", "no-module"],
)
def test_a_go_entry_the_reader_cannot_read_is_its_finding(
    tmp_path: Path, rel: RelPath, text: Prose, finding: Prose
) -> None:
    """A go.work or go.mod entry the reader refuses is reported in its own words, alone."""
    assert _run(_repo(tmp_path, {rel: text})) == [finding]


def test_a_crate_a_cargo_manifest_declares_and_the_rust_tables_lack_is_a_finding(
    tmp_path: Path,
) -> None:
    """A ``[dependencies]`` crate no row of either Rust table names is a finding naming it."""
    cargo = _edited(
        _CARGO_TEXT, Prose('serde_json = "1"\n'), Prose('serde_json = "1"\nthiserror = "2"\n')
    )
    assert _run(_repo(tmp_path, {CARGO: cargo})) == [_lacks(RUST_LAYER, Prose("thiserror"))]


def test_a_row_of_the_second_rust_table_naming_no_crate_is_a_finding(tmp_path: Path) -> None:
    """The section's second table is held too: a row of it naming no declared crate is a finding."""
    guide = _edited(_GUIDE, Prose("| calamine |"), Prose("| zip | MIT | x |\n| calamine |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == [_names(RUST_LAYER, Prose("zip"))]


def test_a_renamed_dependency_is_read_as_the_package_it_names(tmp_path: Path) -> None:
    """A dependency's ``package`` key is the crate: a row naming the key is held both ways."""
    guide = _edited(_GUIDE, Prose("| yaml-rust2 |"), Prose("| yaml |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == [
        _lacks(RUST_LAYER, Prose("yaml-rust2")),
        _names(RUST_LAYER, Prose("yaml")),
    ]


def test_a_path_dependency_on_a_crate_the_tree_no_longer_holds_is_held(tmp_path: Path) -> None:
    """The tree's own crates are set aside: renamed away, the dependency on it is owed a row."""
    cargo = _edited(_CARGO_TEXT, Prose('name = "aletheia"\n'), Prose('name = "aletheia-core"\n'))
    assert _run(_repo(tmp_path, {CARGO: cargo})) == [_lacks(RUST_LAYER, Prose("aletheia"))]


def test_a_cargo_manifest_outside_rust_is_not_read(tmp_path: Path) -> None:
    """Only a Cargo.toml under ``rust/`` is held: one elsewhere declares nothing the table owes."""
    other = RelPath("fuzz/rust/Cargo.toml")
    cargo = Prose('[package]\nname = "fuzzing"\n\n[dependencies]\narbitrary = "1"\n')
    assert _run(_repo(tmp_path, {other: cargo})) == list[Prose]()


def test_a_tree_tracking_no_cargo_manifest_under_rust_is_a_finding(tmp_path: Path) -> None:
    """With no Cargo.toml under ``rust/`` the Rust tables have nothing to be held to."""
    repo = _repo(tmp_path)
    assert _run(repo, untracked={CARGO, CARGO_EXCEL}) == [
        Prose("rust: tracks no Cargo.toml, so the Rust table is unchecked")
    ]


def test_an_untracked_cargo_manifest_declares_nothing(tmp_path: Path) -> None:
    """A Cargo.toml git does not track is not read, so the rows its crates hold name nothing."""
    assert _run(_repo(tmp_path), untracked={CARGO_EXCEL}) == [_names(RUST_LAYER, Prose("calamine"))]


def test_a_tracked_cargo_manifest_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A Cargo.toml git tracks and the work tree lacks leaves the Rust tables unchecked."""
    repo = _repo(tmp_path, drop={CARGO})
    assert _run(repo, absent={CARGO}) == [Prose(f"{CARGO}: could not be read, so {_UNCHECKED}")]


def test_a_cargo_manifest_that_is_not_toml_is_a_finding(tmp_path: Path) -> None:
    """A Cargo.toml tomllib cannot read is reported with what tomllib says."""
    text = Prose("[package\nname = 1\n")
    assert _run(_repo(tmp_path, {CARGO: text})) == [
        Prose(f"{CARGO}: cannot be read as a Cargo manifest: {_toml_error(text)}")
    ]


def test_a_cargo_dependency_its_reader_refuses_is_a_finding(tmp_path: Path) -> None:
    """A dependency whose ``optional`` is not a boolean is reported in the SBOM reader's words."""
    cargo = _edited(
        _CARGO_TEXT,
        Prose('serde_json = "1"\n'),
        Prose('serde_json = { version = "1", optional = "yes" }\n'),
    )
    repo = _repo(tmp_path, {CARGO: cargo})
    assert _run(repo) == [
        Prose(
            f"{CARGO}: cannot be read as a Cargo manifest: {repo / CARGO}: "
            + "dependencies.serde_json.optional: expected a boolean"
        )
    ]


def test_a_distribution_of_a_gathered_extra_the_table_lacks_is_a_finding(tmp_path: Path) -> None:
    """A distribution an extra ``all`` gathers requires and no row names is a finding naming it."""
    manifest = _edited(
        _PYPROJECT_TEXT,
        Prose('excel = ["openpyxl>=3.1"]'),
        Prose('excel = ["openpyxl>=3.1", "XlsxWriter"]'),
    )
    assert _run(_repo(tmp_path, {PYPROJECT: manifest})) == [
        _lacks(PYTHON_LAYER, Prose("xlsxwriter"))
    ]


def test_a_python_row_naming_no_gathered_distribution_is_a_finding(tmp_path: Path) -> None:
    """A row of the Python table naming what no gathered extra requires is a finding naming it."""
    guide = _edited(_GUIDE, Prose("| openpyxl |"), Prose("| numpy | `[can]` | BSD |\n| openpyxl |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == [_names(PYTHON_LAYER, Prose("numpy"))]


def test_python_names_are_compared_as_pep_503_normalises_them(tmp_path: Path) -> None:
    """A row spelling a distribution with other case and separators still names it."""
    guide = _edited(_GUIDE, Prose("| **python-can** |"), Prose("| **Python_Can** |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == list[Prose]()


def test_a_python_row_under_the_wrong_extra_is_a_finding(tmp_path: Path) -> None:
    """A row whose extra cell is not the extra its distribution sits under names the right one."""
    guide = _edited(_GUIDE, Prose("| pyyaml | `[yaml]` |"), Prose("| pyyaml | `[can]` |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == [
        _misplaced(guide, Prose("| pyyaml |"), Prose("pyyaml"), Prose("yaml"))
    ]


def test_an_extra_outside_all_is_not_held_to_the_table(tmp_path: Path) -> None:
    """A distribution only an extra ``all`` does not gather requires is owed no row."""
    manifest = _edited(
        _PYPROJECT_TEXT,
        Prose('dev = ["pytest>=8", "aletheia[all]"]'),
        Prose('dev = ["pytest>=8", "hypothesis", "aletheia[all]"]\ndocs = ["sphinx"]'),
    )
    assert _run(_repo(tmp_path, {PYPROJECT: manifest})) == list[Prose]()


@pytest.mark.parametrize(
    "gathering",
    [Prose(""), Prose('all = ["other[can,yaml,excel]"]\n'), Prose('all = ["aletheia"]\n')],
    ids=["no-all", "another-project", "no-extras"],
)
def test_a_manifest_whose_all_extra_gathers_no_extra_of_the_project_is_a_finding(
    tmp_path: Path, gathering: Prose
) -> None:
    """Without ``all`` naming the project with extras, the Python table has nothing to hold."""
    manifest = _edited(_PYPROJECT_TEXT, Prose('all = ["aletheia[can,yaml,excel]"]\n'), gathering)
    assert _run(_repo(tmp_path, {PYPROJECT: manifest})) == [
        Prose(f"{PYPROJECT}: no [all] extra gathers the runtime extras")
    ]


def test_a_gathered_requirement_the_reader_cannot_read_is_a_finding(tmp_path: Path) -> None:
    """A requirement of a gathered extra the reader cannot read is named with its extra."""
    manifest = _edited(
        _PYPROJECT_TEXT,
        Prose('can = ["python-can>=4.4"]'),
        Prose('can = ["python-can @ https://x"]'),
    )
    assert _run(_repo(tmp_path, {PYPROJECT: manifest})) == [
        Prose(f"{PYPROJECT}: cannot read the requirement 'python-can @ https://x' of [can]"),
        _names(PYTHON_LAYER, Prose("python-can")),
    ]


def test_a_build_requirement_the_build_time_table_lacks_is_a_finding(tmp_path: Path) -> None:
    """A ``[build-system]`` requirement no build-time row names is a finding, as spelled."""
    manifest = _edited(
        _PYPROJECT_TEXT,
        Prose('requires = ["setuptools>=68", "wheel"]'),
        Prose('requires = ["setuptools>=68", "wheel", "Cython>=3"]'),
    )
    assert _run(_repo(tmp_path, {PYPROJECT: manifest})) == [
        Prose(f"{GUIDE}: the {BUILD_TIME} table lacks Cython, a [build-system] requirement")
    ]


def test_a_build_time_row_no_manifest_lists_is_no_finding(tmp_path: Path) -> None:
    """The build-time table is held in one direction: a toolchain row no manifest lists is fine."""
    guide = _edited(_GUIDE, Prose("| GHC |"), Prose("| Shake | BSD-3-Clause | Build |\n| GHC |"))
    assert _run(_repo(tmp_path, {GUIDE: guide})) == list[Prose]()


def test_a_build_requirement_the_reader_cannot_read_is_a_finding(tmp_path: Path) -> None:
    """A ``[build-system]`` requirement that is not one the reader reads is named."""
    manifest = _edited(
        _PYPROJECT_TEXT,
        Prose('"setuptools>=68", "wheel"'),
        Prose('"setuptools @ https://x", "wheel"'),
    )
    assert _run(_repo(tmp_path, {PYPROJECT: manifest})) == [
        Prose(f"{PYPROJECT}: cannot read the build requirement 'setuptools @ https://x'")
    ]


def test_a_pyproject_that_is_not_toml_is_a_finding(tmp_path: Path) -> None:
    """A pyproject.toml tomllib cannot read is reported with what tomllib says."""
    text = Prose("[project\n")
    assert _run(_repo(tmp_path, {PYPROJECT: text})) == [
        Prose(f"{PYPROJECT}: cannot be read as TOML: {_toml_error(text)}")
    ]


@pytest.mark.parametrize(
    "heading", [CPP_LAYER, GO_LAYER, RUST_LAYER, PYTHON_LAYER, BUILD_TIME], ids=lambda h: h
)
def test_a_ledger_section_the_guide_lacks_is_a_finding(tmp_path: Path, heading: Prose) -> None:
    """A guide without one ledger section has that section's finding in place of its table's."""
    repo = _repo(tmp_path, {GUIDE: _guide(drop={heading})})
    assert _run(repo) == [Prose(f"{GUIDE}: has no {heading} section")]


def test_a_guide_lacking_both_python_sections_names_the_runtime_one(tmp_path: Path) -> None:
    """With the Python and build-time sections both gone, the Python layer's is the one named."""
    repo = _repo(tmp_path, {GUIDE: _guide(drop={PYTHON_LAYER, BUILD_TIME})})
    assert _run(repo) == [Prose(f"{GUIDE}: has no {PYTHON_LAYER} section")]


@pytest.mark.parametrize(
    "manifest", [CMAKE, GO_WORK, GO_MOD, GO_EXCEL_MOD, PYPROJECT], ids=lambda rel: rel
)
def test_an_untracked_manifest_is_a_finding(tmp_path: Path, manifest: RelPath) -> None:
    """A manifest git does not track is absent from a checkout, so its table is unchecked."""
    assert _run(_repo(tmp_path), untracked={manifest}) == [
        Prose(f"{manifest}: not tracked, so {_UNCHECKED}")
    ]


@pytest.mark.parametrize(
    "manifest", [CMAKE, GO_WORK, GO_MOD, GO_EXCEL_MOD, PYPROJECT], ids=lambda rel: rel
)
def test_a_tracked_manifest_the_work_tree_lacks_is_a_finding(
    tmp_path: Path, manifest: RelPath
) -> None:
    """A manifest git tracks and the work tree lacks leaves its table unchecked."""
    repo = _repo(tmp_path, drop={manifest})
    assert _run(repo, absent={manifest}) == [
        Prose(f"{manifest}: could not be read, so {_UNCHECKED}")
    ]


def test_an_untracked_guide_is_the_one_finding(tmp_path: Path) -> None:
    """A guide git does not track leaves every table unchecked, and alone is reported."""
    assert _run(_repo(tmp_path), untracked={GUIDE}) == [
        Prose(f"{GUIDE}: not tracked, so {_UNCHECKED}")
    ]


def test_a_tracked_guide_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A guide git tracks and the work tree lacks is the gate's unread document and the arm's."""
    repo = _repo(tmp_path, drop={GUIDE})
    assert _run(repo, absent={GUIDE}) == [
        Prose(f"{GUIDE}: could not be read, so what it says is unchecked"),
        Prose(f"{GUIDE}: could not be read, so {_UNCHECKED}"),
    ]


def test_the_tables_findings_come_in_the_order_cpp_go_rust_python(tmp_path: Path) -> None:
    """Every table off at once is reported C++, Go, Rust then Python, each lacks before names."""
    guide = _edited(_GUIDE, Prose("| OpenXLSX |"), Prose("| fmt | MIT | x |\n| OpenXLSX |"))
    guide = _edited(
        guide,
        Prose("| gopkg.in/yaml.v3 |"),
        Prose("| gopkg.in/check.v1 | BSD | x |\n| gopkg.in/yaml.v3 |"),
    )
    guide = _edited(guide, Prose("| calamine |"), Prose("| zip | MIT | x |\n| calamine |"))
    guide = _edited(guide, Prose("| pyyaml | `[yaml]` |"), Prose("| pyyaml | `[excel]` |"))
    cmake = Prose(
        f"{_CMAKE_TEXT}\nFetchContent_Declare(Catch2\n"
        + f"    URL https://example.com/x.tar.gz\n    URL_HASH SHA256={_PIN})\n"
    )
    go_mod = Prose(f"{_GO_MOD_TEXT}\nrequire github.com/google/uuid v1.6.0\n")
    cargo = _edited(
        _CARGO_TEXT, Prose('serde_json = "1"\n'), Prose('serde_json = "1"\nthiserror = "2"\n')
    )
    manifest = _edited(
        _PYPROJECT_TEXT,
        Prose('requires = ["setuptools>=68", "wheel"]'),
        Prose('requires = ["setuptools>=68", "wheel", "Cython>=3"]'),
    )
    manifest = _edited(
        manifest,
        Prose('excel = ["openpyxl>=3.1"]'),
        Prose('excel = ["openpyxl>=3.1", "XlsxWriter"]'),
    )
    edits = {GUIDE: guide, CMAKE: cmake, GO_MOD: go_mod, CARGO: cargo, PYPROJECT: manifest}
    assert _run(_repo(tmp_path, edits)) == [
        _lacks(CPP_LAYER, Prose("catch2")),
        _names(CPP_LAYER, Prose("fmt")),
        _lacks(GO_LAYER, Prose("github.com/google/uuid")),
        _names(GO_LAYER, Prose("gopkg.in/check.v1")),
        _lacks(RUST_LAYER, Prose("thiserror")),
        _names(RUST_LAYER, Prose("zip")),
        _lacks(PYTHON_LAYER, Prose("xlsxwriter")),
        _misplaced(guide, Prose("| pyyaml |"), Prose("pyyaml"), Prose("yaml")),
        Prose(f"{GUIDE}: the {BUILD_TIME} table lacks Cython, a [build-system] requirement"),
    ]
