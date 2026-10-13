# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the binding-manifest readers (``tools/_manifests.py``).

A go.mod ``require`` is read in its single-line and block forms, marked
indirect exactly as go's own modfile reader marks it; a ``module`` directive
yields its one path and a go.work its ``use`` directories; a FetchContent
declaration is read only in the ``URL`` + ``URL_HASH SHA256=`` shape, in order;
a PEP 508 requirement yields its name, extras and specifier.  Every entry a
reader cannot read, and every block never closed, raises ``ManifestError``
naming the manifest it came from, with the message asserted whole.  The tests
marked as defects show a manifest go or CMake reads one way and the reader
another, each spelling checked against the tool's own reading.
"""

from __future__ import annotations

import pytest

from tools._manifests import (
    DistributionName,
    ExtraName,
    FetchDeclare,
    FetchName,
    FetchSha256,
    FetchUrl,
    GoModule,
    GoRequire,
    GoUse,
    GoVersion,
    ManifestError,
    ManifestText,
    Requirement,
    VersionSpec,
    fetch_declares,
    fetched_package,
    go_module,
    go_requires,
    go_uses,
    normalized,
    requirement,
)

from aletheia.common_types import Prose

_GO_MOD = Prose("go/go.mod")
_GO_WORK = Prose("go.work")
_CMAKE = Prose("cpp/CMakeLists.txt")

_NOT_ONE_PATH = "module directive(s), not one module path"

_JSON_SHA = FetchSha256("0123456789abcdef" * 4)
_YAML_SHA = FetchSha256("FEDCBA9876543210" * 4)

_JSON_DECLARE = (
    "FetchContent_Declare(json\n"
    + "  URL https://example.com/json.tar.xz\n"
    + f"  URL_HASH SHA256={_JSON_SHA}\n"
    + ")\n"
)
_YAML_DECLARE = (
    "FetchContent_Declare(\n"
    + "  yaml-cpp_fetch\n"
    + "  URL https://example.com/yaml-cpp.tar.gz\n"
    + f"  URL_HASH SHA256={_YAML_SHA}\n"
    + "  DOWNLOAD_EXTRACT_TIMESTAMP TRUE\n"
    + ")\n"
)

_JSON = FetchDeclare(FetchName("json"), FetchUrl("https://example.com/json.tar.xz"), _JSON_SHA)
_YAML = FetchDeclare(
    FetchName("yaml-cpp_fetch"), FetchUrl("https://example.com/yaml-cpp.tar.gz"), _YAML_SHA
)

_REFUSAL = (
    "; a declaration of another shape would drop out "
    + "of what the file is read to fetch, so teach the reader its shape or fix it"
)


def _require(module: GoModule, version: GoVersion, *, indirect: bool) -> GoRequire:
    """Build the require the reader is expected to return."""
    return GoRequire(module, version, indirect)


def _requirement(
    name: DistributionName, extras: tuple[ExtraName, ...], spec: VersionSpec
) -> Requirement:
    """Build the requirement the reader is expected to return."""
    return Requirement(name, extras, spec)


def test_a_single_line_require_is_read() -> None:
    """A ``require <module> <version>`` line yields that module at that version, direct."""
    text = ManifestText("module example.com/m\n\ngo 1.26\n\nrequire example.com/a v1.2.3\n")
    assert go_requires(text, _GO_MOD) == [
        _require(GoModule("example.com/a"), GoVersion("v1.2.3"), indirect=False)
    ]


def test_a_require_block_is_read_in_order_past_blank_and_comment_lines() -> None:
    """Every entry of a ``require (`` block is read, in order; blank and comment lines are not."""
    text = ManifestText(
        "module example.com/m\n"
        + "\n"
        + "require ( // the direct dependencies\n"
        + "\texample.com/a v1.0.0\n"
        + "\n"
        + "\t// a comment line is no entry\n"
        + "\texample.com/b\tv2.0.0+incompatible // indirect\n"
        + ")\n"
        + "\n"
        + "require example.com/c v0.1.0\n"
    )
    assert go_requires(text, _GO_MOD) == [
        _require(GoModule("example.com/a"), GoVersion("v1.0.0"), indirect=False),
        _require(GoModule("example.com/b"), GoVersion("v2.0.0+incompatible"), indirect=True),
        _require(GoModule("example.com/c"), GoVersion("v0.1.0"), indirect=False),
    ]


def test_a_go_mod_without_requires_reads_none() -> None:
    """The other directives and blocks of a go.mod are not read as requires."""
    text = ManifestText(
        "module example.com/m\n"
        + "\n"
        + "go 1.26\n"
        + "toolchain go1.26.0\n"
        + "\n"
        + "exclude (\n"
        + "\texample.com/a v1.0.0\n"
        + ")\n"
        + "\n"
        + "replace example.com/b v1.0.0 => ../b\n"
    )
    assert go_requires(text, _GO_MOD) == []


@pytest.mark.parametrize(
    ("comment", "expected"),
    [
        (
            ManifestText(comment),
            _require(GoModule("example.com/a"), GoVersion("v1.0.0"), indirect=indirect),
        )
        for comment, indirect in [
            (" // indirect", True),
            (" //indirect", True),
            (" //   indirect   ", True),
            (" // indirect; why it is kept", True),
            (" // indirect;", False),
            (" // indirectly", False),
            (" // direct", False),
            (" // indirect // more", False),
            (" // why; indirect", False),
            ("", False),
        ]
    ],
)
def test_the_indirect_mark_is_read_as_go_reads_it(
    comment: ManifestText, expected: GoRequire
) -> None:
    """The comment is ``indirect`` alone, or opens on ``indirect;`` with more after it."""
    single = ManifestText(f"require example.com/a v1.0.0{comment}\n")
    block = ManifestText(f"require (\n\texample.com/a v1.0.0{comment}\n)\n")
    assert go_requires(single, _GO_MOD) == [expected]
    assert go_requires(block, _GO_MOD) == [expected]


def test_a_directive_naming_no_entry_raises_naming_the_manifest() -> None:
    """The verb alone on its line is no entry, and go refuses it; so does the reader."""
    with pytest.raises(ManifestError) as caught:
        go_requires(ManifestText("module example.com/m\n\nrequire\n"), _GO_MOD)
    assert str(caught.value) == "go/go.mod: a require directive names no entry"


def test_an_unterminated_require_block_raises_naming_the_manifest() -> None:
    """A ``require (`` never closed raises rather than reading the rest of the file as entries."""
    text = ManifestText("module example.com/m\n\nrequire (\n\texample.com/a v1.0.0\n")
    with pytest.raises(ManifestError) as caught:
        go_requires(text, _GO_MOD)
    assert str(caught.value) == "go/go.mod: unterminated require block"


@pytest.mark.parametrize(
    ("text", "entry"),
    [
        (ManifestText(text), ManifestText(entry))
        for text, entry in [
            ("require example.com/a\n", "example.com/a"),
            ("require example.com/a v1.0.0 extra\n", "example.com/a v1.0.0 extra"),
            ("require example.com/a 1.0.0\n", "example.com/a 1.0.0"),
            ("require (\n\texample.com/a\n)\n", "example.com/a"),
            ("require (\n\texample.com/a 1.0.0 // indirect\n)\n", "example.com/a 1.0.0"),
        ]
    ],
)
def test_a_require_entry_not_a_module_and_a_version_raises_naming_it(
    text: ManifestText, entry: ManifestText
) -> None:
    """One field, three fields or a version not opening on ``v`` raises, quoting the entry."""
    with pytest.raises(ManifestError) as caught:
        go_requires(text, _GO_MOD)
    assert str(caught.value) == f"go/go.mod: cannot parse require entry {entry!r}"


def test_go_module_returns_the_one_module_path() -> None:
    """The ``module`` directive's path is returned, its trailing comment dropped."""
    text = ManifestText(
        "// the binding\nmodule github.com/example/aletheia/go // the module\n\ngo 1.26\n"
    )
    assert go_module(text, _GO_MOD) == GoModule("github.com/example/aletheia/go")


@pytest.mark.parametrize(
    ("text", "message"),
    [
        (ManifestText(text), Prose(f"go/go.mod: declares {count} {_NOT_ONE_PATH}"))
        for text, count in [
            ("go 1.26\n\nrequire example.com/a v1.0.0\n", 0),
            ("", 0),
            ("module example.com/m\nmodule example.com/n\n", 2),
            ("module example.com/m example.com/n\n", 1),
        ]
    ],
)
def test_go_module_raises_unless_one_directive_names_one_path(
    text: ManifestText, message: Prose
) -> None:
    """No module directive, two of them, or one naming two paths raises, counting the directives."""
    with pytest.raises(ManifestError) as caught:
        go_module(text, _GO_MOD)
    assert str(caught.value) == message


def test_an_unterminated_module_block_raises_naming_the_manifest() -> None:
    """A ``module (`` never closed raises rather than counting as no module directive."""
    with pytest.raises(ManifestError) as caught:
        go_module(ManifestText("module (\n\texample.com/m\n"), _GO_MOD)
    assert str(caught.value) == "go/go.mod: unterminated module block"


def test_go_uses_reads_the_single_line_and_the_block_form_in_order() -> None:
    """Every ``use`` directory is read, single-line and block entries alike, in file order."""
    text = ManifestText(
        "go 1.26\n"
        + "\n"
        + "use ./go // the binding\n"
        + "\n"
        + "use (\n"
        + "\t./go/excel\n"
        + "\t// a comment line is no entry\n"
        + "\t./examples/go\n"
        + ")\n"
    )
    assert go_uses(text, _GO_WORK) == [GoUse("./go"), GoUse("./go/excel"), GoUse("./examples/go")]


def test_a_go_work_without_uses_reads_none() -> None:
    """A go.work that uses no directory reads as none, its other directives unread."""
    no_uses: list[GoUse] = []
    text = ManifestText("go 1.26\n\nreplace example.com/a => ./a\n")
    assert go_uses(text, _GO_WORK) == no_uses


@pytest.mark.parametrize(
    ("text", "entry"),
    [
        (ManifestText(text), ManifestText(entry))
        for text, entry in [
            ("use ./a ./b\n", "./a ./b"),
            ("use (\n\t./a ./b\n)\n", "./a ./b"),
        ]
    ],
)
def test_a_use_entry_of_two_fields_raises_naming_it(
    text: ManifestText, entry: ManifestText
) -> None:
    """A use entry that is not one path raises, quoting the entry."""
    with pytest.raises(ManifestError) as caught:
        go_uses(text, _GO_WORK)
    assert str(caught.value) == f"go.work: cannot parse use entry {entry!r}"


def test_an_unterminated_use_block_raises_naming_the_manifest() -> None:
    """A ``use (`` never closed raises."""
    with pytest.raises(ManifestError) as caught:
        go_uses(ManifestText("go 1.26\n\nuse (\n\t./go\n"), _GO_WORK)
    assert str(caught.value) == "go.work: unterminated use block"


def test_fetch_declares_returns_every_declaration_in_order() -> None:
    """Each ``URL`` + ``URL_HASH SHA256=`` declaration is read, its name, URL and pin, in order."""
    text = ManifestText(
        "include(FetchContent)\n"
        + _JSON_DECLARE
        + "\n"
        + _YAML_DECLARE
        + "FetchContent_MakeAvailable(json)\n"
    )
    assert fetch_declares(text, _CMAKE) == [_JSON, _YAML]


def test_a_cmake_text_without_declarations_reads_none() -> None:
    """A CMake file that declares nothing reads as no declaration, not as a refusal."""
    assert fetch_declares(ManifestText("project(x)\ninclude(FetchContent)\n"), _CMAKE) == []


@pytest.mark.parametrize(
    "other",
    [
        ManifestText(other)
        for other in [
            "FetchContent_Declare(Catch2\n  GIT_REPOSITORY https://example.com/catch2.git\n"
            + "  GIT_TAG v3.0.0\n)\n",
            "FetchContent_Declare(short\n  URL https://example.com/s.tgz\n"
            + f"  URL_HASH SHA256={'a' * 63}\n)\n",
            "FetchContent_Declare(long\n  URL https://example.com/l.tgz\n"
            + f"  URL_HASH SHA256={'a' * 65}\n)\n",
            "FetchContent_Declare(md5\n  URL https://example.com/m.tgz\n"
            + f"  URL_HASH MD5={'a' * 32}\n)\n",
            "FetchContent_Declare (spaced\n  URL https://example.com/p.tgz\n"
            + f"  URL_HASH SHA256={'a' * 64}\n)\n",
        ]
    ],
)
def test_a_declaration_of_another_shape_raises_naming_what_was_read(other: ManifestText) -> None:
    """A declaration the shape does not read raises, counted against those that were read."""
    with pytest.raises(ManifestError) as caught:
        fetch_declares(ManifestText(_JSON_DECLARE + other), _CMAKE)
    assert str(caught.value) == (
        "cpp/CMakeLists.txt: found 2 FetchContent_Declare occurrence(s) but read 1 (json)"
        + _REFUSAL
    )


def test_a_lone_declaration_of_another_shape_raises_naming_none_read() -> None:
    """When no declaration reads, the message says none were read."""
    text = ManifestText(
        "FetchContent_Declare(Catch2\n  GIT_REPOSITORY https://example.com/c.git\n)\n"
    )
    with pytest.raises(ManifestError) as caught:
        fetch_declares(text, _CMAKE)
    assert str(caught.value) == (
        "cpp/CMakeLists.txt: found 1 FetchContent_Declare occurrence(s) but read 0 (none)"
        + _REFUSAL
    )


@pytest.mark.parametrize(
    ("name", "package"),
    [
        (FetchName(name), FetchName(package))
        for name, package in [
            ("miniz_fetch", "miniz"),
            ("pugixml_fetch", "pugixml"),
            ("json", "json"),
            ("fetch_json", "fetch_json"),
            ("jsonfetch", "jsonfetch"),
            ("json_fetch_fetch", "json_fetch"),
            ("json-fetch", "json-fetch"),
        ]
    ],
)
def test_fetched_package_strips_one_trailing_fetch_suffix_only(
    name: FetchName, package: FetchName
) -> None:
    """Only a trailing ``_fetch`` is stripped, and only once."""
    assert fetched_package(name) == package


@pytest.mark.parametrize(
    ("entry", "expected"),
    [
        (
            ManifestText("aletheia[can, yaml]"),
            _requirement(
                DistributionName("aletheia"), (ExtraName("can"), ExtraName("yaml")), VersionSpec("")
            ),
        ),
        (
            ManifestText("aletheia[can,,yaml]"),
            _requirement(
                DistributionName("aletheia"), (ExtraName("can"), ExtraName("yaml")), VersionSpec("")
            ),
        ),
        (
            ManifestText("pyyaml>=6.0.3"),
            _requirement(DistributionName("pyyaml"), (), VersionSpec(">=6.0.3")),
        ),
        (
            ManifestText("  pytest >= 8.0, <10  "),
            _requirement(DistributionName("pytest"), (), VersionSpec(">= 8.0, <10")),
        ),
        (
            ManifestText("python-can"),
            _requirement(DistributionName("python-can"), (), VersionSpec("")),
        ),
        (
            ManifestText("hypothesis[cli]~=6.100"),
            _requirement(
                DistributionName("hypothesis"), (ExtraName("cli"),), VersionSpec("~=6.100")
            ),
        ),
        (
            ManifestText("x"),
            _requirement(DistributionName("x"), (), VersionSpec("")),
        ),
        (
            ManifestText("zope.interface!=5.0"),
            _requirement(DistributionName("zope.interface"), (), VersionSpec("!=5.0")),
        ),
    ],
)
def test_requirement_returns_its_name_extras_and_spec(
    entry: ManifestText, expected: Requirement
) -> None:
    """The name, every non-empty extra stripped, and the specifier stripped, empty when absent."""
    assert requirement(entry) == expected


@pytest.mark.parametrize(
    "entry",
    [
        ManifestText(entry)
        for entry in [
            "???bogus",
            "",
            "-leading",
            "trailing-",
            "aletheia[]",
            "pyyaml; python_version<'3.15'",
            "pkg @ https://example.com/pkg.whl",
        ]
    ],
)
def test_requirement_returns_none_for_an_entry_it_does_not_read(entry: ManifestText) -> None:
    """An entry that is no name, or carries a marker or a URL, is not read."""
    assert requirement(entry) is None


@pytest.mark.parametrize(
    ("name", "folded"),
    [
        (DistributionName(name), DistributionName(folded))
        for name, folded in [
            ("PyYAML", "pyyaml"),
            ("python-can", "python-can"),
            ("python_can", "python-can"),
            ("Zope.Interface", "zope-interface"),
            ("a-_.b", "a-b"),
            ("a__b..c--d", "a-b-c-d"),
            ("plain", "plain"),
        ]
    ],
)
def test_normalized_lowers_and_folds_each_separator_run_to_one_hyphen(
    name: DistributionName, folded: DistributionName
) -> None:
    """PEP 503: lowered, every run of ``-``, ``_`` and ``.`` one ``-``."""
    assert normalized(name) == folded


def test_a_require_block_opened_without_a_space_is_read_as_go_reads_it() -> None:
    """``go mod edit -json`` reads ``require(`` as a block opening; so must the reader."""
    text = ManifestText("module example.com/m\n\nrequire(\n\texample.com/a v1.0.0\n)\n")
    assert go_requires(text, _GO_MOD) == [
        _require(GoModule("example.com/a"), GoVersion("v1.0.0"), indirect=False)
    ]


def test_a_single_line_require_separated_by_a_tab_is_read_as_go_reads_it() -> None:
    """``go mod edit -json`` reads ``require<TAB>module version``; so must the reader."""
    text = ManifestText("module example.com/m\n\nrequire\texample.com/b v1.2.0 // indirect; why\n")
    assert go_requires(text, _GO_MOD) == [
        _require(GoModule("example.com/b"), GoVersion("v1.2.0"), indirect=True)
    ]


def test_a_use_block_opened_without_a_space_is_read_as_go_reads_it() -> None:
    """``go work edit -json`` reads ``use(`` as a block opening; so must the reader."""
    assert go_uses(ManifestText("go 1.26\n\nuse(\n\t./a\n)\n"), _GO_WORK) == [GoUse("./a")]


def test_a_quoted_module_path_is_returned_unquoted() -> None:
    """``go mod edit -json`` reads ``module "example.com/m"`` as the path ``example.com/m``."""
    text = ManifestText('module "example.com/m"\n\ngo 1.26\n')
    assert go_module(text, _GO_MOD) == GoModule("example.com/m")


def test_a_requirement_with_a_marker_after_its_spec_is_not_read() -> None:
    """The module states markers are not matched, so a marker entry is refused, never misread."""
    assert requirement(ManifestText("pyyaml>=6.0.3; python_version<'3.15'")) is None


def test_a_commented_out_declaration_is_not_read() -> None:
    """A ``#`` comment declares nothing to CMake, so it bills no fetch."""
    text = ManifestText(
        "# FetchContent_Declare(old URL https://example.com/old.tgz"
        + f" URL_HASH SHA256={_JSON_SHA})\n"
        + _JSON_DECLARE
    )
    assert fetch_declares(text, _CMAKE) == [_JSON]


def test_a_quoted_url_is_read_unquoted() -> None:
    """CMake passes ``URL "https://..."`` as the URL without its quotes."""
    text = ManifestText(
        "FetchContent_Declare(json\n"
        + '  URL "https://example.com/json.tar.xz"\n'
        + f"  URL_HASH SHA256={_JSON_SHA}\n"
        + ")\n"
    )
    assert fetch_declares(text, _CMAKE) == [_JSON]
