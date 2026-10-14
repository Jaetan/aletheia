# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_haskell_ledger``, the building guide's Haskell ledger gate.

A shared library's name is its file name without ``lib`` and ``.so``; what the
library links is every ``ldd`` entry resolved to a file by name, the vDSO, the
dynamic loader and a preloaded library aside.  The guide's Haskell section holds
exactly three tables, tables outside the section uncounted, and anything else is
unread.  Each table is held to the library both ways, a name it lacks and a name
it adds each a finding, and each carried package's licence is held to the one
ghc-pkg records.  The command line answers 0, 1 or 2 as its docstring says.
Every process the gate would start is answered by a stand-in, so no test starts one.
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest
from _processes import CommandWord

from tools.check_haskell_ledger import (
    DIFFERS,
    HASKELL_LAYER,
    HELD,
    UNCHECKED,
    LedgerUnreadError,
    LibraryName,
    ghc_pkg_licence,
    ledger_findings,
    library_name,
    linked,
    main,
    tables,
)
from tools.docs_arms import BUILDING_GUIDE
from tools.sbom_generate import GhcPackage

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable

    from tools._markdown import Row

# One table row's cells, as a reader sees them.
type Cells = tuple[Prose, ...]
# One command line a stand-in process was asked to run.
type Command = list[CommandWord]


class _Ran(NamedTuple):
    """What one run of the command line did: its status, the lines it wrote, what it asked."""

    status: ExitStatus
    said: list[Prose]
    asked: list[Command]


_LDD = Prose(
    "\tlinux-vdso.so.1 (0x00007ffd)\n"
    + "\t/home/u/.bin/preload.so (0x00007f01)\n"
    + "\tlibm.so.6 => /usr/lib/x86_64-linux-gnu/libm.so.6 (0x00007f02)\n"
    + "\tlibHStext-2.1.1-787c-ghc9.8.4.so => /g/lib/libHStext-2.1.1-787c-ghc9.8.4.so (0x00007f03)\n"
    + "\tlibffi.so.8 => /g/lib/libffi.so.8 (0x00007f04)\n"
    + "\tlibgmp.so.10 => /usr/lib/x86_64-linux-gnu/libgmp.so.10 (0x00007f05)\n"
    + "\t/lib64/ld-linux-x86-64.so.2 (0x00007f06)\n"
)
_LIBC = Prose("\tlibc.so.6 => /usr/lib/x86_64-linux-gnu/libc.so.6 (0x00007f07)\n")

_RTS_SO = Path("/g/lib/libHSrts-1.0.2_thr-ghc9.8.4.so")
_TEXT_SO = Path("/g/lib/libHStext-2.1.1-787c-ghc9.8.4.so")
_FFI_SO = Path("/g/lib/libffi.so.8")
_BUNDLED = (_TEXT_SO, _RTS_SO, _FFI_SO)
_LINKS = {
    LibraryName("gmp"),
    LibraryName("c"),
    LibraryName("m"),
    LibraryName("ffi"),
    LibraryName("HSrts-1.0.2_thr-ghc9.8.4"),
    LibraryName("HStext-2.1.1-787c-ghc9.8.4"),
}
_LICENCES = {GhcPackage("rts"): Prose("BSD-3-Clause"), GhcPackage("text"): Prose("BSD-2-Clause")}

_PACKAGES = Prose(
    "| Package | License |\n|---|---|\n| GHC RTS | BSD-3-Clause |\n| text | BSD-2-Clause |\n"
)
_OTHERS = Prose("| Library | License |\n|---|---|\n| libffi | MIT |\n")
_SYSTEM = Prose(
    "| Library | License |\n|---|---|\n"
    + "| **libgmp** | LGPL-3.0+ |\n| glibc (libc, libm) | LGPL-2.1+ |\n"
)
_NOTHING = Prose("")
_NONE_CARRIED = Prose("| Library | License |\n|---|---|\n")
_NO_GMP = Prose("| Library | License |\n|---|---|\n| glibc (libc, libm) | LGPL-2.1+ |\n")


def _guide(packages: Prose = _PACKAGES, others: Prose = _OTHERS, system: Prose = _SYSTEM) -> Prose:
    """Return a guide whose Haskell section holds the three tables, a table before and after it."""
    return Prose(
        "# Building\n\n| Tool | Version |\n|---|---|\n| cabal | 3.12 |\n\n"
        + f"{HASKELL_LAYER}\n\nThe packages:\n\n{packages}\n"
        + f"Beside them:\n\n{others}\nNot bundled:\n\n{system}\n"
        + "### Runtime, Rust layer\n\n| Library | License |\n|---|---|\n| libz | Zlib |\n"
    )


def _findings(guide: Prose) -> list[Prose]:
    """Return the findings over ``guide`` for the canned library, bundle and licences."""
    return ledger_findings(guide, _LINKS, _BUNDLED, _LICENCES.get)


def _shown(found: Iterable[list[Row]]) -> list[list[Cells]]:
    """Return each table's body rows as a reader sees their cells."""
    return [[row.shown for row in table] for table in found]


def _unread(guide: Prose) -> Prose:
    """Return the message ``tables`` raises over ``guide``, failing if it raises none."""
    with pytest.raises(LedgerUnreadError) as raised:
        _ = tables(guide)
    return Prose(str(raised.value))


def test_library_name_drops_the_lib_prefix_and_the_so_suffix() -> None:
    """A versioned system library is named by what lies between ``lib`` and ``.so``."""
    assert library_name(Path("libgmp.so.10")) == LibraryName("gmp")


def test_library_name_keeps_a_ghc_library_s_package_version_and_compiler() -> None:
    """A GHC runtime library keeps everything before its ``.so``, its directory not read."""
    assert library_name(_RTS_SO) == LibraryName("HSrts-1.0.2_thr-ghc9.8.4")


def test_library_name_reads_up_to_the_so_suffix_that_ends_the_name() -> None:
    """A name runs up to the ``.so`` ending it, a version aside: libffi.sound.so is ffi.sound."""
    assert library_name(Path("libffi.sound.so")) == LibraryName("ffi.sound")
    assert library_name(Path("libffi.solver.so.1")) == LibraryName("ffi.solver")
    assert library_name(Path("libffi.so.8.1.4")) == LibraryName("ffi")


def test_library_name_is_none_for_a_name_going_on_past_its_so() -> None:
    """A file whose ``.so`` is followed by anything but a version is no shared library."""
    assert library_name(Path("libffi.solid")) is None
    assert library_name(Path("libfoo.so.x")) is None


def test_library_name_is_none_for_a_file_not_named_lib() -> None:
    """The dynamic loader, whose name does not open on ``lib``, has no library name."""
    assert library_name(Path("/usr/lib/ld-linux-x86-64.so.2")) is None


def test_library_name_is_none_for_a_static_archive() -> None:
    """A ``lib<name>.a`` archive is no shared library, so it has no library name."""
    assert library_name(Path("/usr/lib/libgmp.a")) is None


def test_linked_reads_every_resolved_library_and_sets_aside_the_vdso_preload_and_loader() -> None:
    """The four resolved entries are linked; the vDSO, a preload and the loader are not."""
    assert linked(_LDD) == {
        LibraryName("m"),
        LibraryName("HStext-2.1.1-787c-ghc9.8.4"),
        LibraryName("ffi"),
        LibraryName("gmp"),
    }


def test_linked_sets_aside_a_vdso_printed_with_an_empty_resolution() -> None:
    """An ldd that prints the vDSO with ``=>`` and no file links nothing by it."""
    assert linked(Prose("\tlinux-vdso.so.1 =>  (0x00007ffd)\n")) == set()


def test_tables_returns_the_body_rows_of_the_section_s_three_tables_only() -> None:
    """The tables before and after the section are not counted, and no header row is a body row."""
    assert _shown(tables(_guide())) == [
        [(Prose("GHC RTS"), Prose("BSD-3-Clause")), (Prose("text"), Prose("BSD-2-Clause"))],
        [(Prose("libffi"), Prose("MIT"))],
        [(Prose("libgmp"), Prose("LGPL-3.0+")), (Prose("glibc (libc, libm)"), Prose("LGPL-2.1+"))],
    ]


def test_tables_raises_when_the_guide_has_no_haskell_section() -> None:
    """A heading that drops the section's code span opens no section, so the guide is unread."""
    guide = Prose(f"### Runtime, Haskell layer\n\n{_PACKAGES}\n{_OTHERS}\n{_SYSTEM}")
    assert _unread(guide) == Prose(f"{BUILDING_GUIDE}: has no {HASKELL_LAYER} section")


def test_tables_raises_when_the_section_holds_two_tables() -> None:
    """A section holding two tables instead of three is unread, naming the count."""
    guide = _guide(others=Prose(""))
    assert _unread(guide) == Prose(f"{BUILDING_GUIDE}: {HASKELL_LAYER} holds 2 tables, not 3")


def test_tables_raises_when_the_section_holds_four_tables() -> None:
    """A fourth table inside the section makes it unread as well."""
    guide = _guide(system=Prose(f"{_SYSTEM}\nAlso:\n\n{_OTHERS}"))
    assert _unread(guide) == Prose(f"{BUILDING_GUIDE}: {HASKELL_LAYER} holds 4 tables, not 3")


def test_ledger_findings_is_empty_when_the_three_tables_hold() -> None:
    """Packages, bundled and system libraries and licences all match: no finding."""
    assert _findings(_guide()) == []


def test_ledger_findings_names_a_package_the_table_lacks_and_one_it_adds() -> None:
    """A carried package missing and an uncarried one listed are a finding each, unlicensed."""
    packages = Prose(
        "| Package | License |\n|---|---|\n| GHC RTS | BSD-3-Clause |\n| base | MIT |\n"
    )
    assert _findings(_guide(packages=packages)) == [
        Prose("the Haskell package table lacks text"),
        Prose("the Haskell package table names base, which the bundle does not carry"),
    ]


def test_ledger_findings_names_libffi_listed_among_the_system_libraries() -> None:
    """A carried library listed as a system one is lacked by one table and added by the other."""
    system = Prose(f"{_SYSTEM}| libffi | MIT |\n")
    assert _findings(_guide(others=_NONE_CARRIED, system=system)) == [
        Prose("the bundled library table lacks ffi"),
        Prose(
            "the system library table's row 'libffi' names no library "
            + "the library links from the system"
        ),
    ]


def test_ledger_findings_holds_a_c_library_row_naming_parts_this_build_does_not_link() -> None:
    """The C library's parts a row lists need not all be linked: glibc 2.34 folded them in."""
    system = Prose(
        "| Library | License |\n|---|---|\n"
        + "| **libgmp** | LGPL-3.0+ |\n"
        + "| glibc (libc, libm, libpthread, librt, libdl) | LGPL-2.1+ |\n"
    )
    assert _findings(_guide(system=system)) == []


def test_ledger_findings_names_a_system_row_whose_libraries_the_library_does_not_link() -> None:
    """A row naming no library the build links from the system is stale."""
    system = Prose(f"{_SYSTEM}| libz | Zlib |\n")
    assert _findings(_guide(system=system)) == [
        Prose(
            "the system library table's row 'libz' names no library "
            + "the library links from the system"
        )
    ]


def test_ledger_findings_names_a_system_library_the_table_lacks() -> None:
    """A linked library the bundle does not carry and the system table omits is a finding."""
    assert _findings(_guide(system=_NO_GMP)) == [Prose("the system library table lacks gmp")]


def test_ledger_findings_names_a_licence_ghc_pkg_records_otherwise() -> None:
    """A row whose licence differs from ghc-pkg's names both licences."""
    packages = Prose(
        "| Package | License |\n|---|---|\n| GHC RTS | BSD-3-Clause |\n| text | BSD-3-Clause |\n"
    )
    assert _findings(_guide(packages=packages)) == [
        Prose("text: the ledger says 'BSD-3-Clause', ghc-pkg records 'BSD-2-Clause'")
    ]


def test_ledger_findings_names_every_licence_ghc_pkg_records_none_for() -> None:
    """A package ghc-pkg records no licence for is a finding, in the table's row order."""
    records_none: dict[GhcPackage, Prose] = {}
    assert ledger_findings(_guide(), _LINKS, _BUNDLED, records_none.get) == [
        Prose("rts: the ledger says 'BSD-3-Clause', ghc-pkg records None"),
        Prose("text: the ledger says 'BSD-2-Clause', ghc-pkg records None"),
    ]


def test_ledger_findings_reads_a_package_table_without_a_licence_column_as_stating_none() -> None:
    """A packages table of one column states no licence, which differs from ghc-pkg's."""
    packages = Prose("| Package |\n|---|\n| GHC RTS |\n| text |\n")
    assert _findings(_guide(packages=packages)) == [
        Prose("rts: the ledger says None, ghc-pkg records 'BSD-3-Clause'"),
        Prose("text: the ledger says None, ghc-pkg records 'BSD-2-Clause'"),
    ]


def test_ledger_findings_raises_when_the_section_is_unread() -> None:
    """The findings are not computed over a section that does not hold three tables."""
    with pytest.raises(LedgerUnreadError):
        _ = _findings(_guide(others=Prose("")))


def _done(
    cmd: Command, status: ExitStatus, out: Prose, err: Prose = _NOTHING
) -> subprocess.CompletedProcess[Prose]:
    """Return what a stand-in process answers: ``cmd``, its status and its two outputs."""
    return subprocess.CompletedProcess(cmd, status, out, err)


def _stand_in(
    monkeypatch: pytest.MonkeyPatch, ldd: subprocess.CompletedProcess[Prose] | None = None
) -> list[Command]:
    """Answer ldd with ``ldd`` and ghc-pkg from the canned licences; return what was asked."""
    asked: list[Command] = []

    def answer(cmd: Command) -> subprocess.CompletedProcess[Prose]:
        """Record ``cmd`` and answer it as ldd or ghc-pkg would."""
        asked.append(cmd)
        if cmd[0] == "ldd" and ldd is not None:
            return ldd
        licence = _LICENCES.get(GhcPackage(cmd[2]))
        return _done(cmd, HELD, Prose("" if licence is None else f"{licence}\n"))

    def found(name: CommandWord) -> CommandWord:
        """Resolve ``name`` to itself, so the commands read as their program names."""
        return name

    monkeypatch.setattr("tools.check_haskell_ledger.find_executable", found)
    monkeypatch.setattr("tools.check_haskell_ledger.run_capture", answer)
    return asked


def _ghc_pkg(package: GhcPackage) -> Command:
    """Return the ghc-pkg command that asks the licence of ``package``."""
    words = ("ghc-pkg", "field", package, "license", "--simple-output")
    return [CommandWord(word) for word in words]


def test_ghc_pkg_licence_returns_the_licence_ghc_pkg_prints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The first word ghc-pkg prints for the package's licence field is its licence."""
    asked = _stand_in(monkeypatch)
    assert ghc_pkg_licence(GhcPackage("text")) == Prose("BSD-2-Clause")
    assert asked == [_ghc_pkg(GhcPackage("text"))]


def test_ghc_pkg_licence_is_none_when_ghc_pkg_prints_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A package whose licence field ghc-pkg leaves empty records no licence."""
    _ = _stand_in(monkeypatch)
    assert ghc_pkg_licence(GhcPackage("base")) is None


def test_ghc_pkg_licence_is_none_when_ghc_pkg_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    """A ghc-pkg that exits non-zero records no licence, whatever it printed."""

    def unknown(cmd: Command) -> subprocess.CompletedProcess[Prose]:
        """Answer as ghc-pkg does for a package it does not know."""
        return _done(cmd, DIFFERS, Prose("BSD-3-Clause\n"), Prose("ghc-pkg: cannot find package\n"))

    _ = _stand_in(monkeypatch)
    monkeypatch.setattr("tools.check_haskell_ledger.run_capture", unknown)
    assert ghc_pkg_licence(GhcPackage("rts")) is None


_LIBRARY = CommandWord("build/libaletheia-ffi.so")
_LDD_ASKED = [CommandWord("ldd"), _LIBRARY]


def _run_main(
    monkeypatch: pytest.MonkeyPatch, repo: Path, ldd: subprocess.CompletedProcess[Prose]
) -> _Ran:
    """Run the command line over the guide under ``repo``; return what the run did."""
    said: list[Prose] = []

    def emit(message: Prose) -> None:
        """Record one line the gate writes."""
        said.append(message)

    asked = _stand_in(monkeypatch, ldd)
    monkeypatch.setattr("tools.check_haskell_ledger.emit", emit)
    monkeypatch.setattr("tools.check_haskell_ledger.REPO", repo)
    monkeypatch.setattr("sys.argv", ["check_haskell_ledger", _LIBRARY, *map(str, _BUNDLED)])
    return _Ran(main(), said, asked)


def _plant_guide(repo: Path, guide: Prose) -> None:
    """Write ``guide`` where the gate reads the building guide under ``repo``."""
    path = repo / BUILDING_GUIDE
    path.parent.mkdir(parents=True)
    _ = path.write_text(guide, encoding="utf-8")


def _ldd_reads(out: Prose) -> subprocess.CompletedProcess[Prose]:
    """Return an ldd that reads the library and prints ``out``."""
    return _done(_LDD_ASKED, HELD, out)


def test_main_holds_a_ledger_that_names_what_the_library_links_and_carries(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A ledger that holds exits 0, having asked ldd and then ghc-pkg per carried package."""
    _plant_guide(tmp_path, _guide())
    assert _run_main(monkeypatch, tmp_path, _ldd_reads(Prose(_LDD + _LIBC))) == _Ran(
        HELD,
        [
            Prose(
                "check-haskell-ledger: the Haskell ledger names what the library links and carries"
            )
        ],
        [_LDD_ASKED, _ghc_pkg(GhcPackage("rts")), _ghc_pkg(GhcPackage("text"))],
    )


def test_main_reports_each_finding_and_exits_one(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A table that lacks a linked library exits 1, each finding on a line naming the guide."""
    _plant_guide(tmp_path, _guide(system=_NO_GMP))
    ran = _run_main(monkeypatch, tmp_path, _ldd_reads(Prose(_LDD + _LIBC)))
    assert (ran.status, ran.said) == (
        DIFFERS,
        [Prose(f"check-haskell-ledger: {BUILDING_GUIDE}: the system library table lacks gmp")],
    )


def test_main_is_unchecked_when_ldd_cannot_read_the_library(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An ldd that fails exits 2 with its own message, before the guide or ghc-pkg is read."""
    ldd = _done(_LDD_ASKED, DIFFERS, Prose(""), Prose("\tnot a dynamic executable\n"))
    assert _run_main(monkeypatch, tmp_path, ldd) == _Ran(
        UNCHECKED,
        [Prose(f"check-haskell-ledger: ldd cannot read {_LIBRARY}: not a dynamic executable")],
        [_LDD_ASKED],
    )


@pytest.mark.parametrize("absent", [CommandWord("ldd"), CommandWord("ghc-pkg")])
def test_main_is_unchecked_when_a_tool_it_runs_is_not_on_the_search_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, absent: CommandWord
) -> None:
    """A tool the check runs that the search path lacks exits 2, never a traceback."""
    _plant_guide(tmp_path, _guide())
    said: list[Prose] = []

    def emit(message: Prose) -> None:
        """Record one line the gate writes."""
        said.append(message)

    def found(name: CommandWord) -> CommandWord:
        """Resolve every tool but ``absent``, which raises as the search path's lookup does."""
        if name == absent:
            message = f"required executable not found on PATH: {name}"
            raise RuntimeError(message)
        return name

    _ = _stand_in(monkeypatch, _ldd_reads(Prose(_LDD + _LIBC)))
    monkeypatch.setattr("tools.check_haskell_ledger.find_executable", found)
    monkeypatch.setattr("tools.check_haskell_ledger.emit", emit)
    monkeypatch.setattr("tools.check_haskell_ledger.REPO", tmp_path)
    monkeypatch.setattr("sys.argv", ["check_haskell_ledger", _LIBRARY, *map(str, _BUNDLED)])
    assert (main(), said) == (
        UNCHECKED,
        [
            Prose(
                f"check-haskell-ledger: required executable not found on PATH: {absent}; "
                + "the Haskell ledger is unchecked"
            )
        ],
    )


def test_main_refuses_a_run_naming_no_bundled_library(monkeypatch: pytest.MonkeyPatch) -> None:
    """A bundle always carries libraries, so a run naming none is refused before any read."""
    monkeypatch.setattr("sys.argv", ["check_haskell_ledger", _LIBRARY])
    with pytest.raises(SystemExit) as refused:
        _ = main()
    assert refused.value.code == ExitStatus(2)


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, differing and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, DIFFERS, UNCHECKED)


def test_linked_keeps_a_library_ldd_cannot_find() -> None:
    """A library ldd finds no file for is still one the library links, by the name it needs."""
    assert linked(Prose("\tlibmissing.so.1 => not found\n")) == {LibraryName("missing")}


def test_tables_reads_a_table_right_under_the_heading() -> None:
    """A table on the line after the heading is the section's first table."""
    guide = Prose(f"{HASKELL_LAYER}\n{_PACKAGES}\n{_OTHERS}\n{_SYSTEM}")
    assert len(tables(guide)) == 3


def test_ledger_findings_names_a_bundled_row_the_bundle_does_not_carry() -> None:
    """A library the bundled table names and the bundle lacks is named as not carried."""
    others = Prose("| Library | License |\n|---|---|\n| libffi | MIT |\n| libz | Zlib |\n")
    assert _findings(_guide(others=others)) == [
        Prose("the bundled library table names z, which the bundle does not carry")
    ]


def test_main_is_unchecked_when_the_guide_is_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A guide that cannot be read exits 2, naming the read's error, and asks ghc-pkg nothing."""
    missing = tmp_path / BUILDING_GUIDE
    assert _run_main(monkeypatch, tmp_path, _ldd_reads(Prose(_LDD + _LIBC))) == _Ran(
        UNCHECKED,
        [
            Prose(
                "check-haskell-ledger: [Errno 2] No such file or directory: "
                + f"'{missing}'; the Haskell ledger is unchecked"
            )
        ],
        [_LDD_ASKED],
    )


def test_main_is_unchecked_when_the_guide_lacks_the_haskell_section(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A guide without the section exits 2, naming the section, and asks ghc-pkg nothing."""
    _plant_guide(tmp_path, Prose("# Building\n\nNothing here.\n"))
    assert _run_main(monkeypatch, tmp_path, _ldd_reads(Prose(_LDD + _LIBC))) == _Ran(
        UNCHECKED,
        [
            Prose(
                f"check-haskell-ledger: {BUILDING_GUIDE}: has no {HASKELL_LAYER} section; "
                + "the Haskell ledger is unchecked"
            )
        ],
        [_LDD_ASKED],
    )
