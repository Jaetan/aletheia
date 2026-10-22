# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the C++ wrapper's object layout to its record, ``docs/CPP_LAYOUT.yaml``.

The shared library ``libaletheia-cpp`` is installed under a ``SOVERSION``, and a
program linked against it holds the public types by value, so a change to any
public type's size or alignment is a change every such program is rebuilt for.
The project's rule: a layout change raises ``SOVERSION`` in
``cpp/CMakeLists.txt``, carries the breaking mark on its subject, and re-takes
the record.  Three arms hold it:

* this gate.  The roster is every class, struct, enum and type alias the public
  headers under ``cpp/include/aletheia/`` declare at namespace scope, outside a
  ``detail`` or unnamed namespace and not a template; every roster type is a row
  of the record and no row names a type the headers no longer declare.  The
  record's ``soversion`` is the CMake value.  Against the comparison ref's
  merge-base, a record whose rows changed carries a higher ``soversion`` than
  the base's, and no record carries a lower one: a raise with no row changed
  is allowed, for a break the record cannot see (a virtual function added, a
  signature or an enumerator's value changed).  And
  ``cpp/tests/layout_roster.inc``, the type list the C++ test measures with
  the headers that declare its types, is the roster this gate derives
  (``--write-roster`` rewrites it);
* ``cpp/tests/test_cpp_layout.cpp``, compiled with the pinned toolchain,
  compares ``sizeof`` and ``alignof`` of every roster type to the record;
* ``tools/check_pr_title.py``, which refuses a branch that changes the record
  under a subject without the breaking mark, and ``tools/check_changelog.py``,
  which names the record among the surface records whose change owes an entry.

Exit codes:
  0: the roster, the record, the type list and the SOVERSION agree, and the
     SOVERSION rose where the rows moved and fell nowhere.
  1: a row is missing or stale, the list is stale, the versions differ, the
     rows moved under an unraised SOVERSION, or the SOVERSION fell; what to
     paste or run is printed.
  2: a file cannot be read, or git cannot name the comparison ref's merge-base.

The bump arm reads the base at the merge-base with the comparison ref, so it holds
a pull request; on a push to main the merge-base is the pushed commit itself and
the arm compares the record with itself, as ``tools/check_changelog.py`` does.
"""

from __future__ import annotations

import argparse
import re
import sys
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

import yaml

from tools._common import RelPath, emit, find_executable, git_ls_files, git_toplevel, run_capture
from tools.commit_subjects import GitArg, Revision

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

TOOL = Prose("check-cpp-layout")
DESCRIPTION = "Hold the C++ wrapper's object layout to its record, docs/CPP_LAYOUT.yaml."
RECORD = RelPath("docs/CPP_LAYOUT.yaml")
ROSTER = RelPath("cpp/tests/layout_roster.inc")
CMAKE = RelPath("cpp/CMakeLists.txt")
INCLUDE_ROOT = RelPath("cpp/include")
HEADERS = "cpp/include/aletheia/*.hpp"

# A public type's qualified name, as the headers spell it.
TypeName = NewType("TypeName", str)
# The shared library's SOVERSION, as CMake spells it.
SoVersion = NewType("SoVersion", int)
# A size or an alignment in bytes, as the compiler measures it.
Bytes = NewType("Bytes", int)
# One namespace a header opens, as written (``aletheia``, ``aletheia::detail``), or
# the empty name of an unnamed one.
NamespaceName = NewType("NamespaceName", str)

# One line of a public header, as it is read.
HeaderLine = NewType("HeaderLine", str)
# A public header as an #include names it, relative to cpp/include.
IncludePath = NewType("IncludePath", str)

# Namespaces whose types are not the public surface.
_PRIVATE = frozenset({"detail", ""})
_NAMESPACE_OPEN = re.compile(r"^(?:inline )?namespace ?([\w:]*) ?\{")
_NAMESPACE_CLOSE = re.compile(r"^\} // namespace")
# Attributes and an alignment may stand between the key and the name.
_DECORATION = r"(?:\s+\[\[[^\]]*\]\]|\s+alignas\([^)]*\))*"
# A declaration's head at column 0: a class, struct or enum, which is a definition
# when a brace comes before a semicolon, on this line or a later one, or an alias.
_HEAD = re.compile(
    rf"^(?:(?:class|struct|enum(?: class| struct)?){_DECORATION}\s+(\w+)|using (\w+) =)"
)
_SOVERSION = re.compile(r"^\s*SOVERSION (\d+)\s*$", re.MULTILINE)


class Row(NamedTuple):
    """One row of the record: a type, its size and its alignment in bytes."""

    name: TypeName
    size: Bytes
    align: Bytes


class Record(NamedTuple):
    """The record: the SOVERSION it is taken under, and its rows."""

    soversion: SoVersion
    rows: list[Row]


class Roster(NamedTuple):
    """The public types the headers declare, and the headers declaring one, in header order."""

    types: list[TypeName]
    includes: list[IncludePath]


def _defines(rest: list[HeaderLine]) -> bool:
    """Say whether the declaration that starts ``rest`` reaches a brace before a semicolon."""
    for line in rest:
        brace, semicolon = line.find("{"), line.find(";")
        if brace >= 0 and (semicolon < 0 or brace < semicolon):
            return True
        if semicolon >= 0:
            return False
    return False


def roster(include_root: Path, headers: list[Path]) -> Roster:
    """Give the public types the headers declare, in header order then line order."""
    found: list[TypeName] = []
    includes: list[IncludePath] = []
    for header in headers:
        before = len(found)
        stack: list[NamespaceName] = []
        previous = ""
        lines = [HeaderLine(line) for line in header.read_text(encoding="utf-8").splitlines()]
        for at, line in enumerate(lines):
            if opened := _NAMESPACE_OPEN.match(line):
                stack.append(NamespaceName(opened.group(1)))
            elif _NAMESPACE_CLOSE.match(line) and stack:
                _ = stack.pop()
            elif (head := _HEAD.match(line)) and not previous.startswith("template"):
                parts = [part for name in stack for part in name.split("::")]
                alias = head.group(2)
                if stack and _PRIVATE.isdisjoint(parts) and (alias or _defines(lines[at:])):
                    found.append(TypeName("::".join([*parts, alias or head.group(1)])))
            if line.strip():
                previous = line
        if len(found) > before:
            includes.append(IncludePath(header.relative_to(include_root).as_posix()))
    return Roster(found, includes)


def roster_text(declared: Roster) -> Prose:
    """Render the type list the C++ test includes: its headers, the types, then their names."""
    names = declared.types
    lines = [
        "// SPDX-FileCopyrightText: 2025 Nicolas Pelletier",
        "// SPDX-License-Identifier: BSD-2-Clause",
        "// Every public type of the C++ wrapper and the headers declaring them, which",
        "// tests/test_cpp_layout.cpp measures against docs/CPP_LAYOUT.yaml. Written by",
        "// tools/check_cpp_layout.py --write-roster from the headers; the gate refuses a",
        "// copy that differs from what it derives.",
        *(f"#include <{include}>" for include in declared.includes),
        "",
        "#include <array>",
        "#include <string_view>",
        "",
        "namespace {",
        "",
        "template<typename... T>",
        "struct TypeList {};",
        "",
        "using LayoutRoster = TypeList<",
        *(f"    {name}{'>;' if i == len(names) - 1 else ','}" for i, name in enumerate(names)),
        "constexpr std::array k_layout_names{",
        *(f'    std::string_view{{"{name}"}},' for name in names),
        "};",
        "",
        "} // namespace",
    ]
    return Prose("\n".join(lines) + "\n")


class _RowDocument(TypedDict):
    """One row as the YAML spells it."""

    name: TypeName
    size: Bytes
    align: Bytes


class _RecordDocument(TypedDict):
    """The record as the YAML spells it."""

    soversion: SoVersion
    types: list[_RowDocument]


# A scalar read where the record states a count or a name: the type the record
# gives it, or a boolean or a string a hand edit writes there instead.
type _Scalar = SoVersion | Bytes | TypeName | bool


def _whole(value: _Scalar) -> bool:
    """Say whether a YAML scalar read where a count stands is an integer, not a boolean."""
    return isinstance(value, int) and not isinstance(value, bool)


def _text(value: _Scalar) -> bool:
    """Say whether a YAML scalar read where a name stands is a string."""
    return isinstance(value, str)


def parse_record(text: Prose, where: Prose) -> Record | Prose:
    """Read a record's version and rows from its text, or say why it cannot be read."""
    try:
        document = cast("_RecordDocument", yaml.safe_load(text))
        version, listed = document["soversion"], document["types"]
        rows = [Row(entry["name"], entry["size"], entry["align"]) for entry in listed]
    except yaml.YAMLError as exc:
        return Prose(f"{where} cannot be read: {exc}")
    except (KeyError, TypeError) as exc:
        return Prose(
            f"{where} lacks a soversion, a types list or a row's name, size and align: {exc}"
        )
    if not _whole(version):
        return Prose(f"{where} does not carry an integer soversion")
    for row in rows:
        if not (_text(row.name) and _whole(row.size) and _whole(row.align)):
            return Prose(f"{where}: a row is not a name, a size and an alignment: {row!r}")
    return Record(version, rows)


def parse_soversion(text: Prose, where: Prose) -> SoVersion | Prose:
    """Read the SOVERSION a CMake file sets, or say that it sets none."""
    found = _SOVERSION.search(text)
    if found is None:
        return Prose(f"{where} sets no SOVERSION")
    return SoVersion(int(found.group(1)))


def problems(
    declared: Roster, record: Record, cmake: SoVersion, roster_file: Prose | None
) -> list[Prose]:
    """Say what disagrees between the roster, the record, the type list and CMake."""
    names = declared.types
    out: list[Prose] = []
    recorded = {row.name for row in record.rows}
    out.extend(
        Prose(
            f"{RECORD} has no row for {name}: a new public type; run the C++ layout test "
            + "and paste the row it prints, then raise SOVERSION and carry the breaking mark"
        )
        for name in names
        if name not in recorded
    )
    out.extend(
        Prose(f"{RECORD} names {name}, which no public header declares: delete its row")
        for name in sorted(recorded - set(names))
    )
    if record.soversion != cmake:
        out.append(
            Prose(
                f"{RECORD} records soversion {record.soversion}, and {CMAKE} sets "
                + f"SOVERSION {cmake}"
            )
        )
    if roster_file != roster_text(declared):
        out.append(
            Prose(
                f"{ROSTER} is not the roster the headers give: run "
                + "python/.venv/bin/python -m tools.check_cpp_layout --write-roster"
            )
        )
    return out


def bump_problems(base: Record | SoVersion, head: Record) -> list[Prose]:
    """Say whether the SOVERSION rose where the rows moved, and fell nowhere, against the base.

    ``base`` is the base's record, or its CMake SOVERSION alone where the base
    has no record yet, in which case every row is new.
    """
    if isinstance(base, int):
        changed, base_version = True, base
    else:
        changed, base_version = sorted(base.rows) != sorted(head.rows), base.soversion
    if changed and head.soversion <= base_version:
        return [
            Prose(
                f"{RECORD}'s rows differ from the base's, and its soversion {head.soversion} "
                + f"is not above the base's {base_version}: raise SOVERSION in {CMAKE} and "
                + "in the record, and carry the breaking mark"
            )
        ]
    if head.soversion < base_version:
        return [
            Prose(
                f"{RECORD}'s soversion falls from {base_version} to {head.soversion}: a "
                + "SOVERSION is never reused, so it only rises"
            )
        ]
    return []


def _git(top: Path, *args: GitArg) -> Prose | None:
    """Run git in ``top``; its output, or None when it fails."""
    out = run_capture([find_executable("git"), *args], cwd=top)
    return Prose(out.stdout) if out.returncode == 0 else None


def _merge_base(top: Path, ref: Revision) -> Revision | None:
    """Name the merge-base of HEAD and ``ref`` in ``top``, or None when git cannot."""
    out = run_capture([find_executable("git"), "merge-base", "HEAD", ref], cwd=top)
    return Revision(out.stdout.strip()) if out.returncode == 0 else None


def base_record(top: Path, ref: Revision) -> Record | SoVersion | Prose:
    """Read the record at the merge-base with ``ref``, or its CMake SOVERSION, or why neither."""
    at = _merge_base(top, ref)
    if at is None:
        return Prose(f"git cannot name the merge-base of HEAD and {ref}")
    text = _git(top, GitArg("show"), GitArg(f"{at}:{RECORD}"))
    if text is not None:
        return parse_record(text, Prose(f"{RECORD} at {at}"))
    cmake = _git(top, GitArg("show"), GitArg(f"{at}:{CMAKE}"))
    if cmake is None:
        return Prose(f"{CMAKE} cannot be read at {at}")
    return parse_soversion(cmake, Prose(f"{CMAKE} at {at}"))


def _read(path: Path) -> Prose | None:
    """Read a file as UTF-8, or None when it cannot be read."""
    try:
        return Prose(path.read_text(encoding="utf-8"))
    except OSError, UnicodeDecodeError:
        return None


def main() -> ExitStatus:
    """Refuse a record, a type list or a SOVERSION that disagrees with the headers or the base."""
    ap = argparse.ArgumentParser(description=DESCRIPTION)
    _ = ap.add_argument("base", nargs="?", default="main", help="comparison ref (default: main)")
    _ = ap.add_argument(
        "--write-roster", action="store_true", help=f"rewrite {ROSTER} from the headers"
    )
    arguments = ap.parse_args()
    top = git_toplevel()
    declared = roster(top / INCLUDE_ROOT, [top / rel for rel in git_ls_files(top, HEADERS)])
    if arguments.write_roster:
        _ = (top / ROSTER).write_text(roster_text(declared), encoding="utf-8")
        emit(f"{TOOL}: wrote {ROSTER} ({len(declared.types)} types)")
        return ExitStatus(0)
    record_text, cmake_text = _read(top / RECORD), _read(top / CMAKE)
    record = (
        parse_record(record_text, Prose(str(RECORD)))
        if record_text is not None
        else Prose(f"{RECORD} cannot be read")
    )
    cmake = (
        parse_soversion(cmake_text, Prose(str(CMAKE)))
        if cmake_text is not None
        else Prose(f"{CMAKE} cannot be read")
    )
    base = base_record(top, Revision(str(arguments.base)))
    if not isinstance(record, Record) or isinstance(cmake, str) or isinstance(base, str):
        unread = next(r for r in (record, cmake, base) if isinstance(r, str))
        _ = sys.stderr.write(f"{TOOL}: FAIL: {unread}\n")
        return ExitStatus(2)
    found = [*problems(declared, record, cmake, _read(top / ROSTER)), *bump_problems(base, record)]
    for line in found:
        _ = sys.stderr.write(f"{TOOL}: FAIL: {line}\n")
    if found:
        return ExitStatus(1)
    emit(f"{TOOL}: {len(declared.types)} public types recorded at SOVERSION {cmake}")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
