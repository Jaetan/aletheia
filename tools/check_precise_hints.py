# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse a Python type hint that claims more than the code handles, unless the record names it.

AGENTS/python.md cat 8: every hint is universally quantified.  ``str`` claims
the code handles any string, ``list[float]`` any list of floats, ``dict[str, X]``
any key at all; the code handles none of those, so the hint is false and the
checker cannot refuse what the code refuses.  A hint is imprecise when it holds:

* ``Any`` or ``object``, or a generic given no parameters, which holds
  ``Any``, past all of which the checker sees nothing;
* ``str``, ``int``, ``float`` or ``bytes``, alone, in a union, inside a
  container or as a mapping's key, where a value with a meaning stands, which
  a ``NewType``, an enum, a ``Literal``, a ``TypedDict`` or a dataclass names
  instead; prose is ``Prose``, a ``NewType`` like any other;
* three or more nested subscripts, a shape that wants a name of its own.

A type alias is read as the hint on its right side, however it is spelled
(``type X = ...``, an annotation of ``TypeAlias``, ``TypeAliasType``, or a
generic or a union assigned to a name at module level), since an alias renames
a shape without narrowing it; so is a ``NewType`` over a shape rather than a
name, keyed by its own call.  The type a ``cast`` names is read as a hint too,
a cast being where an imprecise type most often slips in.

It is a ratchet, not a ban: ``docs/PYTHON_IMPRECISE_HINTS.yaml`` records the
imprecise hints the tree has, so that a new one fails.  Both directions are
enforced, as ``tools/check_cpp_index_loops.py`` does, because a row naming more
hints than its file holds is standing permission to write one back.  Adding a
row needs user approval, on the same footing as a ``NOLINT`` suppression, and a
hint a foreign interface forces carries a ``reason:``.  Rows are keyed by file
and by the hint's own text, so an edit elsewhere in the file does not move them.

It reads every tracked Python file outside ``.archive/``, and the Python each
probe hands an interpreter, a heredoc after ``-`` or a ``-c`` string, which no
other checker reads.  A probe that hands one Python in any other form fails the
lens, so that Python is never skipped unread.

Run: ``python -m tools.check_precise_hints`` compares the tree with the record;
``--file PATH --as REL`` compares one file's text, as it would stand after an
edit, with the record's rows for REL, which is what the write-time hook runs;
``--print-record`` prints the tree's rows in the record's spelling; ``--root DIR
--record FILE`` holds another tree, every tracked file under DIR, to its own
record, which is how a repository without the gate is held to it.  Exit 0 is
clean, 1 a hint or a row out of step, 2 a file or the record that cannot be read.
"""

from __future__ import annotations

import argparse
import ast
import collections
import re
import sys
from enum import StrEnum
from pathlib import Path, PurePosixPath
from typing import NamedTuple, NewType, cast

from tools._common import RelPath, emit, git_ls_files, git_toplevel
from tools._ratchet import CanonicalText, RatchetRows, RowKey, as_row, read_ratchet_rows

from aletheia.common_types import ExitStatus, Prose

# The ratchet's record, repo-root-relative, and the list in it the rows sit under.
RECORD = Path("docs") / "PYTHON_IMPRECISE_HINTS.yaml"
_RECORD_LIST = "hints"

CLEAN, OUT_OF_STEP, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)

# Python as a file or a probe holds it, and a probe's shell text.
PythonSource = NewType("PythonSource", str)
ShellSource = NewType("ShellSource", str)

# A line of a file, counted from one; a character's place in a text; how many
# subscripts a hint nests; a name as a hint spells it, the last part of a dotted one.
LineNumber = NewType("LineNumber", int)
TextOffset = NewType("TextOffset", int)
Depth = NewType("Depth", int)
TypeName = NewType("TypeName", str)


class Fault(StrEnum):
    """What makes a hint claim more than the code handles."""

    UNSEEN = "Any, object, or a generic given no parameters, past which the checker sees nothing"
    PRIMITIVE = "str, int, float or bytes where a value with a meaning stands"
    NESTED = "three or more nested subscripts, a shape that wants a name"


class Hint(NamedTuple):
    """One imprecise hint: its text, the line it starts on, and what is wrong with it."""

    text: CanonicalText
    line: LineNumber
    faults: frozenset[Fault]


class _Reading(NamedTuple):
    """What reading a hint's expression found: its faults, and how deep it nests."""

    faults: frozenset[Fault]
    depth: Depth


class _Piece(NamedTuple):
    """Python a probe hands an interpreter, and the probe's line its first line sits on."""

    source: PythonSource
    line: LineNumber


class Observed(NamedTuple):
    """A tree's imprecise hints: how many of each row, where each stands, what each holds."""

    rows: RatchetRows
    lines: dict[RowKey, list[LineNumber]]
    faults: dict[RowKey, frozenset[Fault]]


class _Arguments(NamedTuple):
    """The command line: another tree and its record, one file in place of it, whether to list."""

    root: Path | None
    record: Path | None
    file: Path | None
    rel: RelPath | None
    print_record: bool


_UNSEEN = frozenset({TypeName("Any"), TypeName("object")})

# The generics that hold Any where no parameters are given: a bare `dict` is
# `dict[Any, Any]`, a bare `Callable` takes and returns anything.
_BARE_UNSEEN = frozenset(
    TypeName(name)
    for name in (
        "list", "dict", "set", "frozenset", "tuple", "type", "List", "Dict", "Set", "FrozenSet",
        "Tuple", "Type", "Callable", "Sequence", "MutableSequence", "Mapping", "MutableMapping",
        "Iterable", "Iterator", "Generator", "Collection", "AbstractSet", "deque", "defaultdict",
        "Counter", "OrderedDict", "ChainMap", "Awaitable", "Coroutine", "AsyncIterator",
        "AsyncIterable", "AsyncGenerator",
    )
)  # fmt: skip
_PRIMITIVES = frozenset({TypeName("str"), TypeName("int"), TypeName("float"), TypeName("bytes")})
_NESTED = Depth(3)

# The generics a module-level assignment subscripts when it defines a type alias
# rather than computing a value.
_GENERICS = frozenset(
    TypeName(name)
    for name in (
        "list", "dict", "set", "frozenset", "tuple", "type", "Callable", "Sequence",
        "MutableSequence", "Mapping", "MutableMapping", "Iterable", "Iterator", "Generator",
        "Collection", "AbstractSet", "Optional", "Union", "Literal", "Annotated", "Final",
        "deque", "defaultdict", "Counter", "OrderedDict", "ChainMap", "Awaitable", "Coroutine",
        "AsyncIterator", "AsyncIterable", "AsyncGenerator", "ClassVar", "Required", "NotRequired",
    )
)  # fmt: skip

# An interpreter a probe hands Python to: its `py` or `python` variable, or a
# python named by path or on PATH.  Then a run of one on `-` (a script on stdin)
# or `-c`, a heredoc it reads, and a `-c` string in either quoting.
_INTERPRETER = r'(?:"?\$\{?py(?:thon)?\}?"?|[\w./-]*python[\d.]*)'
_RUN = re.compile(rf"{_INTERPRETER}\s+(?:-|-c)(?=\s|$)")
_PYTHON_HEREDOC = re.compile(rf"{_INTERPRETER}\s+-\s[^\n]*?(?<!<)<<(?!<)")
_HEREDOC = re.compile(r"(?<!<)<<(?!<)(-?)\s*(['\"]?)([A-Za-z_]\w*)\2")
_INLINE = re.compile(rf"{_INTERPRETER}\s+-c\s+'([^']*)'")
_INLINE_QUOTED = re.compile(rf'{_INTERPRETER}\s+-c\s+"((?:[^"\\]|\\.)*)"')
_SHELL_ESCAPE = re.compile(r'\\([\\"$`])')


def _name(node: ast.expr) -> TypeName | None:
    """Name the type a name or a dotted name spells; None for any other node."""
    if isinstance(node, ast.Name):
        return TypeName(node.id)
    if isinstance(node, ast.Attribute):
        return TypeName(node.attr)
    return None


def _unquoted(node: ast.expr) -> ast.expr:
    """Read a quoted hint as the expression it quotes; any other node as it stands."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        try:
            return ast.parse(node.value, mode="eval").body
        except SyntaxError:
            return node
    return node


def _joined(readings: list[_Reading], *, nests: bool) -> _Reading:
    """Join the readings of a node's parts, one level deeper where the node subscripts."""
    faults = frozenset(fault for reading in readings for fault in reading.faults)
    depth = max((reading.depth for reading in readings), default=Depth(0))
    return _Reading(faults, Depth(depth + 1) if nests else depth)


def _named_faults(name: TypeName) -> frozenset[Fault]:
    """Name what a type named alone holds: nothing, unless the name is one the lens refuses."""
    if name in _UNSEEN or name in _BARE_UNSEEN:
        return frozenset({Fault.UNSEEN})
    if name in _PRIMITIVES:
        return frozenset({Fault.PRIMITIVE})
    return frozenset()


def _subscripted(node: ast.Subscript) -> _Reading:
    """Read a subscripted hint: a Literal holds values, an Annotated's note is not a type."""
    outer = _name(node.value)
    if outer == TypeName("Literal"):
        return _Reading(frozenset(), Depth(1))
    parts = list(node.slice.elts) if isinstance(node.slice, ast.Tuple) else [node.slice]
    if outer == TypeName("Annotated"):
        parts = parts[:1]
    return _joined([_read(part) for part in parts], nests=True)


def _read(node: ast.expr) -> _Reading:
    """Read a hint's faults, and how deep its subscripts nest."""
    node = _unquoted(node)
    name = _name(node)
    if name is not None:
        return _Reading(_named_faults(name), Depth(0))
    if isinstance(node, ast.Subscript):
        return _subscripted(node)
    parts: list[ast.expr] = []
    if isinstance(node, ast.BinOp):
        parts = [node.left, node.right]
    elif isinstance(node, (ast.Tuple, ast.List)):
        parts = node.elts
    return _joined([_read(part) for part in parts], nests=False)


def _hint(node: ast.expr, text: CanonicalText) -> Hint | None:
    """Judge one hint, found at ``node`` and keyed by ``text``; None where it is precise."""
    reading = _read(node)
    nested = frozenset({Fault.NESTED}) if reading.depth >= _NESTED else frozenset[Fault]()
    faults = reading.faults | nested
    return Hint(text, LineNumber(node.lineno), faults) if faults else None


def _annotation(node: ast.expr) -> Hint | None:
    """Judge an annotation, keyed by its own text."""
    return _hint(node, CanonicalText(ast.unparse(_unquoted(node))))


def _alias(name: TypeName, value: ast.expr) -> Hint | None:
    """Judge a type alias by its right side, keyed as ``type NAME = RIGHT``."""
    return _hint(value, CanonicalText(f"type {name} = {ast.unparse(_unquoted(value))}"))


def _typelike(node: ast.expr) -> bool:
    """Say whether a module-level value is a type spelled as a generic or a union."""
    if isinstance(node, ast.Subscript):
        return _name(node.value) in _GENERICS
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return all(
            _typelike(side)
            or _name(side) is not None
            or (isinstance(side, ast.Constant) and side.value is None)
            for side in (node.left, node.right)
        )
    return False


def _module_alias(statement: ast.stmt) -> Hint | None:
    """Judge a module-level assignment that defines a type alias; None for any other."""
    if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
        return None
    target, value = statement.targets[0], statement.value
    if not isinstance(target, ast.Name):
        return None
    if isinstance(value, ast.Call) and _name(value.func) == TypeName("TypeAliasType"):
        right = [keyword.value for keyword in value.keywords if keyword.arg == "value"]
        right += value.args[1:2]
        return _alias(TypeName(target.id), right[0]) if right else None
    if isinstance(value, ast.Call) and _name(value.func) == TypeName("NewType"):
        # A NewType over a name narrows it; over a shape it keeps the shape's
        # every fault under a new name, so the shape is judged.
        base = value.args[1] if len(value.args) > 1 else None
        if base is None or _name(base) is not None:
            return None
        return _hint(base, CanonicalText(ast.unparse(value)))
    return _alias(TypeName(target.id), value) if _typelike(value) else None


def _arguments_of(signature: ast.arguments) -> list[ast.arg]:
    """List every argument a signature declares, the starred ones included."""
    starred = [arg for arg in (signature.vararg, signature.kwarg) if arg is not None]
    return [*signature.posonlyargs, *signature.args, *signature.kwonlyargs, *starred]


def hints_in(source: PythonSource) -> list[Hint]:
    """Find every imprecise hint a module holds: annotations, aliases, the types it casts to."""
    module = ast.parse(source)
    found: list[Hint | None] = [_module_alias(statement) for statement in module.body]
    for node in ast.walk(module):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            found += [
                _annotation(arg.annotation) for arg in _arguments_of(node.args) if arg.annotation
            ]
            found += [_annotation(node.returns)] if node.returns is not None else []
        elif isinstance(node, ast.AnnAssign):
            aliased = _name(node.annotation) == TypeName("TypeAlias") and node.value is not None
            if aliased and isinstance(node.target, ast.Name) and node.value is not None:
                found.append(_alias(TypeName(node.target.id), node.value))
            else:
                found.append(_annotation(node.annotation))
        elif isinstance(node, ast.TypeAlias):
            found.append(_alias(TypeName(node.name.id), node.value))
        elif isinstance(node, ast.Call) and _name(node.func) == TypeName("cast"):
            found.append(_cast_type(node))
    return [hint for hint in found if hint is not None]


def _cast_type(call: ast.Call) -> Hint | None:
    """Judge the type a ``cast`` names, as it is passed: first, or as ``typ``."""
    named = [keyword.value for keyword in call.keywords if keyword.arg == "typ"]
    given = named + call.args[:1]
    return _annotation(given[0]) if given else None


def _line_of(text: ShellSource, offset: TextOffset) -> LineNumber:
    """Name the line of ``text`` an offset into it falls on."""
    return LineNumber(text.count("\n", 0, offset) + 1)


def probe_python(text: ShellSource) -> list[_Piece] | Prose:
    """Pull the Python a probe hands an interpreter, or say which run it could not read.

    Every heredoc's body is set aside first, its lines left blank so the rest
    keeps its numbering: a heredoc read by an interpreter on ``-`` is Python,
    any other is data, and shell text quoted inside either is never a run.
    Each run the shell text then holds has to be one of the forms read.
    """
    lines = text.split("\n")
    pieces: list[_Piece] = []
    at = 0
    while at < len(lines):
        opener = _HEREDOC.search(lines[at])
        if opener is None:
            at += 1
            continue
        tabs, _, delimiter = opener.groups()
        end = next(
            (
                index
                for index in range(at + 1, len(lines))
                if (lines[index].lstrip("\t") if tabs else lines[index]) == delimiter
            ),
            None,
        )
        if end is None:
            return Prose(f"line {at + 1}: the heredoc {delimiter} never ends")
        if _PYTHON_HEREDOC.search(lines[at]):
            body = PythonSource("\n".join(lines[at + 1 : end]))
            pieces.append(_Piece(body, LineNumber(at + 2)))
        lines[at + 1 : end] = [""] * (end - at - 1)
        at = end + 1
    shell = ShellSource("\n".join(lines))
    read = collections.Counter(
        _line_of(shell, TextOffset(match.start()))
        for match in (*_INLINE.finditer(shell), *_INLINE_QUOTED.finditer(shell))
    )
    pieces.extend(
        _Piece(PythonSource(match.group(1)), _line_of(shell, TextOffset(match.start(1))))
        for match in _INLINE.finditer(shell)
    )
    pieces.extend(
        _Piece(
            PythonSource(_SHELL_ESCAPE.sub(r"\1", match.group(1))),
            _line_of(shell, TextOffset(match.start(1))),
        )
        for match in _INLINE_QUOTED.finditer(shell)
    )
    read.update(
        _line_of(shell, TextOffset(match.start())) for match in _PYTHON_HEREDOC.finditer(shell)
    )
    runs = collections.Counter(
        _line_of(shell, TextOffset(match.start())) for match in _RUN.finditer(shell)
    )
    unread = sorted(line for line, count in runs.items() if count > read[line])
    if unread:
        return Prose(
            f"line {unread[0]}: Python handed to an interpreter in a form this lens does not read"
        )
    return pieces


def hints_of(rel: RelPath, text: PythonSource | ShellSource) -> list[Hint] | Prose:
    """Find one file's imprecise hints, a module's or a probe's, or say why it cannot be read."""
    try:
        if not rel.endswith(".sh"):
            return hints_in(PythonSource(text))
        pieces = probe_python(ShellSource(text))
        if isinstance(pieces, str):
            return Prose(f"{rel}: {pieces}")
        return [
            hint._replace(line=LineNumber(piece.line + hint.line - 1))
            for piece in pieces
            for hint in hints_in(piece.source)
        ]
    except SyntaxError as error:
        return Prose(f"{rel}: line {error.lineno}: does not parse as Python: {error.msg}")


def in_scope(rel: RelPath) -> bool:
    """Say whether the lens reads a tracked file: Python outside the archive, or a probe."""
    if rel.startswith(".archive/"):
        return False
    return rel.endswith(".py") or (rel.startswith("probes/") and rel.endswith(".sh"))


def _observe(observed: Observed, rel: RelPath, hints: list[Hint]) -> None:
    """Add one file's hints to what has been observed."""
    for hint in hints:
        key = RowKey(rel, hint.text)
        observed.rows[key] = observed.rows.get(key, 0) + 1
        observed.lines.setdefault(key, []).append(hint.line)
        observed.faults[key] = observed.faults.get(key, frozenset()) | hint.faults


def observed_in_tree(root: Path) -> Observed | Prose:
    """Read every tracked file in scope under ``root``, or say which one could not be read."""
    observed = Observed({}, {}, {})
    for rel in git_ls_files(root):
        if not in_scope(rel):
            continue
        hints = hints_of(rel, PythonSource((root / rel).read_text(encoding="utf-8")))
        if isinstance(hints, str):
            return hints
        _observe(observed, rel, hints)
    return observed


def _unrecorded(observed: Observed, key: RowKey, recorded: RatchetRows, record: Path) -> None:
    """Print one row the file holds more of than the record allows."""
    lines = ", ".join(str(line) for line in sorted(observed.lines[key]))
    emit(f"{key.file}: line {lines}: {key.text}")
    for fault in sorted(observed.faults[key]):
        emit(f"    {fault}")
    emit(
        f"  the record allows {recorded.get(key, 0)} here and the file holds {observed.rows[key]}."
    )
    emit("  Name the type (AGENTS/python.md cat 8), or, with user approval, record it in")
    emit(f"  {record}:")
    emit(as_row(key.file, key.text, observed.rows[key]))


def report(
    observed: Observed,
    recorded: RatchetRows,
    *,
    record: Path = RECORD,
    files: set[RelPath] | None = None,
) -> ExitStatus:
    """Print every unrecorded hint and every stale row; name the exit status.

    ``files`` narrows the comparison to the files named, and to hints the
    record does not allow: a row a file under edit holds fewer of is the
    change the record follows, and the tree's run holds it to the record.
    """
    unrecorded = sorted(key for key, n in observed.rows.items() if n > recorded.get(key, 0))
    stale = (
        []
        if files is not None
        else sorted(key for key, n in recorded.items() if n > observed.rows.get(key, 0))
    )
    if files is not None:
        unrecorded = [key for key in unrecorded if key.file in files]
    for key in unrecorded:
        _unrecorded(observed, key, recorded, record)
    for key in stale:
        emit(f"{key.file}: a recorded row names more hints than the file holds")
        emit(f"    {key.text}")
        emit(f"  Its hints were typed: lower its count to {observed.rows.get(key, 0)}, or drop the")
        emit(f"  row when that is 0, in {record}, in the change that typed them.")
    if unrecorded or stale:
        emit(f"{len(unrecorded)} unrecorded, {len(stale)} stale")
        return OUT_OF_STEP
    emit(f"imprecise Python hints: {sum(observed.rows.values())}, every one recorded")
    return CLEAN


def print_record(observed: Observed) -> ExitStatus:
    """Print the tree's rows in the record's spelling, file by file."""
    for key in sorted(observed.rows):
        emit(as_row(key.file, key.text, observed.rows[key]))
    return CLEAN


def _parsed() -> _Arguments:
    """Read the command line."""
    parser = argparse.ArgumentParser(description="Hold Python type hints to the record.")
    _ = parser.add_argument("--root", type=Path, help="hold this tree, not the repository's")
    _ = parser.add_argument("--record", type=Path, help="the record --root's rows are held to")
    _ = parser.add_argument("--file", type=Path, help="read this file in place of the tree")
    _ = parser.add_argument("--as", dest="rel", help="the repository path --file stands for")
    _ = parser.add_argument(
        "--print-record",
        action="store_true",
        help="print the tree's rows as the record spells them",
    )
    arguments = parser.parse_args()
    rel = arguments.rel  # argparse hands the value over untyped; narrowed where it is read
    return _Arguments(
        cast("Path | None", arguments.root),
        cast("Path | None", arguments.record),
        cast("Path | None", arguments.file),
        RelPath(PurePosixPath(rel).as_posix()) if isinstance(rel, str) else None,
        cast("bool", arguments.print_record),
    )


def _observed_in_file(rel: RelPath, file: Path) -> Observed | Prose:
    """Read one file's text as the repository path it stands for, or say why it cannot be read."""
    observed = Observed({}, {}, {})
    if in_scope(rel):
        hints = hints_of(rel, PythonSource(file.read_text(encoding="utf-8")))
        if isinstance(hints, str):
            return hints
        _observe(observed, rel, hints)
    return observed


def main() -> ExitStatus:
    """Compare the tree, or one file, with the record; name the exit status."""
    arguments = _parsed()
    if (arguments.root is None) != (arguments.record is None):
        emit("--root and --record go together: a tree, and the record its rows are held to")
        return UNREADABLE
    root = arguments.root.resolve() if arguments.root is not None else git_toplevel()
    record = arguments.record.resolve() if arguments.record is not None else RECORD
    if arguments.file is not None and arguments.rel is None:
        emit("--file needs --as, the repository path it stands for")
        return UNREADABLE
    one = arguments.rel if arguments.file is not None else None
    observed = (
        _observed_in_file(one, arguments.file)
        if one is not None and arguments.file is not None
        else observed_in_tree(root)
    )
    if isinstance(observed, str):
        emit(observed)
        return UNREADABLE
    if arguments.print_record:
        return print_record(observed)
    recorded = read_ratchet_rows(root, record, _RECORD_LIST)
    if isinstance(recorded, str):
        emit(recorded)
        return UNREADABLE
    return report(observed, recorded, record=record, files={one} if one is not None else None)


if __name__ == "__main__":
    sys.exit(main())
