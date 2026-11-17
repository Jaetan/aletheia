# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every argument crosses into the library whole, whatever its entry declares.

An entry declared without argument types takes a bare Python ``int`` as a C
``int``, its high half dropped, so a call handing it an address under a mutant
that clears the entry's ``argtypes`` frees or reads one the library never
handed out, and whether that ends the process rests on where the heap was
placed.  So every argument of a call into the library is spelled as what
crosses whole: ``None``; a pointer or scalar made where it crosses by
``ctypes`` (``ctypes.c_void_p``, ``byref``, ``cast``, ``pointer``, a ``c_``
type) or by a module ``NewType`` of ``c_void_p``; a structure field every structure of the binding
declares as a pointer; a parameter annotated as ``c_void_p`` or such a
``NewType``; a list, a tuple, a starred list or a conditional of these; or a
name every assignment of which in its function is one of these.  A call into
the library is a call of an
``aletheia_*`` attribute, or of a loop variable over a literal of them.  The
Python under ``python/``, ``benchmarks/``, ``examples/`` and ``tools/`` is
read, vendored code and mutmut's copy left out.
"""

from __future__ import annotations

import ast
import ctypes
import os
from pathlib import Path
from typing import TYPE_CHECKING, Final, Literal, NamedTuple, NewType

import pytest
from _repo_root import REPO_ROOT

import aletheia.client

if TYPE_CHECKING:
    from collections.abc import Iterator

# A source file's text, a line of it, and the source text of one argument.
SourceText = NewType("SourceText", str)
LineNumber = NewType("LineNumber", int)
ArgumentText = NewType("ArgumentText", str)
# An identifier: an entry, a parameter, a field or a local name.
Identifier = NewType("Identifier", str)
# How many names a chain of assignments has passed through, and how many calls
# into the library a source holds.
NameDepth = NewType("NameDepth", int)
CallCount = NewType("CallCount", int)

_ROOTS: Final = (
    "python/aletheia",
    "python/tests",
    "python/benchmarks",
    "benchmarks",
    "examples",
    "tools",
)
_SKIPPED_DIRECTORIES: Final = frozenset(
    {"_vendor", "mutants", ".venv", "__pycache__", "mutation", "results"}
)
_POINTER_MAKERS: Final = frozenset({"c_void_p", "byref", "cast", "pointer"})
# A chain of assignments longer than this is refused rather than followed.
_MAX_NAME_DEPTH: Final = NameDepth(8)


class Crossing(NamedTuple):
    """An argument handed to an entry in a form that may cross as a bare integer."""

    line: LineNumber
    entry: Identifier
    argument: ArgumentText


class Scan(NamedTuple):
    """The calls into the library a source holds, and the arguments that may cross bare."""

    calls: CallCount
    refused: list[Crossing]


def _binding_structures() -> list[type[ctypes.Structure]]:
    """Answer every structure the binding declares (``aletheia.client`` loads them all)."""
    module = aletheia.client.__name__ + "._ffi"
    return [c for c in ctypes.Structure.__subclasses__() if c.__module__ == module]


def _takes(structure: type[ctypes.Structure], field: Identifier, value: Literal[1, b""]) -> bool:
    """Answer whether a fresh structure's field accepts ``value``."""
    try:
        setattr(structure(), field, value)
    except TypeError:
        return False
    return True


def _pointer_fields() -> frozenset[Identifier]:
    """Answer the field names that cross whole in every binding structure that has one.

    A field crosses whole when it refuses an integer, as a pointer does, or takes
    bytes, as a C string does; one that takes an integer and refuses bytes reads
    back as one.
    """
    kinds: dict[Identifier, set[bool]] = {}
    for structure in _binding_structures():
        for declared in vars(structure).values():
            if isinstance(declared, ctypes.CField):
                field = Identifier(declared.name)
                whole = not _takes(structure, field, 1) or _takes(structure, field, b"")
                kinds.setdefault(field, set()).add(whole)
    return frozenset(name for name, seen in kinds.items() if seen == {True})


def _own_nodes(scope: ast.AST) -> Iterator[ast.AST]:
    """Yield the nodes of a scope's body, not descending into a nested function or class."""
    pending = list(ast.iter_child_nodes(scope))
    while pending:
        node = pending.pop()
        yield node
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
            pending.extend(ast.iter_child_nodes(node))


def _is_entry(node: ast.expr) -> bool:
    """Answer whether ``node`` names an entry of the library."""
    return isinstance(node, ast.Attribute) and node.attr.startswith("aletheia_")


def _is_pointer_type(node: ast.expr | None, aliases: frozenset[Identifier]) -> bool:
    """Answer whether an annotation names ``c_void_p`` or a module ``NewType`` of it."""
    if isinstance(node, ast.Attribute):
        return node.attr == "c_void_p"
    return isinstance(node, ast.Name) and (node.id == "c_void_p" or node.id in aliases)


class _Scope:
    """The names one function binds: its parameters, its assignments and its entry loops."""

    def __init__(
        self, scope: ast.AST, outer: _Scope | None, aliases: frozenset[Identifier]
    ) -> None:
        self.outer = outer
        self.aliases = aliases
        self.parameters: dict[Identifier, ast.expr | None] = {}
        self.bound: dict[Identifier, list[ast.expr]] = {}
        self.entries: set[Identifier] = set()
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            arguments = scope.args
            for argument in [*arguments.posonlyargs, *arguments.args, *arguments.kwonlyargs]:
                self.parameters[Identifier(argument.arg)] = argument.annotation
        for node in _own_nodes(scope):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self.bound.setdefault(Identifier(target.id), []).append(node.value)
            elif (
                isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value
            ):
                self.bound.setdefault(Identifier(node.target.id), []).append(node.value)
            elif isinstance(node, ast.For):
                self._note_entry_rows(node)

    def _note_entry_rows(self, statement: ast.For) -> None:
        """Record the loop variables that run over a literal of entries."""
        if not isinstance(statement.iter, (ast.Tuple, ast.List)):
            return
        rows = statement.iter.elts
        if isinstance(statement.target, ast.Name) and rows and all(_is_entry(row) for row in rows):
            self.entries.add(Identifier(statement.target.id))
        if isinstance(statement.target, ast.Tuple):
            for at, name in enumerate(statement.target.elts):
                if (
                    isinstance(name, ast.Name)
                    and rows
                    and all(
                        isinstance(row, ast.Tuple)
                        and len(row.elts) > at
                        and _is_entry(row.elts[at])
                        for row in rows
                    )
                ):
                    self.entries.add(Identifier(name.id))

    def calls_entry(self, call: ast.Call) -> bool:
        """Answer whether ``call`` calls an entry of the library."""
        if _is_entry(call.func):
            return True
        return isinstance(call.func, ast.Name) and call.func.id in self.entries

    def crosses_whole(
        self, node: ast.expr, fields: frozenset[Identifier], depth: NameDepth = NameDepth(0)
    ) -> bool:
        """Answer whether ``node`` is spelled as what crosses an entry whole."""
        parts = _parts(node)
        if parts is not None:
            return all(self.crosses_whole(part, fields, depth) for part in parts)
        if isinstance(node, ast.Name):
            return depth < _MAX_NAME_DEPTH and self.name_crosses_whole(
                Identifier(node.id), fields, NameDepth(depth + 1)
            )
        return _made_whole(node, fields, self.aliases)

    def name_crosses_whole(
        self, name: Identifier, fields: frozenset[Identifier], depth: NameDepth
    ) -> bool:
        """Answer whether a name is a pointer-typed parameter or bound only to what crosses."""
        if name in self.parameters:
            return _is_pointer_type(self.parameters[name], self.aliases)
        if name in self.bound:
            return all(self.crosses_whole(value, fields, depth) for value in self.bound[name])
        return self.outer is not None and self.outer.name_crosses_whole(name, fields, depth)


def _parts(node: ast.expr) -> list[ast.expr] | None:
    """Answer the parts a conditional, a list, a tuple or a starred list crosses as, or None."""
    if isinstance(node, ast.IfExp):
        return [node.body, node.orelse]
    if isinstance(node, (ast.List, ast.Tuple)):
        return list(node.elts)
    if isinstance(node, (ast.ListComp, ast.GeneratorExp)):
        return [node.elt]
    if isinstance(node, ast.Starred):
        return [node.value]
    return None


def _made_whole(
    node: ast.expr, fields: frozenset[Identifier], aliases: frozenset[Identifier]
) -> bool:
    """Answer whether ``node`` is ``None``, a ``ctypes`` value made in place or a pointer field."""
    if isinstance(node, ast.Constant):
        return node.value is None
    if isinstance(node, ast.Call):
        made = node.func
        if isinstance(made, ast.Name):
            return made.id in aliases
        if not (isinstance(made, ast.Attribute) and isinstance(made.value, ast.Name)):
            return False
        return made.value.id == "ctypes" and (
            made.attr in _POINTER_MAKERS or made.attr.startswith("c_")
        )
    return isinstance(node, ast.Attribute) and node.attr in fields


def _pointer_aliases(module: ast.Module) -> frozenset[Identifier]:
    """Answer the module names bound to ``NewType(..., ctypes.c_void_p)``."""
    aliases: set[Identifier] = set()
    for node in module.body:
        value = node.value if isinstance(node, ast.Assign) else None
        if (
            isinstance(node, ast.Assign)
            and isinstance(value, ast.Call)
            and getattr(value.func, "id", "") == "NewType"
            and len(value.args) == 2
            and _is_pointer_type(value.args[1], frozenset())
        ):
            aliases.update(Identifier(t.id) for t in node.targets if isinstance(t, ast.Name))
    return frozenset(aliases)


def scan(source: SourceText, fields: frozenset[Identifier]) -> Scan:
    """Answer the calls into the library in ``source`` and each argument that may cross bare."""
    module = ast.parse(source)
    aliases = _pointer_aliases(module)
    found: list[Crossing] = []
    calls: list[ast.Call] = []

    def visit(scope: ast.AST, outer: _Scope | None) -> None:
        names = _Scope(scope, outer, aliases)
        for node in _own_nodes(scope):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                visit(node, names)
            elif isinstance(node, ast.Call) and names.calls_entry(node):
                calls.append(node)
                entry = ast.unparse(node.func).rsplit(".", 1)[-1]
                arguments = [*node.args, *(keyword.value for keyword in node.keywords)]
                found.extend(
                    Crossing(
                        LineNumber(node.lineno),
                        Identifier(entry),
                        ArgumentText(ast.unparse(argument)),
                    )
                    for argument in arguments
                    if not names.crosses_whole(argument, fields)
                )

    visit(module, None)
    return Scan(CallCount(len(calls)), sorted(found))


def _python_sources() -> Iterator[Path]:
    """Yield every Python file under the roots, the skipped directories left out."""
    for root in _ROOTS:
        for directory, subdirectories, names in os.walk(REPO_ROOT / root):
            subdirectories[:] = sorted(d for d in subdirectories if d not in _SKIPPED_DIRECTORIES)
            yield from (Path(directory) / name for name in sorted(names) if name.endswith(".py"))


_FIELDS: Final = _pointer_fields()


def test_the_binding_declares_its_structures_and_their_pointer_fields() -> None:
    """The structures are found, a pointer field passes and an address field does not."""
    assert len(_binding_structures()) > 1
    assert Identifier("data") in _FIELDS
    assert Identifier("err") not in _FIELDS


@pytest.mark.parametrize(
    ("source", "refused"),
    [
        ("def f(lib, pointer):\n    lib.aletheia_free_str(pointer)\n", "pointer"),
        ("def f(lib, out):\n    lib.aletheia_free_str(out.err)\n", "out.err"),
        (
            "def f(lib):\n    lib.aletheia_free_str(lib.aletheia_format_dbc(None))\n",
            "lib.aletheia_format_dbc(None)",
        ),
        (
            "def f(lib, state):\n    for entry in (lib.aletheia_close,):\n        entry(state)\n",
            "state",
        ),
        (
            (
                "def f(lib, state, out):\n"
                "    for entry, o in ((lib.aletheia_close, out),):\n"
                "        entry(state)\n"
            ),
            "state",
        ),
        ("def f(lib, state: int):\n    lib.aletheia_close(state)\n", "state"),
        ("def f(lib, raw):\n    handle = raw\n    lib.aletheia_close(handle)\n", "handle"),
        (
            (
                "def f(lib, raw, ok):\n"
                "    h = ctypes.c_void_p(raw) if ok else raw\n"
                "    lib.aletheia_close(h)\n"
            ),
            "h",
        ),
        ("def f(lib, size):\n    lib.aletheia_take(size=size)\n", "size"),
        ('def f(lib, p):\n    lib.aletheia_free_str(cast("int", p))\n', "cast('int', p)"),
        ("def f(lib, p):\n    lib.aletheia_free_str(c_long(p))\n", "c_long(p)"),
    ],
)
def test_an_argument_that_may_cross_as_an_integer_is_refused(
    source: SourceText, refused: ArgumentText
) -> None:
    """A bare parameter, an address field, an answered address and a bare handle are refused.

    So is a value no ``ctypes`` maker made: a cast, or a callable merely named like one.
    """
    assert [crossing.argument for crossing in scan(source, _FIELDS).refused] == [refused]


@pytest.mark.parametrize(
    "source",
    [
        "def f(lib, address):\n    lib.aletheia_free_str(ctypes.c_void_p(address))\n",
        "def f(lib, state: ctypes.c_void_p):\n    lib.aletheia_close(state)\n",
        (
            'Handle = NewType("Handle", ctypes.c_void_p)\n'
            "def f(lib, state: Handle):\n"
            "    lib.aletheia_close(state)\n"
        ),
        (
            'Handle = NewType("Handle", ctypes.c_void_p)\n'
            "def f(lib, raw):\n"
            "    h = Handle(ctypes.c_void_p(raw))\n"
            "    lib.aletheia_close(h)\n"
        ),
        (
            "def f(lib, t, out):\n"
            "    text = ctypes.byref(t)\n"
            "    lib.aletheia_process(None, text, ctypes.byref(out))\n"
        ),
        (
            "def f(lib, t):\n"
            "    a = None if t is None else ctypes.byref(t)\n"
            "    lib.aletheia_process(None, a)\n"
        ),
        "def f(lib, out):\n    lib.aletheia_free_buf(out.data)\n",
        (
            "def f(lib, ks):\n"
            "    args = [ctypes.byref(k()) for k in ks]\n"
            "    lib.aletheia_run(*args)\n"
        ),
        "def f(lib, n):\n    lib.aletheia_take(ctypes.c_uint32(n))\n",
        "def f(other, pointer):\n    other.free(pointer)\n",
    ],
)
def test_an_argument_spelled_as_what_crosses_whole_passes(source: SourceText) -> None:
    """A pointer made where it crosses, a pointer-typed parameter and a pointer field pass."""
    assert scan(source, _FIELDS).refused == []


def test_every_call_into_the_library_hands_each_argument_whole() -> None:
    """No call in the tree hands an entry an argument that may cross as a bare integer.

    The walk reaches the wrapper that frees every kernel string and finds its
    call, so a walk that read nothing cannot pass.
    """
    walked = {
        path.relative_to(REPO_ROOT).as_posix(): scan(
            SourceText(path.read_text(encoding="utf-8")), _FIELDS
        )
        for path in _python_sources()
    }
    assert walked["python/aletheia/client/_ffi.py"].calls > 0
    found = [
        f"{path}:{crossing.line}: {crossing.entry}({crossing.argument})"
        for path, result in walked.items()
        for crossing in result.refused
    ]
    assert found == []
