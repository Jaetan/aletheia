# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The route by which a module of ``python/tests/`` imports the repo-root ``tools`` package.

The mutation-setup gate (``tools/check_mutation_setup.py``, its invariant 2)
refuses a test the lane runs whose collection imports ``tools``; this reads
what a collection runs: the module's own imports at its top level, those of
the helpers of ``python/tests/`` it imports, and those a fixture, a decorator
or a signature runs at collection, and names the route an import takes.
"""

from __future__ import annotations

import ast
import importlib.util
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NewType, NoReturn

from tools.check_mutation_setup_lanes import REPO_ROOT, exit_unreadable, read_or_exit

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping, Sequence
    from pathlib import Path

# The directory whose modules are read; the tests point it at a planted tree.
PY_TESTS_DIR = REPO_ROOT / "python" / "tests"

# A module as an import statement names it.
ModuleName = NewType("ModuleName", str)
# A function as its ``def`` names it.
FunctionName = NewType("FunctionName", str)
# A decorator as a name spells it.
DecoratorName = NewType("DecoratorName", str)
# The functions a name reaches in one scope, each name's every definition.
type Scope = Mapping[FunctionName, Sequence[ast.FunctionDef]]


def route_text(route: list[ModuleName]) -> Prose:
    """Name the helpers an import of ``tools`` goes through, or nothing for a direct one."""
    return Prose(f" through {', '.join(f'tests/{name}.py' for name in route)}" if route else "")


def tools_route(path: Path, visited: set[Path]) -> list[ModuleName] | None:
    """Return the helpers through which collecting ``path`` imports ``tools``, or None.

    The list is empty for a module that imports ``tools`` itself, whatever
    else it imports.  A helper is a module or a package of ``python/tests/``
    imported by its name, as pytest's path makes them importable, a dotted
    name reaching each package on its way; one already read is not read
    again, so a cycle ends.
    """
    visited.add(path)
    try:
        tree = ast.parse(read_or_exit(path), filename=path)
    except SyntaxError as exc:
        exit_unreadable(path, Prose(f"{exc.msg} at line {exc.lineno}"))
    imported = list(_imports_at_collection(tree, path))
    if any(module.partition(".")[0] == "tools" for module in imported):
        return []
    for module in imported:
        for helper in _helper_files(module):
            if helper not in visited:
                route = tools_route(helper, visited)
                if route is not None:
                    name = helper.relative_to(PY_TESTS_DIR).with_suffix("").as_posix()
                    return [ModuleName(name), *route]
    return None


def _helper_files(module: ModuleName) -> list[Path]:
    """Return the files of ``python/tests/`` importing ``module`` runs, outermost first."""
    files: list[Path] = []
    parts = module.split(".")
    for depth in range(1, len(parts) + 1):
        stem = PY_TESTS_DIR.joinpath(*parts[:depth])
        candidates = (stem.with_suffix(".py"), stem / "__init__.py")
        found = next((f for f in candidates if f.is_file()), None)
        if found is None:
            break
        files.append(found)
    return files


def _imports_at_collection(tree: ast.Module, path: Path) -> Iterator[ModuleName]:
    """Yield each module an import under ``tree`` names, where importing the module runs it.

    The walk reads the source as written, never as Python resolves it: a
    name is read as it is spelled, in the scope where it is written, and
    every branch is read as running.  So every statement's body is read, a
    class's, a ``try``'s, each handler's and each loop's among them, and ``if
    TYPE_CHECKING:`` reads its ``else`` alone.  A function's body is read
    where a statement read calls it by its own name, a bare decorator
    included, the name looked up in the scope of the call (the module's, a
    class body's or a function body's own definitions, the enclosing ones
    behind them, every definition of a name kept since a later one hiding an
    earlier is a lint failure) and the body read once, in the scope it
    closes over, which a class body's names are not part of.  An annotation
    is read where pytest's collection evaluates a signature: a ``test*``
    function's or coroutine's, a ``pytest_*`` hook's and a fixture's, in the
    module or a ``Test*`` class of it, none where the module imports
    ``annotations`` from ``__future__``.  A fixture is a function decorated
    by a name or an attribute spelled ``fixture``, or by the name ``from
    pytest import fixture as`` binds.

    What Python reaches through a name it resolves as it runs is left
    unread: a function called through an attribute, an alias or a
    rebinding; what constructing a class runs (``__init__``,
    ``__init_subclass__``, a metaclass); a test, class or fixture pytest
    finds under another name (bound to a ``test*`` or ``Test*`` name,
    inherited from a class otherwise named, built in a called function, a
    fixture made by calling ``fixture``); a fixture of a unittest class not
    named ``Test*``; a helper's function; and code run from a string by
    ``exec`` or ``eval``.  So is what Python defers, even where the code
    runs it at once: a lambda's body, a generator expression's past its
    first iterable, a coroutine's, a type parameter, a ``type`` alias's
    value.  What the walk reads but neither Python nor pytest runs is read
    all the same: a branch not taken, a definition a later one hides or
    ``del`` removes, a test a decorator replaces, a decorator spelled
    ``fixture`` that is not pytest's, a helper module's tests and fixtures,
    a ``pytest_*`` function pytest does not call, a test or ``Test*`` class
    whose own or module's ``__test__`` is false, a ``Test*`` class pytest
    passes over for an ``__init__`` or a ``__new__``, and the test methods
    of a ``Test*`` unittest class, whose signatures pytest leaves
    unevaluated.

    A call of ``__import__`` names the module its first argument spells; one
    of ``import_module`` names it relative to the package its second spells;
    either naming a module by an expression stops the gate, since the gate
    reads a name spelled, and ``path`` names the file then.  ``from p import
    n`` names ``p`` and ``p.n``, since ``n`` may be a module of the package
    ``p``.  A relative import names a module of the helper package it sits
    in, and nothing in a test, since the tests are no package.
    """
    run = not _postpones_annotations(tree)
    walk = _Walk(path, _package_of(path), _fixture_spellings(tree))
    return _imports_run_by(tree, {}, walk, annotations_run=run)


@dataclass
class _Walk:
    """What one module's walk carries.

    Its file and helper package, the names its fixtures are spelled by, each
    function's scope, and the functions read.
    """

    path: Path
    package: ModuleName
    fixtures: frozenset[DecoratorName]
    scopes: dict[ast.FunctionDef, Scope] = field(default_factory=dict)
    entered: set[ast.FunctionDef] = field(default_factory=set)


def _imports_run_by(
    node: ast.AST, outer: Scope, walk: _Walk, *, annotations_run: bool
) -> Iterator[ModuleName]:
    """Yield each module an import under ``node`` names, as running ``node`` runs it.

    ``outer`` is the scope around ``node``, whose own definitions hide its
    names; a function called by name is read once, in the scope it closes over.
    ``annotations_run`` says whether pytest's collection evaluates the
    annotations of the tests and fixtures ``node``'s own statements define.
    """
    defined = _functions_defined(node)
    scope: Scope = {**outer, **defined}
    closure = outer if isinstance(node, ast.ClassDef) else scope
    for functions in defined.values():
        for function in functions:
            _ = walk.scopes.setdefault(function, closure)
    for child in _statements_run(node):
        yield from _modules_named(child, walk)
        if not isinstance(child, ast.FunctionDef | ast.AsyncFunctionDef):
            within = annotations_run and _collected_within(child)
            yield from _imports_run_by(child, scope, walk, annotations_run=within)
        for called in _called_by_name(child):
            yield from _imports_of_calling(called, scope, walk)
        for annotation in _signature_collected(child, walk) if annotations_run else []:
            yield from _modules_named(annotation, walk)
            for called in _called_by_name(annotation):
                yield from _imports_of_calling(called, scope, walk)


def _imports_of_calling(called: FunctionName, scope: Scope, walk: _Walk) -> Iterator[ModuleName]:
    """Yield what calling ``called`` imports: each function the name has in ``scope``, read once."""
    for function in scope.get(called, ()):
        if function not in walk.entered:
            walk.entered.add(function)
            yield from _imports_run_by(function, walk.scopes[function], walk, annotations_run=False)


def _collected_within(statement: ast.AST) -> bool:
    """Say whether pytest collects in ``statement``'s body where it collects around it.

    A compound statement's body is its scope's; a class is collected by its
    ``Test`` prefix.
    """
    return not isinstance(statement, ast.ClassDef) or statement.name.startswith("Test")


def _signature_collected(statement: ast.AST, walk: _Walk) -> list[ast.Expr]:
    """Return the annotations pytest's collection evaluates in ``statement``'s signature.

    It reads a ``test*`` function's or coroutine's, a ``pytest_*`` hook's and a
    fixture's; each annotation is returned as the expression statement it then
    runs as.
    """
    if not isinstance(statement, ast.FunctionDef | ast.AsyncFunctionDef) or not (
        statement.name.startswith(("test", "pytest_"))
        or any(_names_fixture(decorator, walk) for decorator in statement.decorator_list)
    ):
        return []
    arguments = statement.args
    parameters = (
        *arguments.posonlyargs,
        *arguments.args,
        *arguments.kwonlyargs,
        arguments.vararg,
        arguments.kwarg,
    )
    annotations = [
        parameter.annotation
        for parameter in parameters
        if parameter is not None and parameter.annotation is not None
    ]
    if statement.returns is not None:
        annotations.append(statement.returns)
    return [ast.Expr(value=annotation) for annotation in annotations]


def _postpones_annotations(tree: ast.Module) -> bool:
    """Say whether ``tree`` imports ``annotations`` from ``__future__``, making each a string."""
    return any(
        isinstance(statement, ast.ImportFrom)
        and statement.module == "__future__"
        and any(alias.name == "annotations" for alias in statement.names)
        for statement in tree.body
    )


def _fixture_spellings(tree: ast.Module) -> frozenset[DecoratorName]:
    """Return the names a decorator spells pytest's ``fixture`` by in ``tree``.

    ``fixture`` itself, and each name ``from pytest import fixture as`` binds.
    """
    return frozenset(
        {DecoratorName("fixture")}
        | {
            DecoratorName(alias.asname)
            for statement in tree.body
            if isinstance(statement, ast.ImportFrom) and statement.module == "pytest"
            for alias in statement.names
            if alias.name == "fixture" and alias.asname is not None
        }
    )


def _names_fixture(decorator: ast.expr, walk: _Walk) -> bool:
    """Say whether ``decorator`` spells pytest's ``fixture``, bare, as an attribute or called."""
    target = decorator.func if isinstance(decorator, ast.Call) else decorator
    return (isinstance(target, ast.Name) and DecoratorName(target.id) in walk.fixtures) or (
        isinstance(target, ast.Attribute) and target.attr == "fixture"
    )


def _package_of(path: Path) -> ModuleName:
    """Return the package of the module at ``path``, as Python sets its ``__package__``.

    It is the dotted path of the module's directory below ``python/tests/``,
    empty for a test or helper beside it, where a relative import has no
    package to resolve in.
    """
    return ModuleName(".".join(path.parent.relative_to(PY_TESTS_DIR).parts))


def _modules_named(statement: ast.AST, walk: _Walk) -> Iterator[ModuleName]:
    """Yield each module ``statement`` names itself: an import's, or a call's in its expressions."""
    if isinstance(statement, ast.Import):
        yield from (ModuleName(alias.name) for alias in statement.names)
    elif isinstance(statement, ast.ImportFrom):
        base = _from_base(statement, walk.package)
        if base is not None:
            yield base
            yield from (ModuleName(f"{base}.{alias.name}") for alias in statement.names)
    for expression in _expressions_run(statement):
        if isinstance(expression, ast.Call):
            named = _module_a_call_imports(expression, walk.path)
            if named is not None:
                yield named


def _from_base(statement: ast.ImportFrom, package: ModuleName) -> ModuleName | None:
    """Return the module ``from ... import`` reads its names from, None where none resolves.

    A relative one resolves in ``package``; outside a package, or above its
    top, Python refuses it, and it names nothing.
    """
    if statement.level == 0:
        return None if statement.module is None else ModuleName(statement.module)
    relative = "." * statement.level + (statement.module or "")
    try:
        return ModuleName(importlib.util.resolve_name(relative, package))
    except ImportError:
        return None


def _functions_defined(node: ast.AST) -> dict[FunctionName, list[ast.FunctionDef]]:
    """Return the functions ``node``'s own running statements define, each name's every one.

    A nested function's or class's body defines its own, not read here.
    """
    defined: dict[FunctionName, list[ast.FunctionDef]] = {}
    pending: list[ast.AST] = [node]
    while pending:
        for child in _statements_run(pending.pop()):
            if isinstance(child, ast.FunctionDef):
                defined.setdefault(FunctionName(child.name), []).append(child)
            elif not isinstance(child, ast.AsyncFunctionDef | ast.ClassDef):
                pending.append(child)
    return defined


def _statements_run(node: ast.AST) -> list[ast.AST]:
    """Return what nested in ``node`` runs when ``node`` does, as module import runs it."""
    if isinstance(node, ast.If) and _names_type_checking(node.test):
        return [*node.orelse]
    return [
        child
        for child in ast.iter_child_nodes(node)
        if isinstance(child, ast.stmt | ast.ExceptHandler | ast.match_case)
    ]


def _expressions_run(node: ast.AST) -> Iterator[ast.expr]:
    """Yield every expression that runs when ``node`` does, a nested statement's left to it."""
    for child in _children_run(node):
        if isinstance(child, ast.expr):
            yield child
        yield from _expressions_run(child)


def _children_run(node: ast.AST) -> list[ast.AST]:
    """Return the children of ``node`` that run when it does.

    A nested statement runs on its own; an annotation, a type parameter and a
    ``type`` alias's value are deferred; of a lambda its defaults run, of a
    generator expression its first iterable.
    """
    if isinstance(node, ast.Lambda):
        return [node.args]
    if isinstance(node, ast.GeneratorExp):
        return [node.generators[0].iter]
    deferred = {id(getattr(node, name, None)) for name in ("annotation", "returns")}
    if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef | ast.TypeAlias):
        deferred |= {id(parameter) for parameter in node.type_params}
    if isinstance(node, ast.TypeAlias):
        deferred.add(id(node.value))
    return [
        child
        for child in ast.iter_child_nodes(node)
        if id(child) not in deferred and not isinstance(child, ast.stmt)
    ]


def _called_by_name(statement: ast.AST) -> Iterator[FunctionName]:
    """Yield each function a running ``statement`` calls by bare name, bare decorators included."""
    for expression in _expressions_run(statement):
        if isinstance(expression, ast.Call) and isinstance(expression.func, ast.Name):
            yield FunctionName(expression.func.id)
    if isinstance(statement, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef):
        yield from (
            FunctionName(decorator.id)
            for decorator in statement.decorator_list
            if isinstance(decorator, ast.Name)
        )


def _names_type_checking(test: ast.expr) -> bool:
    """Say whether ``test`` is ``TYPE_CHECKING``, bare or as an attribute."""
    return (isinstance(test, ast.Name) and test.id == "TYPE_CHECKING") or (
        isinstance(test, ast.Attribute) and test.attr == "TYPE_CHECKING"
    )


def _module_a_call_imports(call: ast.Call, path: Path) -> ModuleName | None:
    """Return the module a ``__import__`` or ``import_module`` call spells, None for another call.

    A module, or the package a relative one rests on, that the call names by
    an expression stops the gate, naming ``path``.
    """
    callee = call.func
    name = (
        callee.id
        if isinstance(callee, ast.Name)
        else callee.attr
        if isinstance(callee, ast.Attribute)
        else None
    )
    if name not in {"__import__", "import_module"}:
        return None
    first = call.args[0] if call.args else None
    if not (isinstance(first, ast.Constant) and isinstance(first.value, str)):
        _exit_at(call, path, Prose("by an expression, which this gate reads only spelled"))
    if name == "__import__" or not first.value.startswith("."):
        return ModuleName(first.value)
    package = (
        call.args[1]
        if len(call.args) > 1
        else next((keyword.value for keyword in call.keywords if keyword.arg == "package"), None)
    )
    if not (isinstance(package, ast.Constant) and isinstance(package.value, str)):
        _exit_at(call, path, Prose("relative to a package it does not spell"))
    try:
        return ModuleName(importlib.util.resolve_name(first.value, package.value))
    except ImportError as exc:
        _exit_at(call, path, Prose(f"above its package: {exc}"))


def _exit_at(call: ast.Call, path: Path, how: Prose) -> NoReturn:
    """Stop the gate at a dynamic import whose module it cannot name, saying ``how`` it is named."""
    exit_unreadable(path, Prose(f"the import at line {call.lineno} names its module {how}"))
