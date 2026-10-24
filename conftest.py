# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Repo-root conftest — harness for `pytest --markdown-docs`.

Doc-example harness per AGENTS/python.md cat 32. Every Python fence of the
documents ``DOC_EXAMPLE_DOCS`` names in ``tools/_ci_steps.py``, and of the
docstrings of the package ``DOC_EXAMPLE_PACKAGE`` names, is collected and
executed end-to-end against the real FFI. A module's docstrings are read from
its source (``source_docstring_fences``), never by importing it.

A fence that names a file shipped under ``examples/`` (``vehicle.dbc``,
``drive.log``) runs against that file, so its checks are held to the signals a
reader's copy carries. The fakes below paper over every other path a fence
names (``drive.blf``, ``highway.asc``, ``vehicle_checks.xlsx``,
``checks.yaml``) so doc examples stay readable while still running against
live code:

* loader wrappers (``dbc_to_json``, ``iter_can_log``, ...) load a shipped file
  the path names, and otherwise return ``vehicle.dbc`` or an empty iterable;
  this keeps the narrative of the fence faithful while side-stepping missing
  files. ``load_checks`` parses a ``str`` as the YAML text it is.
* a ``dbc`` loaded from ``vehicle.dbc`` and a ``client`` that parsed it are
  injected, so fences that reuse names from a prior narrative block (e.g.
  PYTHON_API Examples 2–4 referencing the ``dbc`` Example 1 loads from
  ``vehicle.dbc``) resolve without ``continuation``-chaining every block,
  against the DBC that block loads.

Every fence runs against the forwarding stand-in kernel, which hands each
call to the built library and logs each refusal the library answers. A fence
fails unless its refusals are exactly the codes named by a
``<!-- refuses: <code> ... -->`` line directly above it, so a fence that
discards a refused call fails rather than passing on its run alone.

Scope: this conftest is only loaded when pytest's rootdir resolves to the
repo root (``--markdown-docs`` runs with ``--rootdir=<repo>``). The regular
``python/tests/`` suite uses ``python/pyproject.toml`` as its rootdir, so
these fakes do not leak into unit-test runs.  The harness runs with
``-o pythonpath=python/tests``, so it finds the stand-in kernels the way the
test suite does.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import TYPE_CHECKING, TypedDict, override

import pytest
from _stand_in import StandInName, stand_in_kernel
from pytest_markdown_docs._runners import DefaultRunner, register_runner
from pytest_markdown_docs.plugin import (
    FenceSyntax,
    MarkdownDocstringCodeModule,
    MarkdownInlinePythonItem,
    extract_fence_tests,
)

from tools._hosted_markdown import SourceText, docstrings
from tools.check_fence_marks import harness_markdown_it

import aletheia
import aletheia.can_log
import aletheia.checks
import aletheia.dbc
import aletheia.excel_loader
import aletheia.yaml_loader
from aletheia import (
    AletheiaClient,
    AletheiaError,
    BatchError,
    CANFrameTuple,
    CheckResult,
    FrameResponse,
    ProtocolError,
    Signal,
    ValidationError,
    eventually_always,
    infinitely_often,
    never,
)
from aletheia.can_log import iter_can_log, load_can_log
from aletheia.client._ffi import find_ffi_library
from aletheia.codes import ErrorCode
from aletheia.dbc import dbc_to_json
from aletheia.dsl import Predicate, Property
from aletheia.excel_loader import load_checks_from_excel, load_dbc_from_excel
from aletheia.types import DLCCode
from aletheia.yaml_loader import load_checks

if TYPE_CHECKING:
    from collections.abc import Callable, Generator, Iterator
    from types import ModuleType
    from typing import TypeAliasType

    from markdown_it import MarkdownIt
    from pytest_markdown_docs.definitions import FenceTestDefinition

    from aletheia import DBCDefinition

_REPO_ROOT = Path(__file__).parent

# The data files shipped under examples/, by name: each fence's directory holds a
# copy, so a path a fence names reaches the file a reader's checkout carries.
_SHIPPED = {
    path.name: path
    for path in (_REPO_ROOT / "examples").rglob("*")
    if path.suffix in {".dbc", ".log", ".xlsx", ".yaml"}
}

# The line directly above a fence that demonstrates refusals, naming their codes in order.
_REFUSES = re.compile(r"<!-- refuses: ([a-z0-9_]+(?: [a-z0-9_]+)*) -->")


def _doc_dbc() -> DBCDefinition:
    """Load ``vehicle.dbc``, the DBC the documents' narratives load and reuse."""
    return dbc_to_json(_SHIPPED["vehicle.dbc"])


def _shipped_or[**P, R](real: Callable[P, R], fake: Callable[[], R]) -> Callable[P, R]:
    """Wrap ``real`` to load a file the fence's directory holds, else call ``fake``."""

    def load(*args: P.args, **kwargs: P.kwargs) -> R:
        named = args[0] if args else None
        if isinstance(named, str | Path) and Path(named).is_file():
            return real(*args, **kwargs)
        return fake()

    return load


_harness_dbc_to_json = _shipped_or(dbc_to_json, _doc_dbc)


def _harness_convert_dbc_file[**P](*_args: P.args, **_kwargs: P.kwargs) -> str:
    # Deliberately skip the filesystem write — a doc fence like
    # ``convert_dbc_file("vehicle.dbc", "vehicle.json")`` would otherwise
    # leak ``vehicle.json`` into the repo root during harness runs.
    return "{}"


def _harness_frames() -> Iterator[CANFrameTuple]:
    """Return a single illustrative 7-tuple frame, for a log no fence's directory holds.

    Empty iterators silently pass any unpack — including a 4-tuple unpack
    against a 7-tuple yield, the exact drift that the old 5-tuple era and
    the later 5 → 7 transition (which added BRS/ESI) surfaced across the
    doc sites. Yielding at least one real
    ``CANFrameTuple`` ensures every fence body that iterates is actually
    exercised, so unpack-arity drift fails fast at fence-execution time.
    The synthetic frame ``(0, 0x100, 8, bytes(8), False, None, None)``
    resolves cleanly against ``vehicle.dbc``'s message id ``0x100`` with
    ``dlc=8``; its signals decode to 0, comfortably below the speed limits
    the docs reference. ``brs`` and ``esi`` are ``None`` (CAN 2.0B; the
    BRS/ESI bits do not exist).
    """
    return iter([CANFrameTuple(0, 0x100, DLCCode(8), bytes(8), extended=False, brs=None, esi=None)])


_harness_iter_can_log = _shipped_or(iter_can_log, _harness_frames)
_harness_load_can_log = _shipped_or(load_can_log, list[CANFrameTuple])


def _text_or_shipped[**P, R](real: Callable[P, R], fake: Callable[[], R]) -> Callable[P, R]:
    """Wrap ``real`` to parse a ``str``, which it reads as text, and load a path as the rest do."""
    shipped = _shipped_or(real, fake)

    def load(*args: P.args, **kwargs: P.kwargs) -> R:
        if args and isinstance(args[0], str):
            return real(*args, **kwargs)
        return shipped(*args, **kwargs)

    return load


_harness_load_checks = _text_or_shipped(load_checks, list[CheckResult])
_harness_load_checks_from_excel = _shipped_or(load_checks_from_excel, list[CheckResult])
_harness_load_dbc_from_excel = _shipped_or(load_dbc_from_excel, _doc_dbc)


def _harness_create_template[**P](*_args: P.args, **_kwargs: P.kwargs) -> None:
    return None


class _DocGlobals(TypedDict):
    """Exact name -> type map of the namespace injected into every doc fence.

    Naming each entry (rather than ``dict[str, object]``) keeps the harness
    self-documenting and lets the type checker verify the construction in
    :func:`_make_globals`.  The empty scratch lists carry the element type
    fences are expected to append.
    """

    # The colliding names (AletheiaClient/Signal/Predicate/Property/...) are
    # both TypedDict field names AND types referenced in the annotations, so
    # they are written ``aletheia.X`` (module-qualified) to resolve to the
    # re-exported type rather than the class-scoped field.
    AletheiaClient: type[aletheia.AletheiaClient]
    Signal: type[aletheia.Signal]
    Predicate: type[aletheia.Predicate]
    Property: type[aletheia.Property]
    # Exact decimals in fences: `between(Fraction("11.5"), ...)` — the float
    # principle (no float crosses the API). Injected like the aletheia names so
    # fences need not repeat `from fractions import Fraction`.
    Fraction: type[Fraction]
    AletheiaError: type[aletheia.AletheiaError]
    ProtocolError: type[aletheia.ProtocolError]
    ValidationError: type[aletheia.ValidationError]
    BatchError: type[aletheia.BatchError]
    FrameResponse: TypeAliasType
    infinitely_often: Callable[[aletheia.Property | aletheia.Predicate], aletheia.Property]
    eventually_always: Callable[[aletheia.Property | aletheia.Predicate], aletheia.Property]
    never: Callable[[aletheia.Property | aletheia.Predicate], aletheia.Property]
    dbc_to_json: Callable[..., DBCDefinition]
    convert_dbc_file: Callable[..., str]
    iter_can_log: Callable[..., Iterator[CANFrameTuple]]
    load_can_log: Callable[..., list[CANFrameTuple]]
    load_checks: Callable[..., list[CheckResult]]
    load_checks_from_excel: Callable[..., list[CheckResult]]
    load_dbc_from_excel: Callable[..., DBCDefinition]
    create_template: Callable[..., None]
    dbc: DBCDefinition
    dbc_json: DBCDefinition
    client: aletheia.AletheiaClient
    frames: list[CANFrameTuple]
    trace: list[CANFrameTuple]
    checks: ModuleType
    check_list: list[CheckResult]
    properties: list[aletheia.Property]
    safety_checks: list[CheckResult]
    session_checks: list[CheckResult]
    can_trace: list[CANFrameTuple]
    frame_bytes: bytes
    property: aletheia.Property
    brake_pressed: aletheia.Predicate
    ts: int
    can_id: int
    dlc: int
    data: bytes


def _make_globals() -> _DocGlobals:
    """Per-test globals injected into every markdown code fence.

    Returns a fresh client + mutable collections per invocation so fences
    don't accidentally share state across files. The client is
    ``parse_dbc``'d but deliberately *not* stream-started: fences that
    document ``add_checks``/``set_properties``/``start_stream`` expect
    the pre-start state, and ``send_frame[s]``/``end_stream`` fences
    chain onto their ``start_stream`` predecessor via ``continuation``.
    """
    client = AletheiaClient()
    client.__enter__()  # pylint: disable=unnecessary-dunder-call
    # Loaded once the client is up: the loader reads every number through the kernel.
    dbc = _doc_dbc()
    client.parse_dbc(dbc)
    return {
        "AletheiaClient": AletheiaClient,
        "Signal": Signal,
        "Predicate": Predicate,
        "Property": Property,
        "Fraction": Fraction,
        "AletheiaError": AletheiaError,
        "ProtocolError": ProtocolError,
        "ValidationError": ValidationError,
        "BatchError": BatchError,
        "FrameResponse": FrameResponse,
        "infinitely_often": infinitely_often,
        "eventually_always": eventually_always,
        "never": never,
        "dbc_to_json": _harness_dbc_to_json,
        "convert_dbc_file": _harness_convert_dbc_file,
        "iter_can_log": _harness_iter_can_log,
        "load_can_log": _harness_load_can_log,
        "load_checks": _harness_load_checks,
        "load_checks_from_excel": _harness_load_checks_from_excel,
        "load_dbc_from_excel": _harness_load_dbc_from_excel,
        "create_template": _harness_create_template,
        "dbc": dbc,
        "dbc_json": dbc,
        "client": client,
        "frames": [],
        "trace": [],
        "checks": aletheia.checks,
        "check_list": [],
        "properties": [],
        "safety_checks": [],
        "session_checks": [],
        "can_trace": [],
        "frame_bytes": bytes(8),
        "property": Signal("VehicleSpeed").less_than(250).always(),
        "brake_pressed": Signal("BrakePressure").greater_than(0),
        "ts": 0,
        "can_id": 0x100,
        "dlc": 8,
        "data": bytes(8),
    }


def pytest_sessionstart() -> None:
    """Replace loader functions project-wide with harness wrappers.

    In-fence ``from aletheia.dbc import dbc_to_json`` binds the
    real function, bypassing the globals hook. Patching both the
    re-exports on ``aletheia`` and the definitions on their submodules
    ensures every import form lands on the fake.
    """
    aletheia.dbc_to_json = _harness_dbc_to_json
    aletheia.dbc.dbc_to_json = _harness_dbc_to_json
    aletheia.convert_dbc_file = _harness_convert_dbc_file
    aletheia.dbc.convert_dbc_file = _harness_convert_dbc_file
    aletheia.iter_can_log = _harness_iter_can_log
    aletheia.can_log.iter_can_log = _harness_iter_can_log
    aletheia.load_can_log = _harness_load_can_log
    aletheia.can_log.load_can_log = _harness_load_can_log
    aletheia.load_checks = _harness_load_checks
    aletheia.yaml_loader.load_checks = _harness_load_checks
    aletheia.load_checks_from_excel = _harness_load_checks_from_excel
    aletheia.excel_loader.load_checks_from_excel = _harness_load_checks_from_excel
    aletheia.load_dbc_from_excel = _harness_load_dbc_from_excel
    aletheia.excel_loader.load_dbc_from_excel = _harness_load_dbc_from_excel
    aletheia.create_template = _harness_create_template
    aletheia.excel_loader.create_template = _harness_create_template


def pytest_markdown_docs_globals() -> _DocGlobals:
    """pytest-markdown-docs hook — globals merged into every fence's namespace."""
    return _make_globals()


def source_docstring_fences(
    self: MarkdownDocstringCodeModule,
) -> Generator[MarkdownInlinePythonItem]:
    """Yield a Python file's docstring fences, read from its source, not from the imported module.

    The plugin's own collector imports the module and walks it with
    ``inspect.getmembers``, which on Python 3.14 evaluates every function's
    deferred annotations and fails on a name imported under ``TYPE_CHECKING``.
    Read from the source, every docstring is reached, nested ones included, and
    nothing runs at collection, ``__main__`` included; each fence is run as the
    plugin runs a Markdown fence, numbered by the file line it opens on.
    """
    syntax = FenceSyntax(str(self.config.getoption("markdowndocs_syntax")))
    for hosted in docstrings(SourceText(self.path.read_text(encoding="utf-8"))):
        tests = extract_fence_tests(
            harness_markdown_it(),
            hosted.text,
            hosted.start - 1,
            source_path=self.path,
            fence_syntax=syntax,
        )
        for i, test in enumerate(tests, start=1):
            yield MarkdownInlinePythonItem.from_parent(
                self,
                name=f"{hosted.owner}[CodeFence#{i}][line:{test.start_line}]",
                test_definition=test,
            )


# The plugin's collector of a Python file collects it this way.
MarkdownDocstringCodeModule.collect = source_docstring_fences


@register_runner()
class ProgramRunner(DefaultRunner):
    """Run a fence as a reader would: a program of its own, in a process of its own.

    A fence opened ``python runner:ProgramRunner`` is a whole program, one that
    runs a real clock or the async client's worker threads, which belong to its
    process and not to the test's. It runs in the fence's sandbox directory
    against the forwarding stand-in kernel the session names, so its refusals
    are read as any fence's, reads no harness global, and fails unless it exits
    zero. Its lines keep their document numbers, the fence's source being padded
    to its opening line.
    """

    @override
    def runtest(
        self,
        test: FenceTestDefinition,
        args: dict[str, object],
        *,
        asyncio_runner: None = None,
    ) -> None:
        del args, asyncio_runner  # the program reads no harness global and runs its own loop
        program = Path("fence.py")
        _ = program.write_text(test.source, encoding="utf-8")
        ran = subprocess.run(
            [sys.executable, str(program)], capture_output=True, text=True, check=False
        )
        if ran.returncode != 0:
            msg = (
                f"{test.source_path}: the program exited {ran.returncode}\n{ran.stdout}{ran.stderr}"
            )
            raise AssertionError(msg)


def pytest_collectstart(collector: pytest.Collector) -> None:
    """Refuse a docstring collector that collects otherwise than ``source_docstring_fences``."""
    if (
        isinstance(collector, MarkdownDocstringCodeModule)
        and type(collector).collect is not source_docstring_fences
    ):
        msg = (
            f"{collector.path}: pytest-markdown-docs built a docstring collector of its own,"
            + " which imports the module; its class no longer takes the collect conftest.py"
            + " gives MarkdownDocstringCodeModule"
        )
        raise pytest.UsageError(msg)


def pytest_markdown_docs_markdown_it() -> MarkdownIt:
    """pytest-markdown-docs hook: the harness collects through a parser that runs no tilde fence."""
    return harness_markdown_it()


@pytest.fixture(autouse=True)
def sandbox_cwd(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run every doc fence in a per-test ``tmp_path`` holding a copy of each shipped data file.

    A loader reads the file a fence names when the directory holds it, so a
    fence naming ``vehicle.dbc`` or ``drive.log`` runs against the shipped
    file, and every other path reaches the loader's fake. Defense-in-depth:
    even though ``pytest_sessionstart`` patches ``create_template`` (and the
    other loader entry points), the patches only fire when this conftest is
    loaded.  Running pytest with a non-repo rootdir bypasses the conftest,
    lets the real ``create_template`` execute, and lands
    ``vehicle_checks.xlsx`` in the invoking shell's cwd.  Pinning cwd to
    ``tmp_path`` per test means any file write, patched or not, goes to a
    sandboxed dir that pytest auto-cleans, and a fence writing over a copy
    leaves the shipped file as it was.
    """
    for name, path in _SHIPPED.items():
        _ = shutil.copyfile(path, tmp_path / name)
    monkeypatch.chdir(tmp_path)


@pytest.fixture(scope="session", autouse=True)
def refusal_log(tmp_path_factory: pytest.TempPathFactory) -> Generator[Path]:
    """Load the forwarding stand-in kernel in place of the library, logging refusals to one file.

    The variables are set before any fence loads the library, so every
    client a fence opens, the injected one or its own, reaches the kernel
    through the stand-in.
    """
    log = tmp_path_factory.mktemp("refusals") / "refusals.log"
    log.touch()
    with pytest.MonkeyPatch.context() as env:
        env.setenv("ALETHEIA_FORWARD_TO", str(find_ffi_library()))
        env.setenv("ALETHEIA_REFUSAL_LOG", str(log))
        env.setenv("ALETHEIA_LIB", str(stand_in_kernel(StandInName("forwarding_kernel"))))
        yield log


def _stated_refusals(item: MarkdownInlinePythonItem) -> list[ErrorCode]:
    """Return the codes the ``refuses`` line directly above the fence names, in order."""
    lines = item.path.read_text(encoding="utf-8").splitlines()
    # start_line is the 1-based line opening the fence, so the line above it is list index - 2.
    above = lines[item.start_line - 2] if item.start_line > 1 else ""
    # A docstring's lines carry its indentation, which getdoc removes.
    stated = _REFUSES.fullmatch(above.strip() if item.path.suffix == ".py" else above)
    return [ErrorCode(code) for code in stated.group(1).split()] if stated else []


@pytest.hookimpl(wrapper=True)
def pytest_runtest_call(item: pytest.Item) -> Generator[None]:
    """Fail a fence whose refusals are not exactly the codes its ``refuses`` line names."""
    if not isinstance(item, MarkdownInlinePythonItem):
        return (yield)
    # The item resolves its fixtures as it runs, so the log is asked for first.
    log = Path(item.fixture_request.getfixturevalue("refusal_log"))
    before = log.stat().st_size
    result = yield
    with log.open(encoding="utf-8") as read:
        _ = read.seek(before)
        envelopes = [line.split("\t", 1)[1] for line in read.read().splitlines()]
    refused = [ErrorCode(json.loads(envelope)["code"]) for envelope in envelopes]
    stated = _stated_refusals(item)
    assert refused == stated, (
        f"the kernel refused [{' '.join(refused)}], the fence states [{' '.join(stated)}]: an"
        + " example that shows a refusal names its codes on a `<!-- refuses: <code> ... -->`"
        + " line directly above its fence\n"
        + "\n".join(envelopes)
    )
    return result
