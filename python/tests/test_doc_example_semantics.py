# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Each temporal example the documentation gives checks what its comment says.

The doc-example harness holds every example to running; these tests hold the
temporal ones to their meaning. Each example is read where a reader reads it, a
docstring of the DSL or a section of ``docs/reference/PYTHON_API.md``, its
statements run up to the first ``with`` block, and the property it builds (the
name ``property`` it binds, or else its last expression) is streamed through the
kernel on a trace where the comment says it holds and on one where it says it
fails; where the property is an ``always``, the failing trace fails it past its
first frame. A frame carries every signal the examples name, a value not given
being 0.
"""

from __future__ import annotations

import ast
import runpy
from pathlib import Path
from typing import NamedTuple, NewType

import pytest
from _dbc_helpers import dbc, message, signal
from pytest_markdown_docs.plugin import extract_fence_tests

from tools._hosted_markdown import SourceText, docstrings
from tools.check_fence_marks import harness_markdown_it

from aletheia import AletheiaClient
from aletheia.dsl import Property, Signal
from aletheia.types import DLCCode

_REPO = Path(__file__).resolve().parents[2]

# What holds an example: a docstring's dotted owner, or a document heading's text.
Holder = NewType("Holder", str)
# A signal's name as the examples spell it, and a raw value a frame gives it.
SignalName = NewType("SignalName", str)
RawValue = NewType("RawValue", int)
# The milliseconds a frame of a trace is sent at, and a fence's place among its docstring's.
Millis = NewType("Millis", int)
FenceIndex = NewType("FenceIndex", int)
# The source of one example fence, and a trace written as text: frames split by
# ``|``, each its milliseconds then ``Name=value`` words.
FenceSource = NewType("FenceSource", str)
TraceText = NewType("TraceText", str)
# The verdict a stream ends with: fails, holds, or the statuses it leaves.
Verdict = NewType("Verdict", str)


class Frame(NamedTuple):
    """One frame of a trace: when it is sent and the values it gives."""

    millis: Millis
    values: dict[SignalName, RawValue]


_SIGNALS = tuple(
    SignalName(name)
    for name in (
        "Speed",
        "VehicleSpeed",
        "BrakePressure",
        "BrakePedal",
        "StartButton",
        "PowerMode",
        "Ignition",
        "Brake",
        "BrakeLight",
        "Gear",
        "EngineRunning",
        "Acceleration",
        "BrakeActive",
    )
)
# Thirteen 16-bit signals fill 26 bytes, so one CAN-FD frame of 32 bytes carries them all.
_DLC = DLCCode(13)
_DBC = dbc(
    [
        message(
            256,
            "Bus",
            [signal(name, start_bit=16 * i, length=16) for i, name in enumerate(_SIGNALS)],
            dlc=32,
        )
    ]
)


def _trace(text: TraceText) -> list[Frame]:
    """Return the frames ``text`` writes, in order."""
    frames: list[Frame] = []
    for part in text.split("|"):
        millis, *words = part.split()
        given = {SignalName(w.split("=")[0]): RawValue(int(w.split("=")[1])) for w in words}
        frames.append(Frame(Millis(int(millis)), given))
    return frames


def _fence_of_docstring(path: Path, owner: Holder, index: FenceIndex) -> FenceSource:
    """Return the source of the docstring fence ``index`` of ``owner`` in ``path``."""
    for hosted in docstrings(SourceText(path.read_text(encoding="utf-8"))):
        if hosted.owner == owner:
            tests = list(
                extract_fence_tests(
                    harness_markdown_it(), hosted.text, hosted.start - 1, source_path=path
                )
            )
            return FenceSource(tests[index].source)
    msg = f"{path}: no docstring owned by {owner}"
    raise AssertionError(msg)


def _fence_under_heading(path: Path, heading: Holder) -> FenceSource:
    """Return the first Python fence after the heading ``heading`` of ``path``."""
    tokens = harness_markdown_it().parse(path.read_text(encoding="utf-8"))
    for i, token in enumerate(tokens):
        if (
            token.type == "inline"
            and token.content == heading
            and tokens[i - 1].type == "heading_open"
        ):
            for later in tokens[i:]:
                if later.type == "fence" and later.info.split()[:1] == ["python"]:
                    return FenceSource(later.content)
    msg = f"{path}: no Python fence under the heading {heading!r}"
    raise AssertionError(msg)


def _program(source: FenceSource) -> list[ast.stmt]:
    """Return the example's statements before its first ``with``, the last binding ``property``."""
    body: list[ast.stmt] = []
    for stmt in ast.parse(source).body:
        if isinstance(stmt, ast.With):
            break
        body.append(stmt)
    if body and isinstance(last := body[-1], ast.Expr):
        body[-1] = _binding(last.value)
    return body


def _binding(value: ast.expr) -> ast.Assign:
    """Return the statement binding ``property`` to ``value``."""
    return ast.Assign(targets=[ast.Name("property", ast.Store())], value=value)


def _outer_always(body: list[ast.stmt]) -> ast.expr | None:
    """Return what the property calls ``always`` on, or None when it ends in another operator."""
    match body[-1:]:
        case [ast.Assign(value=ast.Call(func=ast.Attribute(value=inner, attr="always"), args=[]))]:
            return inner
        case _:
            return None


def _run(body: list[ast.stmt], scratch: Path) -> Property:
    """Run the statements and return the property they bind."""
    program = scratch / "example.py"
    _ = program.write_text(ast.unparse(ast.fix_missing_locations(ast.Module(body, []))))
    built = runpy.run_path(str(program), init_globals={"Signal": Signal})["property"]
    assert isinstance(built, Property), f"the example builds {type(built).__name__}, not a Property"
    return built


def _property_of(source: FenceSource, scratch: Path) -> Property:
    """Run the example's statements before its first ``with`` and return the property it builds."""
    return _run(_program(source), scratch)


def _verdict(prop: Property, trace: list[Frame]) -> Verdict:
    """Stream ``trace`` against ``prop``: fails, holds, or every status the stream reported."""
    with AletheiaClient() as client:
        _ = client.parse_dbc(_DBC)
        _ = client.set_properties([prop.to_dict()])
        _ = client.start_stream()
        decided: set[Verdict] = set()
        for millis, values in trace:
            frame = client.build_frame(
                can_id=256, dlc=_DLC, signals={name: values.get(name, 0) for name in _SIGNALS}
            )
            response = client.send_frame(millis * 1000, 256, _DLC, frame)
            if "type" in response:  # narrows the union to PropertyBatchResponse
                decided |= {Verdict(r["status"]) for r in response["results"]}
        ended = client.end_stream()
        assert ended["status"] == "complete", ended
        decided |= {Verdict(r["status"]) for r in ended["results"]}
    return Verdict("fails") if "fails" in decided else Verdict("/".join(sorted(decided)))


class Example(NamedTuple):
    """One documented example: where it is, and a trace it holds on and one it fails on."""

    path: Path
    holder: Holder
    fence: FenceIndex | None  # the docstring fence; None for a document heading
    holds: TraceText
    fails: TraceText


_DSL = _REPO / "python" / "aletheia" / "dsl.py"
_PROPERTY = _REPO / "python" / "aletheia" / "_dsl_property.py"
_PACKAGE = _REPO / "python" / "aletheia" / "__init__.py"
_API = _REPO / "docs" / "reference" / "PYTHON_API.md"


# A brake press answered within 100 ms by a fall of 15, and one never answered.
_BRAKE_ANSWERED = TraceText(
    "0 VehicleSpeed=100 | 10 BrakePressure=5 VehicleSpeed=100 | 50 BrakePressure=5 VehicleSpeed=85"
)
_BRAKE_UNANSWERED = TraceText(
    "0 VehicleSpeed=100 | 10 BrakePressure=5 VehicleSpeed=100 | 200 VehicleSpeed=100"
)
_RELEASED = TraceText("0 Brake=1 | 10 Ignition=1 Brake=1 | 20 Ignition=1")
_DROPPED = TraceText("0 Brake=1 | 10 Ignition=0")
_START_HELD = TraceText("0 | 10 PowerMode=2")
_START_PRESSED = TraceText("0 | 10 StartButton=1 | 20 PowerMode=2")
_SPEED_HELD = TraceText("0 Speed=60 | 500 Speed=60 Brake=1")
_SPEED_DROPPED = TraceText("0 Speed=60 | 500 Speed=40 | 800 Speed=60 Brake=1")
_RELEASED_IN_WINDOW = TraceText("0 Brake=1 | 3000 Ignition=1 Brake=1 | 4000 Ignition=1")
_DROPPED_IN_WINDOW = TraceText("0 Brake=1 | 2000 Ignition=0")

EXAMPLES = {
    "the module's brake response": Example(
        _DSL, Holder("<module>"), FenceIndex(0), _BRAKE_ANSWERED, _BRAKE_UNANSWERED
    ),
    "Predicate.within": Example(
        _DSL, Holder("Predicate.within"), FenceIndex(0), _BRAKE_ANSWERED, _BRAKE_UNANSWERED
    ),
    "Predicate.implies": Example(
        _DSL, Holder("Predicate.implies"), FenceIndex(0), _BRAKE_ANSWERED, _BRAKE_UNANSWERED
    ),
    "Predicate.until": Example(
        _DSL, Holder("Predicate.until"), FenceIndex(0), _START_HELD, _START_PRESSED
    ),
    "Predicate.release": Example(
        _DSL, Holder("Predicate.release"), FenceIndex(0), _RELEASED, _DROPPED
    ),
    "Predicate.metric_until": Example(
        _DSL, Holder("Predicate.metric_until"), FenceIndex(0), _SPEED_HELD, _SPEED_DROPPED
    ),
    "Predicate.metric_release": Example(
        _DSL,
        Holder("Predicate.metric_release"),
        FenceIndex(0),
        _RELEASED_IN_WINDOW,
        _DROPPED_IN_WINDOW,
    ),
    "Predicate.next's alternative": Example(
        _DSL,
        Holder("Predicate.next"),
        FenceIndex(1),
        TraceText("0 Gear=1 | 50 Gear=2"),
        TraceText("0 Gear=1 | 50 Gear=3 | 80 Gear=2"),
    ),
    "Property.implies": Example(
        _PROPERTY,
        Holder("Property.implies"),
        FenceIndex(0),
        TraceText(
            "0 Ignition=1 | 400 Ignition=1 EngineRunning=1 | 800 Ignition=1 EngineRunning=1"
            + " | 1200 Ignition=1 EngineRunning=1 | 1600 Ignition=1 EngineRunning=1"
        ),
        TraceText("0 | 400 Ignition=1 | 800 Ignition=1 | 1200 Ignition=1 | 1600 Ignition=1"),
    ),
    "Property.until": Example(
        _PROPERTY,
        Holder("Property.until"),
        FenceIndex(0),
        TraceText("0 Ignition=1 Brake=1 BrakeLight=1 | 10 Ignition=1 | 20"),
        TraceText("0 Ignition=1 Brake=1 | 10"),
    ),
    "Property.release": Example(
        _PROPERTY,
        Holder("Property.release"),
        FenceIndex(0),
        TraceText(
            "0 Brake=1 | 500 Ignition=1 Brake=1 | 1000 Ignition=1 | 1500 Ignition=1"
            + " | 1600 Ignition=1"
        ),
        TraceText("0 Brake=1 | 500"),
    ),
    "Property.metric_until": Example(
        _PROPERTY,
        Holder("Property.metric_until"),
        FenceIndex(0),
        TraceText("0 Speed=60 | 100 Speed=60 | 200 Speed=60 Brake=1"),
        TraceText("0 Speed=60 | 100 Speed=40 | 200 Speed=60 Brake=1"),
    ),
    "Property.metric_release": Example(
        _PROPERTY,
        Holder("Property.metric_release"),
        FenceIndex(0),
        TraceText("0 Brake=1 | 2000 Brake=1 | 6000"),
        TraceText("0 Brake=1 | 2000"),
    ),
    "the package's composition": Example(
        _PACKAGE,
        Holder("<module>"),
        FenceIndex(1),
        TraceText("0 Speed=100 | 10 Brake=1 Speed=100 | 50 Brake=1 Speed=85"),
        TraceText("0 Speed=100 | 10 Brake=1 Speed=100 | 200 Speed=100"),
    ),
    "the guide's Implication": Example(
        _API,
        Holder("Implication"),
        None,
        TraceText(
            "0 Speed=100 | 10 BrakePedal=5 Speed=100 | 50 BrakePedal=5 Speed=90 | 90 Speed=90"
        ),
        TraceText("0 Speed=100 | 10 BrakePedal=5 Speed=100 | 200 Speed=100"),
    ),
    "the guide's Until": Example(
        _API,
        Holder("Until"),
        None,
        TraceText("0 | 10 PowerMode=2 | 20 PowerMode=2 StartButton=1"),
        TraceText("0 PowerMode=2 | 10 | 20 StartButton=1 | 30 PowerMode=2"),
    ),
    "the guide's Release Operator": Example(
        _API, Holder("Release Operator"), None, _RELEASED, _DROPPED
    ),
    "the guide's Metric Until": Example(
        _API, Holder("Metric Until"), None, _SPEED_HELD, _SPEED_DROPPED
    ),
    "the guide's Metric Release": Example(
        _API, Holder("Metric Release"), None, _RELEASED_IN_WINDOW, _DROPPED_IN_WINDOW
    ),
    "the guide's power mode state machine": Example(
        _API,
        Holder("Example 4: Power Mode State Machine"),
        None,
        TraceText("0 BrakeActive=1 | 10 BrakeActive=0 | 20 VehicleSpeed=5 Acceleration=2"),
        TraceText("0 VehicleSpeed=5 | 10 BrakeActive=1 | 20 BrakeActive=1 Acceleration=2 | 30"),
    ),
}


def _source(example: Example) -> FenceSource:
    """Return the source of the example's fence."""
    if example.fence is None:
        return _fence_under_heading(example.path, example.holder)
    return _fence_of_docstring(example.path, example.holder, example.fence)


# The examples whose property is an ``always`` of another.
_ALWAYS = {
    key: example
    for key, example in EXAMPLES.items()
    if _outer_always(_program(_source(example))) is not None
}


@pytest.mark.parametrize("example", EXAMPLES.values(), ids=EXAMPLES.keys())
def test_the_example_holds_and_fails_where_its_comment_says(
    example: Example, tmp_path: Path
) -> None:
    """The property the example builds holds on its trace and fails on the other."""
    prop = _property_of(_source(example), tmp_path)
    assert _verdict(prop, _trace(example.holds)) == "holds"
    assert _verdict(prop, _trace(example.fails)) == "fails"


@pytest.mark.parametrize("example", _ALWAYS.values(), ids=_ALWAYS.keys())
def test_the_failing_trace_fails_past_its_first_frame(example: Example, tmp_path: Path) -> None:
    """Its outer ``always`` removed, the property does not fail the trace it fails on.

    The property is then read at the first frame alone, so a trace failing it there cannot tell
    the example's ``always`` from its absence.
    """
    body = _program(_source(example))
    inner = _outer_always(body)
    assert inner is not None
    body[-1] = _binding(inner)
    assert _verdict(_run(body, tmp_path), _trace(example.fails)) != "fails"
