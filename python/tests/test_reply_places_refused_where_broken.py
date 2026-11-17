# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every reply reader accepts a broken place of a real reply or refuses it in the one form."""

from __future__ import annotations

import json
import re
from contextlib import contextmanager
from fractions import Fraction
from typing import TYPE_CHECKING, Final, Literal, NamedTuple, NewType

import pytest
from _dbc_helpers import KernelReply, dbc
from _repo_root import REPO_ROOT

from aletheia import AletheiaClient, AletheiaError, FFIBackend, MockBackend, ProtocolError, Signal
from aletheia.client._response_parsers import (
    build_error_response,
    parse_complete_warnings,
    parse_finalization_results,
    parse_frame_response,
    parse_parsed_dbc_response,
)
from aletheia.common_types import Prose
from aletheia.types import DLCCode, dump_json, is_str_dict

if TYPE_CHECKING:
    from collections.abc import Generator, Iterator

    from aletheia.types import JSONValue, PropertyResultEntry, SetPropertiesCommand

pytestmark = pytest.mark.usefixtures("rts_up")

# A reader of a kernel reply, named by the command whose reply it reads.
type ReaderName = Literal[
    "parseDBC",
    "formatDBC",
    "formatDBCText",
    "validateDBC",
    "frame",
    "endStream",
    "extractAllSignals",
    "error envelope",
]

# How a place is broken: its key deleted, its value or an array's entry replaced by another kind.
type Breakage = Literal["deleted", "retyped", "entry retyped"]

# The scenario a real reply comes from.
FixtureName = NewType("FixtureName", str)

# A place in a reply: its keys from the root joined by ``/``, an array adding none.
ReplyPath = NewType("ReplyPath", str)

# What came at a broken place: ``nothing``, ``string`` or ``number``.
Arrival = NewType("Arrival", str)

# A key of a reply object.
ReplyKey = NewType("ReplyKey", str)

# The position of an entry in a reply array, counted from 0.
EntryIndex = NewType("EntryIndex", int)

# A DBC file's text.
DBCText = NewType("DBCText", str)

# A row's table in the reply proof.
AgdaTable = NewType("AgdaTable", str)

# One line of the reply proof's source.
AgdaLine = NewType("AgdaLine", str)

# The opaque session handle the kernel answers ``init`` with.
SessionHandle = NewType("SessionHandle", int)

type Step = ReplyKey | EntryIndex

# The steps from a reply's root down to one value.
type Where = tuple[Step, ...]


class Case(NamedTuple):
    """A reader and the real reply it is fed broken copies of."""

    reader: ReaderName
    fixture: FixtureName


class Break(NamedTuple):
    """One broken copy: the place, the value's steps, how it is broken and what replaces it."""

    path: ReplyPath
    where: Where
    breakage: Breakage
    replacement: JSONValue


class Failure(NamedTuple):
    """A broken place a reader neither accepted nor refused in the one form."""

    path: ReplyPath
    breakage: Breakage
    verdict: Prose


_REPO: Final = REPO_ROOT
_CORPUS: Final = _REPO / "python" / "tests" / "fixtures" / "dbc_corpus"
_REPLY_PROOF: Final = _REPO / "src" / "Aletheia" / "Protocol" / "ReplyRange.agda"
_ROOT: Final = ReplyPath("")

_CORPUS_NAMES: Final = tuple(
    FixtureName(name)
    for name in (
        "kitchen_sink",
        "attributes",
        "comments_groups",
        "env_vars",
        "value_tables",
        "multiplexing",
        "extended_can",
    )
)
_UNKNOWN_TARGET = FixtureName("value_tables with an unknown VAL_ target")
_TWIN = FixtureName("kitchen_sink with a twin message")
_LOADS: Final = (*_CORPUS_NAMES, _UNKNOWN_TARGET)
_ENVELOPES: Final = {
    FixtureName("trailing input"): "text_trailing_input",
    FixtureName("invalid character"): "dbc_invalid_character",
    FixtureName("identifier past its bound"): "input_bound_exceeded",
    FixtureName("validation failed"): "handler_validation_failed",
}
_KITCHEN_SINK = FixtureName("kitchen_sink")
_PROPERTIES = FixtureName("kitchen_sink with five properties")
_MIXED = FixtureName("a value, an over-range error and an absent signal")

CASES: Final = (
    *(Case("parseDBC", name) for name in _LOADS),
    *(Case("formatDBC", name) for name in _LOADS),
    Case("formatDBCText", _KITCHEN_SINK),
    Case("formatDBCText", _TWIN),
    Case("validateDBC", _KITCHEN_SINK),
    Case("validateDBC", _TWIN),
    Case("frame", _PROPERTIES),
    Case("endStream", _PROPERTIES),
    Case("extractAllSignals", _MIXED),
    *(Case("error envelope", name) for name in _ENVELOPES),
)

# Message 256 holds a selector, a halved value, a signal its selector leaves out
# and one whose value's numerator passes the wire's 128-bit bound.
_MIXED_TEXT: Final = DBCText(
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 Mixed: 8 ECU\n'
    + ' SG_ Mode M : 0|4@1+ (1,0) [0|15] "" Vector__XXX\n'
    + ' SG_ Half m0 : 8|8@1+ (0.5,0) [0|127.5] "" Vector__XXX\n'
    + ' SG_ Other m1 : 8|8@1+ (1,0) [0|255] "" Vector__XXX\n'
    + " SG_ Big : 16|17@1+ (0.12345678901234567890123456789012345678,0)"
    + ' [0|10000] "" Vector__XXX\n'
)

# Mode 0, Half 3/2, Big all ones over its low 16 bits.
_MIXED_FRAME: Final = bytes([0x00, 0x03, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00])

# Speed 250 rpm and Temp 60 degC, then Speed 0: Temp holds, Speed under 100 fails.
_FIRST_FRAME: Final = bytes([0xE8, 0x03, 100, 0, 0, 0, 0, 0])
_SECOND_FRAME: Final = bytes([0x00, 0x00, 100, 0, 0, 0, 0, 0])

# The crashes a reader can raise on a reply it does not narrow; any other propagates.
_CRASHES: Final = (
    LookupError,
    TypeError,
    AttributeError,
    ArithmeticError,
    ValueError,
    AssertionError,
    RuntimeError,
    AletheiaError,
)

_CLAUSE: Final = re.compile(
    r"^(?P<table>replyRange|replyText|replyNonEmpty) \((?P<keys>(?:\"[^\"]*\" ∷ )+)\[\]\)"
)
_CLAUSE_START: Final = re.compile(r"^(?:replyRange|replyText|replyNonEmpty) \(")


def _corpus_text(name: FixtureName) -> DBCText:
    """Read a corpus DBC's text."""
    return DBCText((_CORPUS / f"{name}.dbc").read_text(encoding="utf-8"))


@contextmanager
def _session() -> Generator[tuple[FFIBackend, SessionHandle]]:
    """Open one kernel session on the real library, closed on exit."""
    backend = FFIBackend()
    state = SessionHandle(backend.init())
    try:
        yield backend, state
    finally:
        backend.close(state)


def _value(reply: KernelReply) -> JSONValue:
    """Decode a reply, which the kernel writes as one JSON object."""
    decoded = json.loads(reply)
    assert is_str_dict(decoded), decoded
    return decoded


def _command(backend: FFIBackend, state: SessionHandle, command: JSONValue) -> JSONValue:
    """Send a JSON command and decode the kernel's reply."""
    return _value(KernelReply(backend.process(state, dump_json(command).encode())))


def _load(backend: FFIBackend, state: SessionHandle, text: DBCText) -> JSONValue:
    """Load a DBC text and return the kernel's parseDBCText reply."""
    return _command(backend, state, {"type": "command", "command": "parseDBCText", "text": text})


def _field(reply: JSONValue, key: ReplyKey) -> JSONValue:
    """Read one key of a reply object."""
    assert isinstance(reply, dict), reply
    return reply[key]


def _with_twin(dbc_json: JSONValue) -> JSONValue:
    """Append a copy of the DBC's first message under another name, sharing its id."""
    assert isinstance(dbc_json, dict), dbc_json
    messages = dbc_json["messages"]
    assert isinstance(messages, list), messages
    first = messages[0]
    assert isinstance(first, dict), first
    return {**dbc_json, "messages": [*messages, {**first, "name": "Twin"}]}


def _load_replies() -> dict[Case, JSONValue]:
    """Load every corpus DBC and the variant with an unknown VAL_ target, then format it back."""
    replies: dict[Case, JSONValue] = {}
    texts = {name: _corpus_text(name) for name in _CORPUS_NAMES}
    texts[_UNKNOWN_TARGET] = DBCText(
        _corpus_text(FixtureName("value_tables")) + '\nVAL_ 999 Ghost 0 "Zero" ;\n'
    )
    for name, text in texts.items():
        with _session() as (backend, state):
            replies[Case("parseDBC", name)] = _load(backend, state, text)
            replies[Case("formatDBC", name)] = _value(KernelReply(backend.format_dbc_binary(state)))
    return replies


def _dbc_command_replies(loaded: JSONValue) -> dict[Case, JSONValue]:
    """Format and validate kitchen_sink's DBC and its twin-message variant."""
    replies: dict[Case, JSONValue] = {}
    kitchen_sink = _field(loaded, ReplyKey("dbc"))
    for name, body in ((_KITCHEN_SINK, kitchen_sink), (_TWIN, _with_twin(kitchen_sink))):
        with _session() as (backend, state):
            replies[Case("formatDBCText", name)] = _command(
                backend, state, {"type": "command", "command": "formatDBCText", "dbc": body}
            )
            replies[Case("validateDBC", name)] = _command(
                backend, state, {"type": "command", "command": "validateDBC", "dbc": body}
            )
    return replies


def _stream_replies() -> dict[Case, JSONValue]:
    """Stream kitchen_sink under five properties: a batch on the first frame, then the end."""
    with _session() as (backend, state):
        loaded = _load(backend, state, _corpus_text(_KITCHEN_SINK))
        assert _field(loaded, ReplyKey("status")) == "success", loaded
        command: SetPropertiesCommand = {
            "type": "command",
            "command": "setProperties",
            "properties": [
                Signal("Temp").greater_than(0).eventually().to_dict(),
                Signal("Speed").less_than(100).always().to_dict(),
                Signal("Pressure").greater_than(10).eventually().to_dict(),
                Signal("Pressure").less_than(100).always().to_dict(),
                Signal("Speed").greater_than(Fraction(5000)).eventually().to_dict(),
            ],
        }
        accepted = _value(KernelReply(backend.process(state, dump_json(command).encode())))
        assert _field(accepted, ReplyKey("status")) == "success", accepted
        _ = backend.start_stream_binary(state)
        frames = [
            _value(
                KernelReply(
                    backend.send_frame_binary(
                        state,
                        timestamp=timestamp,
                        can_id=256,
                        extended=False,
                        dlc=DLCCode(8),
                        data=data,
                        brs=None,
                        esi=None,
                    )
                )
            )
            for timestamp, data in ((1000, _FIRST_FRAME), (2000, _SECOND_FRAME))
        ]
        end = _value(KernelReply(backend.end_stream_binary(state)))
    assert _field(frames[0], ReplyKey("type")) == "property_batch", frames
    return {Case("frame", _PROPERTIES): frames[0], Case("endStream", _PROPERTIES): end}


def _extraction_reply() -> JSONValue:
    """Extract message 256 of the mixed DBC through the JSON-answering entry."""
    with _session() as (backend, state):
        loaded = _load(backend, state, _MIXED_TEXT)
        assert _field(loaded, ReplyKey("status")) == "success", loaded
        return _value(
            KernelReply(
                backend.extract_signals_binary(
                    state, can_id=256, extended=False, dlc=DLCCode(8), data=_MIXED_FRAME
                )
            )
        )


def _envelope_replies() -> dict[Case, JSONValue]:
    """Refuse four kitchen_sink variants, each with the code its fixture names."""
    base = _corpus_text(_KITCHEN_SINK)
    texts = dict(
        zip(
            _ENVELOPES,
            (
                base + "\nBO_ 1 X: 8\n",
                base + '\nCM_ "a""b";\n',
                re.sub("BU_: ", "BU_: " + "N" * 129 + " ", base, count=1),
                base + '\nBO_ 256 Twin: 8 Engine\n SG_ D : 0|8@1+ (1,0) [0|255] "" Gateway\n',
            ),
            strict=True,
        )
    )
    replies: dict[Case, JSONValue] = {}
    for name, text in texts.items():
        with _session() as (backend, state):
            reply = _load(backend, state, DBCText(text))
        assert _field(reply, ReplyKey("code")) == _ENVELOPES[name], reply
        replies[Case("error envelope", name)] = reply
    return replies


@pytest.fixture(scope="module", name="kernel_replies")
def _kernel_replies() -> dict[Case, JSONValue]:
    """Answer every case's command on the real kernel."""
    out = _load_replies()
    out |= _dbc_command_replies(out[Case("parseDBC", _KITCHEN_SINK)])
    out |= _stream_replies()
    out[Case("extractAllSignals", _MIXED)] = _extraction_reply()
    out |= _envelope_replies()
    assert set(out) == set(CASES)
    return out


def _below(path: ReplyPath, key: ReplyKey) -> ReplyPath:
    """Name the place of ``key`` in the object at ``path``."""
    return ReplyPath(f"{path}/{key}" if path else key)


def _is_rational(value: JSONValue) -> bool:
    """Tell the kernel's ``{numerator, denominator}`` object, a leaf of the reply proof."""
    return isinstance(value, dict) and value.keys() == {"numerator", "denominator"}


def _stand_ins(value: JSONValue) -> tuple[JSONValue, ...]:
    """Name a value's replacements: ``"x"`` for a number, 0 for the rest, both for a rational."""
    if _is_rational(value):
        return (0, "x")
    if isinstance(value, int | float) and not isinstance(value, bool):
        return ("x",)
    return (0,)


def _breaks(value: JSONValue, path: ReplyPath, where: Where) -> Iterator[Break]:
    """Break every place below ``value``: each key deleted and retyped, each entry retyped."""
    if isinstance(value, dict) and not _is_rational(value):
        for raw_key, held in value.items():
            key = ReplyKey(raw_key)
            here, steps = _below(path, key), (*where, key)
            yield Break(here, steps, "deleted", None)
            yield from (Break(here, steps, "retyped", new) for new in _stand_ins(held))
            yield from _breaks(held, here, steps)
    elif isinstance(value, list):
        for index, entry in enumerate(value):
            steps = (*where, EntryIndex(index))
            yield from (Break(path, steps, "entry retyped", new) for new in _stand_ins(entry))
            yield from _breaks(entry, path, steps)


def _broken(value: JSONValue, where: Where, change: Break) -> JSONValue:
    """Copy ``value`` with the place at ``where`` broken as ``change`` says, sharing the rest."""
    step, rest = where[0], where[1:]
    if isinstance(value, dict) and isinstance(step, str):
        out = dict(value)
        if rest:
            out[step] = _broken(value[step], rest, change)
        elif change.breakage == "deleted":
            del out[step]
        else:
            out[step] = change.replacement
        return out
    assert isinstance(value, list), (value, step)
    assert isinstance(step, int), step
    entries = list(value)
    entries[step] = _broken(value[step], rest, change) if rest else change.replacement
    return entries


def _arrival(change: Break) -> Arrival:
    """Name what came at the broken place: ``nothing`` for a deleted key, else its kind."""
    if change.breakage == "deleted":
        return Arrival("nothing")
    return Arrival("string" if isinstance(change.replacement, str) else "number")


def _spelled(where: Where) -> Prose:
    """Spell a value's steps as ``dbc.messages[0].signals[1].factor``."""
    text = "".join(f"[{step}]" if isinstance(step, int) else f".{step}" for step in where)
    return Prose(text.removeprefix("."))


def _no_enrichment(entry: PropertyResultEntry) -> None:
    """Leave a finalization entry as the parser read it."""
    del entry


def _read(reader: ReaderName, reply: KernelReply) -> None:
    """Feed ``reply`` to ``reader``, through the client where the reader lives in it."""
    match reader:
        case "parseDBC":
            decoded = _value(reply)
            assert is_str_dict(decoded), decoded
            _ = parse_parsed_dbc_response(decoded)
        case "frame":
            decoded = _value(reply)
            assert is_str_dict(decoded), decoded
            _ = parse_frame_response(decoded)
        case "endStream":
            decoded = _value(reply)
            assert is_str_dict(decoded), decoded
            _ = parse_finalization_results(decoded, _no_enrichment)
            _ = parse_complete_warnings(decoded)
        case "error envelope":
            decoded = _value(reply)
            assert is_str_dict(decoded), decoded
            _ = build_error_response(decoded)
        case "formatDBC" | "formatDBCText" | "validateDBC" | "extractAllSignals":
            with AletheiaClient(backend=MockBackend([reply])) as client:
                match reader:
                    case "formatDBC":
                        _ = client.format_dbc()
                    case "formatDBCText":
                        _ = client.format_dbc_text(dbc([]))
                    case "validateDBC":
                        _ = client.validate_dbc(dbc([]))
                    case "extractAllSignals":
                        _ = client.extract_signals(0x100, DLCCode(0), b"")


def _verdict(reader: ReaderName, change: Break, reply: KernelReply) -> Prose | None:
    """Say how ``reader`` took a broken copy: ``None`` for an acceptance or the one form."""
    try:
        _read(reader, reply)
    except ProtocolError as exc:
        text = str(exc)
        head, tail = f"reply {change.path}: expected ", f", got {_arrival(change)}"
        if text.startswith(head) and text.endswith(tail):
            return None
        return Prose(f"refused as {text!r}")
    except _CRASHES as exc:
        return Prose(f"crashed with {type(exc).__name__}: {exc}")
    return None


def _proof_paths() -> dict[AgdaTable, frozenset[ReplyPath]]:
    """Read the paths of the reply proof's ``replyRange``, ``replyText`` and ``replyNonEmpty``."""
    rows: dict[AgdaTable, set[ReplyPath]] = {}
    for raw in _REPLY_PROOF.read_text(encoding="utf-8").splitlines():
        line = AgdaLine(raw)
        if not _CLAUSE_START.match(line):
            continue
        clause = _CLAUSE.match(line)
        assert clause is not None, f"a clause the test cannot read: {line}"
        keys = re.findall(r"\"([^\"]*)\"", clause["keys"])
        rows.setdefault(AgdaTable(clause["table"]), set()).add(ReplyPath("/".join(keys)))
    return {table: frozenset(paths) for table, paths in rows.items()}


@pytest.mark.parametrize("case", CASES, ids=[f"{case.reader}-{case.fixture}" for case in CASES])
def test_a_broken_reply_place_is_accepted_or_refused_in_the_one_form(
    case: Case, kernel_replies: dict[Case, JSONValue]
) -> None:
    """A reader accepts each broken place or refuses it as ``reply <path>: expected …, got …``."""
    reply = kernel_replies[case]
    failures: dict[Failure, list[Where]] = {}
    for change in _breaks(reply, _ROOT, ()):
        broken = KernelReply(json.dumps(_broken(reply, change.where, change)).encode())
        verdict = _verdict(case.reader, change, broken)
        if verdict is not None:
            failures.setdefault(Failure(change.path, change.breakage, verdict), []).append(
                change.where
            )
    lines = [
        f"{failure.path} {failure.breakage} (at {_spelled(wheres[0])}, x{len(wheres)}): "
        + failure.verdict
        for failure, wheres in failures.items()
    ]
    if lines:
        copies = sum(len(wheres) for wheres in failures.values())
        pytest.fail(
            f"{case.reader} on {case.fixture}: {copies} broken copies out of the one form,"
            + f" {len(lines)} by path, breakage and verdict\n"
            + "\n".join(lines),
            pytrace=False,
        )


def test_every_place_the_reply_proof_names_is_broken_by_some_case(
    kernel_replies: dict[Case, JSONValue],
) -> None:
    """Each path of the reply proof's three tables is broken in some case's reply."""
    tables = _proof_paths()
    assert set(tables) == {"replyRange", "replyText", "replyNonEmpty"}
    broken = {change.path for case in CASES for change in _breaks(kernel_replies[case], _ROOT, ())}
    unbroken = {table: sorted(paths - broken) for table, paths in tables.items()}
    assert unbroken == {table: [] for table in tables}
