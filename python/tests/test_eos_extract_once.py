# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""End-of-stream enrichment runs ONE extraction pass per frame, not per property.

Pins the extract-once shape of ``end_stream`` violation enrichment: the frame
loop runs at most once per ``end_stream`` (one full-frame extraction per
last-seen frame, merged first-frame-wins, stopping once every wanted signal
has a value) and its result is distributed to every fails/unresolved entry.
``MockBackend`` records exactly one ``<binary:extractAllSignals>`` sentinel per
logical extraction (its binary path raises ``BinaryPathUnsupportedError``, so
the JSON fallback records once), which makes the FFI-call cardinality directly
observable through the public interface — the counting idiom mirrors
``test_backend_protocol.test_full_streaming_session_through_mock``.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import (
    MessageId,
    dbc,
    kernel_message,
    kernel_signal,
    message,
    parse_dbc_reply,
    signal,
)

from aletheia import AletheiaClient, MockBackend, PropertyDiagnostic, ProtocolError, Signal
from aletheia._dbc_types import SignalName
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from aletheia.types import (
        CompleteResponse,
        DBCDefinition,
        ErrorResponse,
        JSONValue,
        LTLFormula,
        PropertyResultEntry,
        ViolationEnrichment,
    )

# Every session below registers real properties, and ``set_properties``
# renders each formula's rational threshold via the kernel renderer — which
# needs a live GHC RTS (the renderer never self-initialises).
pytestmark = pytest.mark.usefixtures("rts_up")

_EXTRACT_SENTINEL = b"<binary:extractAllSignals>"

# parseDBC canned response: two messages, one 8-bit signal each, so the
# client's signal lookup covers both CAN IDs (the mock's binary extraction
# path then raises BinaryPathUnsupportedError and the JSON fallback records
# the sentinel — one per logical extraction).
_PARSE_DBC_RESPONSE = parse_dbc_reply(
    kernel_message(MessageId(256), kernel_signal(SignalName("SigA"))),
    kernel_message(MessageId(512), kernel_signal(SignalName("SigB"))),
)


def _resp(obj: dict[str, JSONValue]) -> bytes:
    """Encode a canned JSON response for the MockBackend queue."""
    return json.dumps(obj).encode("utf-8")


def _two_message_dbc() -> DBCDefinition:
    """Request-side DBC matching ``_PARSE_DBC_RESPONSE``: SigA@256, SigB@512."""
    return dbc(
        [
            message(0x100, "MsgA", [signal("SigA")]),
            message(0x200, "MsgB", [signal("SigB")]),
        ]
    )


def _extraction_resp(values: dict[str, int]) -> bytes:
    """Canned extract-signals success response carrying integer *values*."""
    wire_values: list[JSONValue] = [
        {"name": name, "value": {"numerator": num, "denominator": 1}}
        for name, num in values.items()
    ]
    return _resp({"status": "success", "values": wire_values, "errors": [], "absent": []})


def _fails_entry(index: int) -> JSONValue:
    """One canned fails finalization entry for the endStream results list."""
    return {
        "type": "property",
        "status": "fails",
        "property_index": index,
        "timestamp": 1000,
        "reason": "eventually unmet",
    }


def _holds_entry(index: int) -> JSONValue:
    """One canned holds finalization entry for the endStream results list."""
    return {"type": "property", "status": "holds", "property_index": index}


def _complete_resp(*entries: JSONValue) -> bytes:
    """Canned endStream complete response with the given result entries."""
    return _resp({"status": "complete", "results": list(entries), "warnings": []})


def _queue_session_setup(backend: MockBackend) -> None:
    """Queue the parseDBC / setProperties / startStream responses (in order)."""
    backend.queue_response(_PARSE_DBC_RESPONSE)
    backend.queue_response(_resp({"status": "success"}))
    backend.queue_response(_resp({"status": "success"}))


def _two_signal_properties() -> list[LTLFormula]:
    """Two properties over the same frame set: SigA (msg 256) and SigB (msg 512)."""
    return [
        Signal("SigA").greater_than(10).eventually().to_dict(),
        Signal("SigB").greater_than(10).eventually().to_dict(),
    ]


def _get_results(response: CompleteResponse | ErrorResponse) -> list[PropertyResultEntry]:
    """Narrow an end_stream response to its finalization results list."""
    assert response["status"] == "complete"
    return response["results"]


def _get_enrichment(entry: PropertyResultEntry) -> ViolationEnrichment:
    """Return the entry's enrichment, asserting it was attached."""
    enrichment = entry.get("enrichment")
    assert enrichment is not None, f"enrichment missing on {entry!r}"
    return enrichment


def test_three_properties_extract_once_per_frame_not_per_property() -> None:
    """Three failing properties share ONE extraction pass over the frame snapshot.

    Two last-seen frames and three failing properties (P0 wants SigA, P1
    wants SigB, P2 wants SigA again — mirroring Go's
    ``TestEndStream_ThreePropertiesShareOneExtractionPass``): the P-outer
    shape would extract 4 times — P0 and P1 each walk one frame (consuming
    the two queued responses), then P2 re-walks both frames against the
    mock's empty-queue defaults — and a naive P×F sweep 6 times.  The
    extract-once shape extracts exactly twice (once per frame), then
    distributes the merged map filtered per diagnostic, sharing SigA's
    single extraction between P0 and P2.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))  # frame 0x100 @ t=0
    backend.queue_response(_resp({"status": "ack"}))  # frame 0x100 @ t=1000
    backend.queue_response(_resp({"status": "ack"}))  # frame 0x200 @ t=2000
    backend.queue_response(_complete_resp(_fails_entry(0), _fails_entry(1), _fails_entry(2)))
    backend.queue_response(_extraction_resp({"SigA": 5}))  # frame 0x100 (sorted first)
    backend.queue_response(_extraction_resp({"SigB": 7}))  # frame 0x200

    properties = [
        *_two_signal_properties(),
        Signal("SigA").less_than(3).eventually().to_dict(),  # P2 re-wants SigA
    ]
    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(properties)
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        client.send_frame(1000, 0x100, DLCCode(8), bytes(8))  # overwrites last 0x100
        client.send_frame(2000, 0x200, DLCCode(8), bytes(8))
        response = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 2

    results = _get_results(response)
    enrichment_a = _get_enrichment(results[0])
    assert enrichment_a["signals"] == {"SigA": Fraction(5)}
    assert "SigA = 5" in enrichment_a["enriched_reason"]
    enrichment_b = _get_enrichment(results[1])
    assert enrichment_b["signals"] == {"SigB": Fraction(7)}
    # P0 and P2 both want SigA — the single shared pass hands both the SAME
    # value (the P-outer shape would have handed P2 a separate extraction).
    enrichment_a2 = _get_enrichment(results[2])
    assert enrichment_a2["signals"] == enrichment_a["signals"]
    assert enrichment_a2["signals"] == {"SigA": Fraction(5)}


def test_frame_loop_breaks_early_once_union_is_covered() -> None:
    """The frame loop stops as soon as every wanted signal has a value.

    The first (lowest-CAN-ID) frame's extraction already supplies both
    properties' signals, so the second last-seen frame is never extracted.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_fails_entry(0), _fails_entry(1)))
    backend.queue_response(_extraction_resp({"SigA": 5, "SigB": 7}))  # covers the union

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        client.send_frame(1000, 0x200, DLCCode(8), bytes(8))
        response = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 1

    results = _get_results(response)
    assert _get_enrichment(results[0])["signals"] == {"SigA": Fraction(5)}
    assert _get_enrichment(results[1])["signals"] == {"SigB": Fraction(7)}


def test_merge_is_first_frame_wins_not_overwrite() -> None:
    """A signal seen on two frames keeps the FIRST (lowest-CAN-ID) value.

    Frame 0x100's extraction yields SigA=1; frame 0x200's yields SigA=2 and
    SigB=3.  The union {SigA, SigB} is not covered after the first frame
    (SigB is still missing), so the loop continues to 0x200 — and the merge
    must keep SigA=1 from the first frame while adopting SigB=3.  An
    overwrite/last-wins merge would report SigA=2 instead.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))  # frame 0x100
    backend.queue_response(_resp({"status": "ack"}))  # frame 0x200
    backend.queue_response(_complete_resp(_fails_entry(0), _fails_entry(1)))
    backend.queue_response(_extraction_resp({"SigA": 1}))  # frame 0x100 (sorted first)
    backend.queue_response(_extraction_resp({"SigA": 2, "SigB": 3}))  # frame 0x200

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        client.send_frame(1000, 0x200, DLCCode(8), bytes(8))
        response = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 2

    results = _get_results(response)
    # First frame wins: SigA=1 from frame 0x100, not the 0x200 re-extraction.
    assert _get_enrichment(results[0])["signals"] == {"SigA": Fraction(1)}
    assert _get_enrichment(results[1])["signals"] == {"SigB": Fraction(3)}


def test_no_tracked_frames_attaches_fallback_without_extraction() -> None:
    """Zero tracked frames costs zero FFI calls, yet enrichment still attaches."""
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_complete_resp(_fails_entry(0)))

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        response = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 0

    results = _get_results(response)
    enrichment = _get_enrichment(results[0])
    assert enrichment["signals"] == {}
    assert enrichment["enriched_reason"].startswith("violated: ")


def _signalless_diagnostic(_formula: LTLFormula) -> PropertyDiagnostic:
    """Return a diagnostic naming no signal, which no formula builds."""
    return PropertyDiagnostic(signals=(), formula_desc="eventually(nothing)")


def test_an_empty_union_extracts_no_tracked_frame(monkeypatch: pytest.MonkeyPatch) -> None:
    """Diagnostics naming no signal extract no tracked frame, and the entry still enriches.

    Every formula reaches an atomic predicate naming a signal, so the
    diagnostics are built naming none here: with two frames tracked, the
    frame loop stops at its head before the first extraction.
    """
    monkeypatch.setattr("aletheia.client._client.build_diagnostic", _signalless_diagnostic)
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_fails_entry(0)))
    # Read only by a loop that extracts, so the count below is what refuses it.
    backend.queue_response(_extraction_resp({"SigA": 5}))
    backend.queue_response(_extraction_resp({"SigB": 7}))

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        client.send_frame(1000, 0x200, DLCCode(8), bytes(8))
        response = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 0
    enrichment = _get_enrichment(_get_results(response)[0])
    assert enrichment["signals"] == {}
    assert enrichment["enriched_reason"] == "violated: eventually(nothing) [core: eventually unmet]"


def test_all_satisfied_costs_zero_extractions() -> None:
    """No fails/unresolved entries → no extraction pass and no enrichment."""
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_holds_entry(0), _holds_entry(1)))

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        response = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 0

    results = _get_results(response)
    assert len(results) == 2
    for entry in results:
        assert "enrichment" not in entry


def test_a_property_index_past_the_properties_raises_key_error() -> None:
    """An end-of-stream result indexes the diagnostics with its ``property_index`` directly.

    The kernel proves every index below the number of properties
    ``set_properties`` was handed, so one past them raises the diagnostics
    map's own ``KeyError`` before any extraction runs.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_fails_entry(1)))

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties([Signal("SigA").greater_than(10).eventually().to_dict()])
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        with pytest.raises(KeyError, match=r"^1$"):
            _ = client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 0


def test_failed_extraction_raises_from_end_stream() -> None:
    """A last-seen frame's extraction answered with an error raises from end_stream.

    Two failing properties over one last-seen frame: the shared pass
    attempts the frame once and the extraction's ``ProtocolError`` reaches
    the caller rather than leaving the entries with a fallback enrichment.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_fails_entry(0), _fails_entry(1)))
    backend.queue_response(_resp({"status": "error", "message": "boom"}))  # extraction fails

    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        with pytest.raises(ProtocolError):
            client.end_stream()

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 1


_ONE_MESSAGE_DBC_TEXT = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n'
    'BO_ 256 Msg: 8 ECU\n SG_ Sig : 0|16@1+ (0.25,0) [0|8000] "u" ECU\n\n'
)


def test_an_unknown_identifier_ahead_keeps_the_verdicts() -> None:
    """A trace holding an identifier the DBC lacks ends with its verdicts enriched.

    On the real kernel: the unknown identifier's last frame sorts first and is
    extracted first, and the kernel answers it with an error entry rather
    than a refusal, so end_stream keeps the failing verdict and its values.
    """
    with AletheiaClient() as client:
        client.parse_dbc_text(_ONE_MESSAGE_DBC_TEXT)
        client.set_properties([Signal("Sig").less_than(10).eventually().to_dict()])
        client.start_stream()
        client.send_frame(1000, 0x100, DLCCode(8), bytes([0xFF, 0, 0, 0, 0, 0, 0, 0]))
        client.send_frame(2000, 0x050, DLCCode(8), bytes([0xFF, 0, 0, 0, 0, 0, 0, 0]))
        result = client.end_stream()

    assert result["status"] == "complete"
    [entry] = result["results"]
    assert entry["status"] == "fails"
    # Sig reads 0x00FF counts of a quarter.
    assert _get_enrichment(entry)["signals"] == {"Sig": Fraction(255, 4)}


# What the kernel writes on an Eventually property the trace never met.
_UNMET = "Eventually: never satisfied before end of stream"
_UNMET_FORMULA = "eventually(Speed > 250)"


def _speed_never_above_250(speed: Fraction) -> CompleteResponse:
    """Return the complete reply of ``eventually(Speed > 250)`` with Speed last read as *speed*."""
    enrichment: ViolationEnrichment = {
        "signals": {"Speed": speed},
        "formula_desc": _UNMET_FORMULA,
        "enriched_reason": f"Speed = {speed} (formula: {_UNMET_FORMULA}) [core: {_UNMET}]",
        "core_reason": _UNMET,
    }
    entry: PropertyResultEntry = {
        "type": "property",
        "property_index": 0,
        "status": "fails",
        "timestamp": 0,
        "reason": _UNMET,
        "enrichment": enrichment,
    }
    return {"status": "complete", "results": [entry], "warnings": []}


def test_an_extended_last_frame_enriches_the_end_of_stream_failure() -> None:
    """A 29-bit last frame is extracted from its own extended message.

    The identifier is past the 11-bit range, so it names the extended message
    only, and the entry carries the value read from it, the formula's text and
    the kernel's reason in both of the fields that hold it.
    """
    extended_id = 0x18FF0001
    extended_message = message(extended_id, "ExtMsg", [signal("Speed")])
    extended_message["extended"] = True
    with AletheiaClient() as client:
        client.parse_dbc(dbc([extended_message]))
        client.set_properties([Signal("Speed").greater_than(250).eventually().to_dict()])
        client.start_stream()
        client.send_frame(
            1000, extended_id, DLCCode(8), bytes([200, 0, 0, 0, 0, 0, 0, 0]), extended=True
        )
        response = client.end_stream()

    assert response == _speed_never_above_250(Fraction(200))


def test_the_lowest_identifier_last_frame_gives_a_shared_signal() -> None:
    """A signal three last frames carry is read from the lowest ``(identifier, extended)`` key.

    The frames arrive highest identifier first, the extended 0x100 frame
    carrying the smallest payload, so an order by arrival, by DLC (a tie here,
    left in arrival order) or by payload reads another frame's value than the
    standard 0x100 frame's 20.
    """
    extended_message = message(0x100, "ExtMsg", [signal("Speed")])
    extended_message["extended"] = True
    shared = dbc(
        [
            message(0x100, "StdMsg", [signal("Speed")]),
            extended_message,
            message(0x200, "Other", [signal("Speed")]),
        ]
    )
    with AletheiaClient() as client:
        client.parse_dbc(shared)
        client.set_properties([Signal("Speed").greater_than(250).eventually().to_dict()])
        client.start_stream()
        client.send_frame(1000, 0x200, DLCCode(8), bytes([30, 0, 0, 0, 0, 0, 0, 0]))
        client.send_frame(2000, 0x100, DLCCode(8), bytes([10, 0, 0, 0, 0, 0, 0, 0]), extended=True)
        client.send_frame(3000, 0x100, DLCCode(8), bytes([20, 0, 0, 0, 0, 0, 0, 0]))
        response = client.end_stream()

    assert response == _speed_never_above_250(Fraction(20))
