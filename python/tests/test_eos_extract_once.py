# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""End-of-stream enrichment runs ONE extraction pass per frame, not per property.

Pins the extract-once shape of ``end_stream`` violation enrichment: the frame
loop runs at most once per ``end_stream`` (one full-frame extraction per
last-seen frame, merged first-frame-wins, early-break once every wanted signal
has a value) and its result is distributed to every fails/unresolved entry.
``MockBackend`` records exactly one ``<binary:extractAllSignals>`` sentinel per
logical extraction (its binary path raises ``BinaryPathUnsupportedError``, so
the JSON fallback records once), which makes the FFI-call cardinality directly
observable through the public interface — the counting idiom mirrors
``test_backend_protocol.test_full_streaming_session_through_mock``.
"""

from __future__ import annotations

import json
import logging
from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, MockBackend, Signal
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
_PARSE_DBC_RESPONSE = (
    b'{"status":"success","dbc":{"version":"",'
    b'"messages":['
    b'{"id":256,"extended":false,"dlc":8,"signals":'
    b'[{"name":"SigA","startBit":0,"length":8,"presence":"always"}]},'
    b'{"id":512,"extended":false,"dlc":8,"signals":'
    b'[{"name":"SigB","startBit":0,"length":8,"presence":"always"}]}]'
    b'},"warnings":[]}'
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
    return {"status": "fails", "property_index": index, "reason": "eventually unmet"}


def _holds_entry(index: int) -> JSONValue:
    """One canned holds finalization entry for the endStream results list."""
    return {"status": "holds", "property_index": index}


def _complete_resp(*entries: JSONValue) -> bytes:
    """Canned endStream complete response with the given result entries."""
    return _resp({"status": "complete", "results": list(entries)})


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
    """Zero tracked frames costs zero FFI calls, yet enrichment still attaches.

    This is also the public pin for the empty-union skip's observable
    contract (0 extractions + enrichment always attached with the
    empty-values fallback reason): an empty diagnostic signal list is
    unreachable through the public API — the collector passes names through
    verbatim and the kernel rejects an empty signal name with the typed
    ``parse_invalid_identifier`` error before diagnostics are ever built —
    uniform with the Go/C++/Rust suites, whose pins take the same shape.
    The skip's condition is separately covered by the sentinel-count pins in
    this file (inverting it would zero out the multi-property test).
    """
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


def test_oob_property_index_warns_excludes_and_spares_valid_entries(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """An out-of-bounds property_index is warned once and excluded.

    The OOB entry gets no enrichment (and drives no extraction of its own),
    while the valid entry in the same finalization batch is still enriched.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_fails_entry(0), _fails_entry(3)))
    backend.queue_response(_extraction_resp({"SigA": 5}))

    with (
        caplog.at_level(logging.WARNING, logger="aletheia"),
        AletheiaClient(backend=backend) as client,
    ):
        client.parse_dbc(_two_message_dbc())
        client.set_properties([Signal("SigA").greater_than(10).eventually().to_dict()])
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        response = client.end_stream()

    oob_messages = [
        record.getMessage()
        for record in caplog.records
        if record.getMessage().startswith("enrichment.property_index_oob")
    ]
    assert len(oob_messages) == 1
    assert "index=3" in oob_messages[0]
    assert "count=1" in oob_messages[0]

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 1

    results = _get_results(response)
    assert _get_enrichment(results[0])["signals"] == {"SigA": Fraction(5)}
    assert "enrichment" not in results[1]


def test_failed_extraction_warns_once_per_frame_not_per_property(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """A failing frame extraction warns once per frame per end_stream.

    Two failing properties over one last-seen frame whose extraction errors:
    the shared pass attempts the frame once and emits ONE
    ``enrichment.extraction_failed`` warning.  The discrimination against
    the P-outer shape is carried by the SENTINEL count (1 vs 2 — each
    property's walk re-extracted the frame), not the warn count: with this
    fixture the old shape also warned exactly once, because the queued
    error response is consumed by the first property's walk and the second
    walk pops the mock's empty-queue default success (empty values, no
    warning).  Both entries still get the fallback enrichment.
    """
    backend = MockBackend()
    _queue_session_setup(backend)
    backend.queue_response(_resp({"status": "ack"}))
    backend.queue_response(_complete_resp(_fails_entry(0), _fails_entry(1)))
    backend.queue_response(_resp({"status": "error", "message": "boom"}))  # extraction fails

    with (
        caplog.at_level(logging.WARNING, logger="aletheia"),
        AletheiaClient(backend=backend) as client,
    ):
        client.parse_dbc(_two_message_dbc())
        client.set_properties(_two_signal_properties())
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        response = client.end_stream()

    failed_messages = [
        record.getMessage()
        for record in caplog.records
        if record.getMessage().startswith("enrichment.extraction_failed")
    ]
    assert len(failed_messages) == 1

    assert backend.inputs.count(_EXTRACT_SENTINEL) == 1

    results = _get_results(response)
    for entry in results:
        enrichment = _get_enrichment(entry)
        assert enrichment["signals"] == {}
        assert enrichment["enriched_reason"].startswith("violated: ")
