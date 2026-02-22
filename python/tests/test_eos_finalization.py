"""Tests for end-of-stream property finalization.

Verifies that properties are correctly finalized when end_stream() is called.
"""

import pytest
from aletheia.client import AletheiaClient
from aletheia.dsl import Signal


SIMPLE_DBC = {
    "version": "1.0",
    "messages": [{
        "id": 256,
        "name": "Test",
        "dlc": 8,
        "sender": "ECU",
        "signals": [{
            "name": "Speed",
            "startBit": 0,
            "length": 16,
            "byteOrder": "little_endian",
            "signed": False,
            "factor": 1.0,
            "offset": 0.0,
            "minimum": 0.0,
            "maximum": 65535.0,
            "unit": "kph",
            "presence": "always",
        }],
    }],
}


class TestEndOfStreamFinalization:
    """End-of-stream property finalization."""

    def test_always_satisfied_multi_frame(self) -> None:
        """Always property that holds → satisfaction at end-of-stream."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 256, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            results = resp.get("results", [])
            assert len(results) == 1
            assert results[0]["status"] == "satisfaction"

    def test_changed_by_never_one_frame(self) -> None:
        """1-frame changed_by(0).never() → violation (never resolved)."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").changed_by(0).never().to_dict()
            ])
            client.start_stream()
            client.send_frame(0, 256, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            results = resp.get("results", [])
            assert len(results) == 1
            assert results[0]["status"] == "violation"
            assert "never resolved" in results[0].get("reason", "")

    def test_always_zero_frames(self) -> None:
        """0-frame Always → violation (never resolved)."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            resp = client.end_stream()
            results = resp.get("results", [])
            assert len(results) == 1
            assert results[0]["status"] == "violation"

    def test_eventually_never_satisfied(self) -> None:
        """Eventually never satisfied → violation at end-of-stream."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").greater_than(1000).eventually().to_dict()
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 256, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            results = resp.get("results", [])
            assert len(results) == 1
            assert results[0]["status"] == "violation"
            assert "Eventually" in results[0].get("reason", "")

    def test_multiple_properties_mixed(self) -> None:
        """Multiple properties: some hold, some fail at end-of-stream."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                # Property 0: Always(Speed < 100) — will hold
                Signal("Speed").less_than(100).always().to_dict(),
                # Property 1: Eventually(Speed > 1000) — will fail
                Signal("Speed").greater_than(1000).eventually().to_dict(),
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 256, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            results = resp.get("results", [])
            assert len(results) == 2
            # Property 0: satisfaction
            assert results[0]["status"] == "satisfaction"
            # Property 1: violation
            assert results[1]["status"] == "violation"

    def test_results_field_present(self) -> None:
        """end_stream() response always has 'results' field."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            client.send_frame(0, 256, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert "results" in resp
            assert resp["status"].value == "complete"

    def test_no_properties_empty_results(self) -> None:
        """Stream with no properties → empty results list."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([])
            client.start_stream()
            client.send_frame(0, 256, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            results = resp.get("results", [])
            assert len(results) == 0
