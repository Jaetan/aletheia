"""Shared test fixtures for all test modules

Provides common setup and mock configurations to eliminate duplication
across test files.
"""

from contextlib import contextmanager
from unittest.mock import Mock, patch

import pytest

from aletheia import Signal, StreamingClient


@pytest.fixture(name="mock_process")
def _mock_process():
    """Mock subprocess.Popen process with standard success response"""
    process = Mock()
    process.stdin = Mock()
    process.stdout = Mock()
    process.stdout.readline.return_value = b'{"status": "success"}\n'
    process.poll.return_value = None
    return process


@pytest.fixture(name="mock_streaming_client")
def _mock_streaming_client(mock_process):
    """Mock StreamingClient with subprocess patched"""
    with patch('subprocess.Popen', return_value=mock_process):
        with StreamingClient() as client:
            yield client


@pytest.fixture(name="sample_dbc")
def _sample_dbc():
    """Sample DBC JSON structure for testing"""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x100,
                "name": "TestMessage",
                "dlc": 8,
                "sender": "TestECU",
                "signals": [
                    {
                        "name": "TestSignal",
                        "startBit": 0,
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 65535.0,
                        "unit": "",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


@pytest.fixture(name="sample_property")
def _sample_property():
    """Sample LTL property for testing"""
    return Signal("Speed").less_than(220).always()


@pytest.fixture(name="sample_can_frame")
def _sample_can_frame():
    """Sample CAN frame data (timestamp, id, data)"""
    return (1000, 0x100, [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07])


@pytest.fixture(name="mock_popen_factory")
def _mock_popen_factory():
    """Factory fixture for creating mock Popen with configurable responses.

    Usage:
        def test_something(mock_popen_factory):
            with mock_popen_factory([b'{"status": "success"}\\n']) as mock_popen:
                # mock_popen is the patched subprocess.Popen
                ...
    """
    @contextmanager
    def create_mock_popen(responses: list[bytes]):
        process = Mock()
        process.stdin = Mock()
        process.stdout = Mock()
        process.stdout.readline.side_effect = responses
        process.poll.return_value = None
        with patch('subprocess.Popen', return_value=process) as mock_popen:
            mock_popen.mock_process = process  # Expose for additional configuration
            yield mock_popen

    return create_mock_popen
