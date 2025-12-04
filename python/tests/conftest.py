"""Shared test fixtures for all test modules

Provides common setup and mock configurations to eliminate duplication
across test files.
"""

import pytest
from unittest.mock import Mock, patch


@pytest.fixture
def mock_process():
    """Mock subprocess.Popen process with standard success response"""
    process = Mock()
    process.stdin = Mock()
    process.stdout = Mock()
    process.stdout.readline.return_value = b'{"status": "success"}\n'
    process.poll.return_value = None
    return process


@pytest.fixture
def mock_streaming_client(mock_process):
    """Mock StreamingClient with subprocess patched"""
    with patch('subprocess.Popen', return_value=mock_process):
        from aletheia import StreamingClient
        with StreamingClient() as client:
            yield client


@pytest.fixture
def sample_dbc():
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


@pytest.fixture
def sample_property():
    """Sample LTL property for testing"""
    from aletheia import Signal
    return Signal("Speed").less_than(220).always()


@pytest.fixture
def sample_can_frame():
    """Sample CAN frame data (timestamp, id, data)"""
    return (1000, 0x100, [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07])
