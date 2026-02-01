"""Shared test fixtures for all test modules

Provides common setup and mock configurations to eliminate duplication
across test files.
"""

from collections.abc import Callable, Generator
from contextlib import contextmanager, AbstractContextManager
from dataclasses import dataclass
from unittest.mock import Mock, patch

import pytest

from aletheia import Signal, StreamingClient
from aletheia.dsl import Property
from aletheia.protocols import DBCDefinition


@dataclass(frozen=True)
class CANFrame:
    """CAN frame test data with named fields for clarity."""
    timestamp: int
    can_id: int
    data: list[int]

# Fixtures are collected by pytest via the @pytest.fixture decorator.
# Exporting them signals they are part of this module's public API.
__all__ = [
    "CANFrame",
    "_mock_process",
    "_mock_streaming_client",
    "_sample_dbc",
    "_sample_property",
    "_sample_can_frame",
    "_mock_popen_factory",
]


@pytest.fixture(name="mock_process")
def _mock_process() -> Mock:
    """Mock subprocess.Popen process with standard success response"""
    process = Mock()
    process.stdin = Mock()
    process.stdout = Mock()
    process.stdout.readline.return_value = b'{"status": "success"}\n'
    process.poll.return_value = None
    return process


@pytest.fixture(name="mock_streaming_client")
def _mock_streaming_client(mock_process: Mock) -> Generator[StreamingClient, None, None]:
    """Mock StreamingClient with subprocess patched"""
    with patch('subprocess.Popen', return_value=mock_process):
        with StreamingClient() as client:
            yield client


@pytest.fixture(name="sample_dbc")
def _sample_dbc() -> DBCDefinition:
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
def _sample_property() -> Property:
    """Sample LTL property for testing"""
    return Signal("Speed").less_than(220).always()


@pytest.fixture(name="sample_can_frame")
def _sample_can_frame() -> CANFrame:
    """Sample CAN frame data for testing"""
    return CANFrame(
        timestamp=1000,
        can_id=0x100,
        data=[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
    )


# Type alias for the mock factory callable
MockPopenFactory = Callable[[list[str]], AbstractContextManager[Mock]]


@pytest.fixture(name="mock_popen_factory")
def _mock_popen_factory() -> MockPopenFactory:
    """Factory fixture for creating mock Popen with configurable responses.

    Patches aletheia.binary_client.subprocess.Popen by default (where the
    import lives). Also patches get_binary_path to avoid filesystem checks.

    Usage:
        def test_something(mock_popen_factory):
            with mock_popen_factory(['{"status": "success"}\\n']) as mock_proc:
                # mock_proc is the mock process object
                # mock_proc.stdin.write.call_args shows what was written
                ...

    Args (to create_mock_popen):
        responses: List of response strings for stdout.readline()
        patch_path: Override the patch target (default: binary_client path)
    """
    @contextmanager
    def create_mock_popen(
        responses: list[str],
        patch_path: str = 'aletheia.binary_client.subprocess.Popen'
    ) -> Generator[Mock, None, None]:
        process = Mock()
        process.stdin = Mock()
        process.stdout = Mock()
        process.stderr = Mock()
        process.stdout.readline.side_effect = responses
        process.poll.return_value = None
        with patch(patch_path, return_value=process):
            with patch('aletheia.binary_utils.get_binary_path', return_value='/fake/aletheia'):
                yield process

    return create_mock_popen
