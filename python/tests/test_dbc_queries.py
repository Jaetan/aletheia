"""Tests for dbc_queries multiplexing helpers and definition lookups."""

from aletheia.dbc_queries import (
    always_present_signals,
    is_multiplexed,
    message_by_id,
    message_by_name,
    multiplexed_signals,
    multiplexor_names,
    mux_values,
    signal_by_name,
    signals_for_mux_value,
)
from aletheia.protocols import DBCDefinition, DBCSignalAlways, DBCSignalMultiplexed


def _mux_dbc() -> DBCDefinition:
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x200,
                "name": "MuxMessage",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    DBCSignalAlways(
                        name="MuxSelector", startBit=0, length=8,
                        byteOrder="little_endian", signed=False,
                        factor=1, offset=0, minimum=0, maximum=255,
                        unit="", presence="always",
                    ),
                    DBCSignalMultiplexed(
                        name="Temperature", startBit=8, length=16,
                        byteOrder="little_endian", signed=True,
                        factor=0.1, offset=-40, minimum=-40, maximum=215,
                        unit="degC",
                        multiplexor="MuxSelector", multiplex_values=[0],
                    ),
                    DBCSignalMultiplexed(
                        name="Pressure", startBit=8, length=16,
                        byteOrder="little_endian", signed=False,
                        factor=0.01, offset=0, minimum=0, maximum=655,
                        unit="bar",
                        multiplexor="MuxSelector", multiplex_values=[1],
                    ),
                    DBCSignalAlways(
                        name="Voltage", startBit=40, length=16,
                        byteOrder="little_endian", signed=False,
                        factor=0.01, offset=0, minimum=0, maximum=65,
                        unit="V", presence="always",
                    ),
                ],
            }
        ],
    }


def _plain_dbc() -> DBCDefinition:
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x100,
                "name": "EngineData",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    DBCSignalAlways(
                        name="Speed", startBit=0, length=16,
                        byteOrder="little_endian", signed=False,
                        factor=0.1, offset=0, minimum=0, maximum=300,
                        unit="km/h", presence="always",
                    ),
                ],
            }
        ],
    }


# ---------------------------------------------------------------------------
# is_multiplexed
# ---------------------------------------------------------------------------


def test_is_multiplexed_true() -> None:
    """Verify is multiplexed true."""
    assert is_multiplexed(_mux_dbc()["messages"][0])


def test_is_multiplexed_false() -> None:
    """Verify is multiplexed false."""
    assert not is_multiplexed(_plain_dbc()["messages"][0])


# ---------------------------------------------------------------------------
# always_present_signals / multiplexed_signals
# ---------------------------------------------------------------------------


def test_always_present_signals() -> None:
    """Verify always present signals."""
    sigs = always_present_signals(_mux_dbc()["messages"][0])
    assert [s["name"] for s in sigs] == ["MuxSelector", "Voltage"]


def test_multiplexed_signals() -> None:
    """Verify multiplexed signals."""
    sigs = multiplexed_signals(_mux_dbc()["messages"][0])
    assert [s["name"] for s in sigs] == ["Temperature", "Pressure"]


def test_always_present_no_mux() -> None:
    """Verify always present no mux."""
    msg = _plain_dbc()["messages"][0]
    assert len(always_present_signals(msg)) == 1


def test_multiplexed_no_mux() -> None:
    """Verify multiplexed no mux."""
    msg = _plain_dbc()["messages"][0]
    assert multiplexed_signals(msg) == []


# ---------------------------------------------------------------------------
# multiplexor_names
# ---------------------------------------------------------------------------


def test_multiplexor_names() -> None:
    """Verify multiplexor names."""
    assert multiplexor_names(_mux_dbc()["messages"][0]) == ["MuxSelector"]


def test_multiplexor_names_empty() -> None:
    """Verify multiplexor names empty."""
    assert not multiplexor_names(_plain_dbc()["messages"][0])


# ---------------------------------------------------------------------------
# mux_values
# ---------------------------------------------------------------------------


def test_mux_values() -> None:
    """Verify mux values."""
    assert mux_values(_mux_dbc()["messages"][0], "MuxSelector") == [0, 1]


def test_mux_values_unknown() -> None:
    """Verify mux values unknown."""
    assert not mux_values(_mux_dbc()["messages"][0], "NonExistent")


# ---------------------------------------------------------------------------
# signals_for_mux_value
# ---------------------------------------------------------------------------


def test_signals_for_mux_value_0() -> None:
    """Verify signals for mux value 0."""
    sigs = signals_for_mux_value(_mux_dbc()["messages"][0], "MuxSelector", 0)
    assert [s["name"] for s in sigs] == ["MuxSelector", "Temperature", "Voltage"]


def test_signals_for_mux_value_1() -> None:
    """Verify signals for mux value 1."""
    sigs = signals_for_mux_value(_mux_dbc()["messages"][0], "MuxSelector", 1)
    assert [s["name"] for s in sigs] == ["MuxSelector", "Pressure", "Voltage"]


def test_signals_for_mux_value_unknown() -> None:
    """Verify signals for mux value unknown."""
    sigs = signals_for_mux_value(_mux_dbc()["messages"][0], "MuxSelector", 99)
    assert [s["name"] for s in sigs] == ["MuxSelector", "Voltage"]


def test_signals_for_mux_value_unknown_multiplexor() -> None:
    """Verify signals for mux value unknown multiplexor."""
    sigs = signals_for_mux_value(_mux_dbc()["messages"][0], "NonExistent", 0)
    assert [s["name"] for s in sigs] == ["MuxSelector", "Voltage"]


# ---------------------------------------------------------------------------
# message_by_id / message_by_name
# ---------------------------------------------------------------------------


def test_message_by_id() -> None:
    """Verify message by id."""
    msg = message_by_id(_mux_dbc(), 0x200)
    assert msg is not None
    assert msg["name"] == "MuxMessage"


def test_message_by_id_not_found() -> None:
    """Verify message by id not found."""
    assert message_by_id(_mux_dbc(), 0x999) is None


def test_message_by_id_extended_vs_standard() -> None:
    # Standard ID 0x200 exists; extended 0x200 should not match.
    """Verify message by id extended vs standard."""
    assert message_by_id(_mux_dbc(), 0x200, extended=True) is None


def test_message_by_name() -> None:
    """Verify message by name."""
    msg = message_by_name(_mux_dbc(), "MuxMessage")
    assert msg is not None
    assert msg["id"] == 0x200


def test_message_by_name_not_found() -> None:
    """Verify message by name not found."""
    assert message_by_name(_mux_dbc(), "NoSuch") is None


# ---------------------------------------------------------------------------
# signal_by_name
# ---------------------------------------------------------------------------


def test_signal_by_name() -> None:
    """Verify signal by name."""
    sig = signal_by_name(_mux_dbc()["messages"][0], "Temperature")
    assert sig is not None
    assert sig["signed"] is True


def test_signal_by_name_not_found() -> None:
    """Verify signal by name not found."""
    assert signal_by_name(_mux_dbc()["messages"][0], "NoSuch") is None


# ---------------------------------------------------------------------------
# Edge cases: empty signals
# ---------------------------------------------------------------------------


def _empty_msg() -> DBCDefinition:
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x500,
                "name": "EmptyMsg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [],
            }
        ],
    }


def test_empty_signals_is_multiplexed() -> None:
    """Verify empty signals is multiplexed."""
    assert not is_multiplexed(_empty_msg()["messages"][0])


def test_empty_signals_always_present() -> None:
    """Verify empty signals always present."""
    assert always_present_signals(_empty_msg()["messages"][0]) == []


def test_empty_signals_multiplexor_names() -> None:
    """Verify empty signals multiplexor names."""
    assert not multiplexor_names(_empty_msg()["messages"][0])


# ---------------------------------------------------------------------------
# Multiple distinct multiplexors
# ---------------------------------------------------------------------------


def _dual_mux_dbc() -> DBCDefinition:
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x400,
                "name": "DualMuxMsg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    DBCSignalAlways(
                        name="MuxA", startBit=0, length=4,
                        byteOrder="little_endian", signed=False,
                        factor=1, offset=0, minimum=0, maximum=15,
                        unit="", presence="always",
                    ),
                    DBCSignalMultiplexed(
                        name="SigA1", startBit=8, length=8,
                        byteOrder="little_endian", signed=False,
                        factor=1, offset=0, minimum=0, maximum=255,
                        unit="",
                        multiplexor="MuxA", multiplex_values=[0],
                    ),
                    DBCSignalAlways(
                        name="MuxB", startBit=4, length=4,
                        byteOrder="little_endian", signed=False,
                        factor=1, offset=0, minimum=0, maximum=15,
                        unit="", presence="always",
                    ),
                    DBCSignalMultiplexed(
                        name="SigB1", startBit=16, length=8,
                        byteOrder="little_endian", signed=False,
                        factor=1, offset=0, minimum=0, maximum=255,
                        unit="",
                        multiplexor="MuxB", multiplex_values=[0],
                    ),
                    DBCSignalMultiplexed(
                        name="SigA2", startBit=8, length=8,
                        byteOrder="little_endian", signed=False,
                        factor=1, offset=0, minimum=0, maximum=255,
                        unit="",
                        multiplexor="MuxA", multiplex_values=[1],
                    ),
                ],
            }
        ],
    }


def test_multiplexor_names_multiple() -> None:
    """Verify multiplexor names multiple."""
    names = multiplexor_names(_dual_mux_dbc()["messages"][0])
    assert names == ["MuxA", "MuxB"]


def test_mux_values_dual() -> None:
    """Verify mux values dual."""
    msg = _dual_mux_dbc()["messages"][0]
    assert mux_values(msg, "MuxA") == [0, 1]
    assert mux_values(msg, "MuxB") == [0]


# ---------------------------------------------------------------------------
# message_by_id with extended ID
# ---------------------------------------------------------------------------


def _extended_dbc() -> DBCDefinition:
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 0x200,
                "name": "StdMsg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [],
            },
            {
                "id": 0x200,
                "name": "ExtMsg",
                "dlc": 8,
                "sender": "ECU",
                "extended": True,
                "signals": [],
            },
        ],
    }


def test_message_by_id_extended_positive() -> None:
    """Verify message by id extended positive."""
    msg = message_by_id(_extended_dbc(), 0x200, extended=True)
    assert msg is not None
    assert msg["name"] == "ExtMsg"


def test_message_by_id_standard_in_mixed_dbc() -> None:
    """Verify message by id standard in mixed dbc."""
    std = message_by_id(_extended_dbc(), 0x200, extended=False)
    assert std is not None
    assert std["name"] == "StdMsg"
