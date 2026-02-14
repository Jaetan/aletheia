#!/usr/bin/env python3
"""DBC Validation Demo

Aletheia validates DBC files automatically during parse_dbc():
  - Signal overlap detection (unless multiplexed to different values)
  - Range consistency (minimum <= maximum)

Requirements:
    - Aletheia built: `cabal run shake -- build`
"""

from aletheia import AletheiaClient


def create_valid_dbc() -> dict:
    """Non-overlapping signals: Temperature[0:15], Pressure[16:31], Status[32:39]."""
    return {
        "version": "1.0",
        "messages": [{
            "id": 256, "name": "SensorData", "dlc": 8, "sender": "ECU",
            "signals": [
                {"name": "Temperature", "startBit": 0, "length": 16,
                 "byteOrder": "little_endian", "signed": True,
                 "factor": 0.1, "offset": -40, "minimum": -40, "maximum": 215,
                 "unit": "C", "presence": "always"},
                {"name": "Pressure", "startBit": 16, "length": 16,
                 "byteOrder": "little_endian", "signed": False,
                 "factor": 0.01, "offset": 0, "minimum": 0, "maximum": 655.35,
                 "unit": "bar", "presence": "always"},
                {"name": "Status", "startBit": 32, "length": 8,
                 "byteOrder": "little_endian", "signed": False,
                 "factor": 1, "offset": 0, "minimum": 0, "maximum": 255,
                 "unit": "", "presence": "always"},
            ],
        }],
    }


def create_overlapping_dbc() -> dict:
    """Overlapping signals: Temperature[0:15] and Pressure[8:23] share bits 8-15."""
    return {
        "version": "1.0",
        "messages": [{
            "id": 256, "name": "SensorData", "dlc": 8, "sender": "ECU",
            "signals": [
                {"name": "Temperature", "startBit": 0, "length": 16,
                 "byteOrder": "little_endian", "signed": True,
                 "factor": 0.1, "offset": -40, "minimum": -40, "maximum": 215,
                 "unit": "C", "presence": "always"},
                {"name": "Pressure", "startBit": 8, "length": 16,
                 "byteOrder": "little_endian", "signed": False,
                 "factor": 0.01, "offset": 0, "minimum": 0, "maximum": 655.35,
                 "unit": "bar", "presence": "always"},
            ],
        }],
    }


def create_inconsistent_range_dbc() -> dict:
    """Temperature minimum=100 > maximum=50."""
    return {
        "version": "1.0",
        "messages": [{
            "id": 256, "name": "SensorData", "dlc": 8, "sender": "ECU",
            "signals": [
                {"name": "Temperature", "startBit": 0, "length": 16,
                 "byteOrder": "little_endian", "signed": True,
                 "factor": 0.1, "offset": -40, "minimum": 100, "maximum": 50,
                 "unit": "C", "presence": "always"},
            ],
        }],
    }


def create_multiplexed_dbc() -> dict:
    """SensorA[8:23] and SensorB[8:23] overlap but are multiplexed (MuxSelector=0 vs 1)."""
    return {
        "version": "1.0",
        "messages": [{
            "id": 256, "name": "MultiplexedData", "dlc": 8, "sender": "ECU",
            "signals": [
                {"name": "MuxSelector", "startBit": 0, "length": 8,
                 "byteOrder": "little_endian", "signed": False,
                 "factor": 1, "offset": 0, "minimum": 0, "maximum": 3,
                 "unit": "", "presence": "always"},
                {"name": "SensorA", "startBit": 8, "length": 16,
                 "byteOrder": "little_endian", "signed": False,
                 "factor": 0.1, "offset": 0, "minimum": 0, "maximum": 6553.5,
                 "unit": "rpm", "multiplexor": "MuxSelector", "multiplex_value": 0},
                {"name": "SensorB", "startBit": 8, "length": 16,
                 "byteOrder": "little_endian", "signed": True,
                 "factor": 0.01, "offset": 0, "minimum": -327.68, "maximum": 327.67,
                 "unit": "m/s", "multiplexor": "MuxSelector", "multiplex_value": 1},
            ],
        }],
    }


def test_dbc(name: str, dbc: dict, expect_valid: bool) -> bool:
    """Parse a DBC and check whether validation passes or fails as expected."""
    try:
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

            valid = response.get("status") == "success"
            passed = valid == expect_valid
            status = "VALID" if valid else "INVALID"
            verdict = "PASS" if passed else "FAIL"
            msg = response.get("message", "")

            print(f"  {name}: {status} — {verdict}")
            if msg:
                print(f"    {msg}")
            return passed

    except Exception as e:
        print(f"  {name}: ERROR — {e}")
        return False


def main() -> None:
    print("=" * 60)
    print("DBC VALIDATION DEMO")
    print("=" * 60)

    results = [
        test_dbc("Valid DBC (no overlap)", create_valid_dbc(), expect_valid=True),
        test_dbc("Overlapping signals", create_overlapping_dbc(), expect_valid=False),
        test_dbc("Inconsistent range (min > max)", create_inconsistent_range_dbc(), expect_valid=False),
        test_dbc("Multiplexed (overlap OK)", create_multiplexed_dbc(), expect_valid=True),
    ]

    passed = sum(results)
    total = len(results)

    print(f"\n{passed}/{total} tests passed")

    print("\n" + "=" * 60)
    print("DONE")
    print("=" * 60)


if __name__ == "__main__":
    main()
