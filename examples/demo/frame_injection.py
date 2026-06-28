# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Frame Injection Demo.

Injects a modified CAN frame mid-stream and verifies that Aletheia
detects the violation at the exact injected frame.

Requirements:
    - Aletheia built: `cabal run shake -- build`
    - Run from the examples/demo directory
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

from drive_log import NORMAL_DRIVE, VEHICLE_DYNAMICS_ID

from aletheia import AletheiaClient, Signal
from aletheia.dbc import dbc_to_json
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from drive_log import CANFrame

_TARGET_SPEED_FRAME = 15  # inject into the 15th VehicleDynamics frame
_INJECTED_SPEED_KPH = 130  # exceeds the 120 kph limit (exact int — the float principle)
_MAX_SHOWN = 3  # violations printed before eliding the rest


class _Violation(NamedTuple):
    """One detected property violation during the injected stream."""

    frame_index: int
    timestamp_ms: int
    reason: str | None


def _find_target_frame(frames: list[CANFrame], target_count: int) -> int | None:
    """Return the index of the ``target_count``-th VehicleDynamics frame."""
    speed_frame_count = 0
    for i, frame in enumerate(frames):
        if frame.can_id == VEHICLE_DYNAMICS_ID:
            speed_frame_count += 1
            if speed_frame_count == target_count:
                return i
    return None


def _stream_with_injection(
    client: AletheiaClient,
    frames: list[CANFrame],
    target_index: int,
    modified_data: bytearray,
    injected_speed: float,
) -> list[_Violation]:
    """Stream ``frames``, substituting ``modified_data`` at ``target_index``."""
    violations: list[_Violation] = []
    for i, frame in enumerate(frames):
        data = modified_data if i == target_index else frame.data
        if i == target_index:
            print(f"  [{i:3d}] >> INJECTING (speed={injected_speed} kph)")
        response = client.send_frame(
            timestamp=frame.timestamp_us,
            can_id=frame.can_id,
            dlc=DLCCode(len(data)),
            data=data,
        )
        if "results" in response:
            fails = [e for e in response["results"] if e["status"] == "fails"]
            if fails:
                violations.append(_Violation(i, frame.timestamp_ms, fails[0].get("reason")))
                print(f"  [{i:3d}] !! VIOLATION at {frame.timestamp_ms}ms")
    return violations


def _print_results(violations: list[_Violation], target_index: int) -> None:
    """Print the injection results summary."""
    print("\n" + "=" * 60)
    print("RESULTS")
    print("=" * 60)

    if not violations:
        print("\n  No violations detected (unexpected)")
        return

    print(f"\n  {len(violations)} violation(s) detected")
    first_idx = violations[0].frame_index
    if first_idx == target_index:
        print(f"  First violation at injected frame #{target_index}")
    else:
        print(f"  First violation at frame #{first_idx} (injection was #{target_index})")

    for v in violations[:_MAX_SHOWN]:
        print(f"    Frame #{v.frame_index} at {v.timestamp_ms}ms")
        if v.reason is not None:
            print(f"      {v.reason}")

    if len(violations) > _MAX_SHOWN:
        print(f"    ... and {len(violations) - _MAX_SHOWN} more")


def main() -> None:
    """Load a DBC, inject an over-limit speed frame, and report the violation."""
    print("=" * 60)
    print("FRAME INJECTION DEMO")
    print("=" * 60)

    dbc_path = Path(__file__).parent / "vehicle.dbc"
    dbc = dbc_to_json(str(dbc_path))

    speed = Signal("VehicleSpeed")
    speed_limit = speed.less_than(120).always()

    print(f"\nDBC: {dbc['version']}")
    print("Property: speed.less_than(120).always()")

    target_index = _find_target_frame(NORMAL_DRIVE, _TARGET_SPEED_FRAME)
    if target_index is None:
        print(f"Error: Could not find frame #{_TARGET_SPEED_FRAME}")
        return
    original_frame = NORMAL_DRIVE[target_index]

    print("\n" + "=" * 60)
    print("PREPARING INJECTION")
    print("=" * 60)

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        dlc = DLCCode(len(original_frame.data))
        original_result = client.extract_signals(
            can_id=original_frame.can_id, dlc=dlc, data=original_frame.data
        )
        original_speed = original_result.get("VehicleSpeed")
        print(f"\n  Frame #{target_index} at {original_frame.timestamp_ms}ms")
        print(f"  Original speed: {original_speed:.1f} kph")

        modified_data = client.update_frame(
            can_id=original_frame.can_id,
            dlc=dlc,
            frame=original_frame.data,
            signals={"VehicleSpeed": _INJECTED_SPEED_KPH},
        )
        print(f"  Injected speed: {_INJECTED_SPEED_KPH:.1f} kph")

        print("\n" + "=" * 60)
        print("STREAMING WITH INJECTION")
        print("=" * 60)
        print(f"\n  {len(NORMAL_DRIVE)} frames, injecting at index {target_index}")

        client.set_properties([speed_limit.to_dict()])
        client.start_stream()
        violations = _stream_with_injection(
            client, NORMAL_DRIVE, target_index, modified_data, _INJECTED_SPEED_KPH
        )
        client.end_stream()

    _print_results(violations, target_index)

    print("\n" + "=" * 60)
    print("DONE")
    print("=" * 60)


if __name__ == "__main__":
    main()
