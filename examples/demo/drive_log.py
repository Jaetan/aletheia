# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Generate sample CAN log data for the demo.

This module provides sample CAN frames simulating a drive where:
- Vehicle accelerates to 90 kph
- Brakes are applied promptly (within 500ms) when speed > 80 kph
- Vehicle decelerates

The data is designed to satisfy the property:
  "Whenever speed exceeds 80, braking must follow within 500 milliseconds"
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from dataclasses import dataclass


@dataclass
class CANFrame:
    """A single CAN frame with timestamp."""

    timestamp_us: int  # Microseconds
    can_id: int
    data: bytearray

    @property
    def timestamp_ms(self) -> int:
        """Frame timestamp in milliseconds (derived from the microsecond field)."""
        return self.timestamp_us // 1000


def encode_speed(speed_kph: float) -> bytearray:
    """Encode vehicle speed into CAN frame data.

    Speed signal: 16-bit little-endian, factor 0.01, offset 0
    """
    raw = int(speed_kph / 0.01)
    return bytearray([raw & 0xFF, (raw >> 8) & 0xFF, 0, 0, 0, 0, 0, 0])


def encode_brake(pressure_kpa: float, *, active: bool = False) -> bytearray:
    """Encode brake status into CAN frame data.

    BrakePressure: 16-bit little-endian, factor 0.1, offset 0
    BrakeActive: 1-bit at bit 16
    """
    raw_pressure = int(pressure_kpa / 0.1)
    return bytearray(
        [raw_pressure & 0xFF, (raw_pressure >> 8) & 0xFF, 1 if active else 0, 0, 0, 0, 0, 0]
    )


# CAN IDs from the DBC
VEHICLE_DYNAMICS_ID = 0x100  # 256
BRAKE_STATUS_ID = 0x200  # 512

# Demo-scenario thresholds
_BRAKE_APPLY_MS = 1700  # brakes engage within 500ms of crossing 80 kph (~1666ms)
_MIN_BRAKING_SPEED_KPH = 10  # below this the brakes release (pressure 0)


def generate_normal_drive() -> list[CANFrame]:
    """Generate frames for a normal drive where property holds.

    Timeline (ms):
      0-1000: Accelerating, speed 0-60 kph, no braking needed
      1000-2000: Speed 60-90 kph, crosses 80 at ~1600ms
      1650: Brake applied (within 500ms of crossing 80)
      2000-3000: Decelerating with brakes
    """
    frames: list[CANFrame] = []

    # Phase 1: Acceleration (0-1000ms), speed 0->60 kph
    for t in range(0, 1000, 100):  # Every 100ms
        speed = 60 * (t / 1000)  # Linear acceleration
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))
        frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(0)))

    # Phase 2: Continue acceleration (1000-2000ms), speed 60->90 kph
    # Speed crosses 80 kph at t=1666ms
    for t in range(1000, 2000, 100):
        speed = 60 + 30 * ((t - 1000) / 1000)  # 60 + 30 * fraction
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))

        # Apply brakes at 1700ms (within 500ms of crossing 80 at ~1666ms)
        if t >= _BRAKE_APPLY_MS:
            frames.append(
                CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(500, active=True))
            )
        else:
            frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(0)))

    # Phase 3: Deceleration with brakes (2000-3000ms)
    for t in range(2000, 3100, 100):
        speed = max(0, 90 - 90 * ((t - 2000) / 1000))  # Decelerate to 0
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))
        pressure = 800 if speed > _MIN_BRAKING_SPEED_KPH else 0
        frames.append(
            CANFrame(
                t * 1000 + 10000,
                BRAKE_STATUS_ID,
                encode_brake(pressure, active=speed > _MIN_BRAKING_SPEED_KPH),
            )
        )

    # Sort by timestamp
    frames.sort(key=lambda f: f.timestamp_us)
    return frames


def generate_overspeed_drive() -> list[CANFrame]:
    """Generate frames where vehicle exceeds 120 kph speed limit.

    Clear violation scenario for the property "speed < 120 always":
    - Vehicle accelerates normally to 90 kph
    - Then accelerates further to 150 kph (violating 120 limit)
    - Then decelerates back to safe speed
    """
    frames: list[CANFrame] = []

    # Phase 1: Normal acceleration (0-1000ms), speed 0->90 kph
    for t in range(0, 1000, 100):
        speed = 90 * (t / 1000)
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))
        frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(0)))

    # Phase 2: Overspeed (1000-2000ms), speed 90->150 kph
    # Crosses 120 kph at ~1500ms
    for t in range(1000, 2000, 100):
        speed = 90 + 60 * ((t - 1000) / 1000)  # 90 + 60 = 150 max
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))
        frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(0)))

    # Phase 3: Braking and deceleration (2000-3500ms), speed 150->0 kph
    for t in range(2000, 3600, 100):
        speed = max(0, 150 - 100 * ((t - 2000) / 1500))
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))
        pressure = 1000 if speed > _MIN_BRAKING_SPEED_KPH else 0
        frames.append(
            CANFrame(
                t * 1000 + 10000,
                BRAKE_STATUS_ID,
                encode_brake(pressure, active=speed > _MIN_BRAKING_SPEED_KPH),
            )
        )

    frames.sort(key=lambda f: f.timestamp_us)
    return frames


def _shift(frames: list[CANFrame], offset_us: int) -> list[CANFrame]:
    """Return a copy of ``frames`` with every timestamp advanced by ``offset_us``."""
    return [CANFrame(f.timestamp_us + offset_us, f.can_id, f.data) for f in frames]


def generate_combined_drive() -> list[CANFrame]:
    """Build a single monotonic trace: a normal drive, then an overspeed event.

    The normal segment satisfies the speed limit; the overspeed segment is
    time-shifted to continue *after* it (never restarting the clock), so the
    whole trace has strictly non-decreasing timestamps — a requirement of the
    streaming LTL evaluator. VehicleSpeed climbs past the 120 kph limit in the
    second segment, so ``aletheia check`` reports VehicleSpeed violations and
    exits 1. This is the trace written to ``drive.log`` and streamed by the
    flagship ``aletheia check`` example.
    """
    normal = generate_normal_drive()
    gap_us = 100_000  # 100 ms of clear air between the two segments
    offset = max(f.timestamp_us for f in normal) + gap_us
    combined = normal + _shift(generate_overspeed_drive(), offset)
    combined.sort(key=lambda f: f.timestamp_us)
    return combined


def to_candump(frames: list[CANFrame]) -> str:
    """Render frames in candump log format: ``(secs.micros) can0 ID#HEXDATA``."""
    lines = [
        f"({f.timestamp_us / 1_000_000:.6f}) can0 {f.can_id:03X}#{f.data.hex()}" for f in frames
    ]
    return "\n".join(lines) + "\n"


# Pre-generated data for the demo
NORMAL_DRIVE = generate_normal_drive()
OVERSPEED_DRIVE = generate_overspeed_drive()
COMBINED_DRIVE = generate_combined_drive()


if __name__ == "__main__":
    # Regenerate the shipped flagship fixture `drive.log` (a single monotonic
    # normal-then-overspeed trace). Run: `python3 drive_log.py`.
    from pathlib import Path

    out = Path(__file__).resolve().parent / "drive.log"
    out.write_text(to_candump(COMBINED_DRIVE), encoding="utf-8")
    print(f"wrote {out} ({len(COMBINED_DRIVE)} frames)")
