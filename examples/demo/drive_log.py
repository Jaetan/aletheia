"""Generate sample CAN log data for the demo.

This module provides sample CAN frames simulating a drive where:
- Vehicle accelerates to 90 kph
- Brakes are applied promptly (within 500ms) when speed > 80 kph
- Vehicle decelerates

The data is designed to satisfy the property:
  "Whenever speed exceeds 80, braking must follow within 500 milliseconds"
"""

from dataclasses import dataclass


@dataclass
class CANFrame:
    """A single CAN frame with timestamp."""
    timestamp_us: int  # Microseconds
    can_id: int
    data: list[int]

    @property
    def timestamp_ms(self) -> int:
        return self.timestamp_us // 1000


def encode_speed(speed_kph: float) -> list[int]:
    """Encode vehicle speed into CAN frame data.

    Speed signal: 16-bit little-endian, factor 0.01, offset 0
    """
    raw = int(speed_kph / 0.01)
    return [raw & 0xFF, (raw >> 8) & 0xFF, 0, 0, 0, 0, 0, 0]


def encode_brake(pressure_kpa: float, active: bool = False) -> list[int]:
    """Encode brake status into CAN frame data.

    BrakePressure: 16-bit little-endian, factor 0.1, offset 0
    BrakeActive: 1-bit at bit 16
    """
    raw_pressure = int(pressure_kpa / 0.1)
    return [
        raw_pressure & 0xFF,
        (raw_pressure >> 8) & 0xFF,
        1 if active else 0,
        0, 0, 0, 0, 0
    ]


# CAN IDs from the DBC
VEHICLE_DYNAMICS_ID = 0x100  # 256
BRAKE_STATUS_ID = 0x200      # 512


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
        if t >= 1700:
            frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(500, True)))
        else:
            frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(0)))

    # Phase 3: Deceleration with brakes (2000-3000ms)
    for t in range(2000, 3100, 100):
        speed = max(0, 90 - 90 * ((t - 2000) / 1000))  # Decelerate to 0
        frames.append(CANFrame(t * 1000, VEHICLE_DYNAMICS_ID, encode_speed(speed)))
        pressure = 800 if speed > 10 else 0
        frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(pressure, speed > 10)))

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
        pressure = 1000 if speed > 10 else 0
        frames.append(CANFrame(t * 1000 + 10000, BRAKE_STATUS_ID, encode_brake(pressure, speed > 10)))

    frames.sort(key=lambda f: f.timestamp_us)
    return frames


# Pre-generated data for the demo
NORMAL_DRIVE = generate_normal_drive()
OVERSPEED_DRIVE = generate_overspeed_drive()
