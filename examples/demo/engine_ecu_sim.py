"""Engine ECU Simulator with Staleness Bug

Simulates an Engine ECU that sends periodic CAN messages containing:
- EngineRPM (16-bit, factor 0.25)
- CoolantTemp (8-bit, factor 1, offset -40)
- FrameCounter (4-bit alive counter, cycles 0-15)

The staleness bug: after a certain point the ECU firmware freezes internally
but keeps sending frames. The FrameCounter stops incrementing — it is stuck
at the same value. RPM and temperature still look plausible because the
frozen firmware replays its last computed values.

This is a real-world failure mode in automotive ECUs. The alive counter
exists precisely to detect this, but naive value-range tests cannot catch it.
"""

from dataclasses import dataclass

# CAN message ID for the Engine ECU
ENGINE_STATUS_ID = 0x300  # 768

# DBC definition for the Engine ECU
ENGINE_DBC = {
    "version": "1.0",
    "messages": [
        {
            "id": ENGINE_STATUS_ID,
            "name": "EngineStatus",
            "dlc": 8,
            "sender": "EngineECU",
            "signals": [
                {
                    "name": "EngineRPM",
                    "startBit": 0,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 0.25,
                    "offset": 0.0,
                    "minimum": 0.0,
                    "maximum": 16383.75,
                    "unit": "rpm",
                    "presence": "always",
                },
                {
                    "name": "CoolantTemp",
                    "startBit": 16,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0,
                    "offset": -40.0,
                    "minimum": -40.0,
                    "maximum": 215.0,
                    "unit": "degC",
                    "presence": "always",
                },
                {
                    "name": "FrameCounter",
                    "startBit": 24,
                    "length": 4,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0,
                    "offset": 0.0,
                    "minimum": 0.0,
                    "maximum": 15.0,
                    "unit": "",
                    "presence": "always",
                },
            ],
        }
    ],
}


@dataclass
class CANFrame:
    """A single CAN frame with timestamp."""
    timestamp_us: int
    can_id: int
    data: bytearray


def _encode_engine_frame(rpm: float, coolant_c: float, counter: int) -> bytearray:
    """Encode Engine ECU signals into a CAN frame.

    Layout (little-endian):
      Byte 0-1: EngineRPM (raw = rpm / 0.25)
      Byte 2:   CoolantTemp (raw = coolant_c + 40)
      Byte 3:   FrameCounter in low nibble (bits 24-27)
      Byte 4-7: unused (zero)
    """
    raw_rpm = int(rpm / 0.25)
    raw_temp = int(coolant_c + 40)
    raw_counter = counter & 0x0F
    return bytearray([
        raw_rpm & 0xFF,
        (raw_rpm >> 8) & 0xFF,
        raw_temp & 0xFF,
        raw_counter,
        0, 0, 0, 0,
    ])


def generate_normal_trace(n_frames: int = 50) -> list[CANFrame]:
    """Generate a healthy Engine ECU trace.

    - RPM ramps from idle (800) to 3000 over the trace
    - Coolant temperature rises from 60C to 90C
    - FrameCounter increments every frame, cycling 0-15
    - Counter starts at 1 (not 0) to avoid first-frame changedBy artifact
    """
    frames: list[CANFrame] = []
    for i in range(n_frames):
        t_us = i * 10_000  # 10ms period = 100 Hz
        rpm = 800 + (2200 * i / n_frames)
        coolant = 60 + (30 * i / n_frames)
        counter = (i + 1) % 16  # Start at 1: avoids |1 - 0| = 0 on first frame
        frames.append(CANFrame(t_us, ENGINE_STATUS_ID,
                               _encode_engine_frame(rpm, coolant, counter)))
    return frames


def generate_frozen_trace(
    n_frames: int = 50,
    freeze_at: int = 15,
) -> list[CANFrame]:
    """Generate a trace where the ECU freezes after `freeze_at` frames.

    Before freeze: normal operation, counter increments.
    After freeze: RPM and temperature still look plausible (last computed
    values with small noise), but FrameCounter is stuck.

    This simulates an ECU whose main loop has hung but whose CAN TX
    hardware continues retransmitting the last buffer.
    """
    frames: list[CANFrame] = []
    frozen_counter = (freeze_at + 1) % 16  # Match normal trace offset

    for i in range(n_frames):
        t_us = i * 10_000

        if i < freeze_at:
            # Normal operation
            rpm = 800 + (2200 * i / n_frames)
            coolant = 60 + (30 * i / n_frames)
            counter = (i + 1) % 16  # Start at 1, matching normal trace
        else:
            # Frozen: RPM and temp stay at last values (ECU retransmits buffer)
            rpm = 800 + (2200 * freeze_at / n_frames)
            coolant = 60 + (30 * freeze_at / n_frames)
            counter = frozen_counter  # STUCK!

        frames.append(CANFrame(t_us, ENGINE_STATUS_ID,
                               _encode_engine_frame(rpm, coolant, counter)))
    return frames
