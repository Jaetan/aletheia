"""Aletheia - Formally verified CAN frame analysis with LTL

AletheiaClient
==============

AletheiaClient provides streaming LTL checking and signal operations:

    from aletheia import AletheiaClient, Signal

    with AletheiaClient() as client:
        client.parse_dbc(dbc_json)

        # Signal operations work anytime after DBC loaded
        result = client.extract_signals(can_id=0x100, data=frame_bytes)
        speed = result.get("VehicleSpeed", 0.0)

        # Build frames from signal values
        frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 50.0})

        # Update specific signals in a frame
        modified = client.update_frame(can_id=0x100, frame=data, signals={"VehicleSpeed": 130.0})

        # Streaming LTL checking
        client.set_properties([Signal("Speed").less_than(220).always().to_dict()])
        client.start_stream()

        for frame in can_trace:
            # Signal ops work while streaming too!
            response = client.send_frame(timestamp, can_id, data)

        client.end_stream()

Python DSL for LTL Properties
==============================

Use the fluent Signal interface to build properties:

    # Temporal operators
    Signal("Speed").less_than(220).always()
    Signal("DoorClosed").equals(1).eventually()
    Signal("ErrorCode").equals(0xFF).never()

    # Composition
    brake.and_(throttle.equals(0))
    brake.implies(speed_decreases.within(100))
"""

from .client import (
    AletheiaClient,
    AletheiaError,
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
)
from .checks import Check, CheckResult
from .dsl import Signal, Predicate, Property, infinitely_often, eventually_always, never
from .excel_loader import load_checks_from_excel, load_dbc_from_excel, create_template
from .yaml_loader import load_checks

__version__ = "0.3.2"
__all__ = [
    # Client
    "AletheiaClient",
    "SignalExtractionResult",
    # Exceptions
    "AletheiaError",
    "ProcessError",
    "ProtocolError",
    # Check API
    "Check",
    "CheckResult",
    # Excel loader
    "load_checks_from_excel",
    "load_dbc_from_excel",
    "create_template",
    # YAML loader
    "load_checks",
    # DSL
    "Signal",
    "Predicate",
    "Property",
    "infinitely_often",
    "eventually_always",
    "never",
]
