"""Aletheia - Formally verified CAN frame analysis with LTL"""

from aletheia.decoder import CANDecoder, CheckResult, Counterexample
from aletheia.ltl import LTL
from aletheia.dsl import Signal, Predicate, Property
from aletheia.verifier import verify, VerificationResult

__version__ = "0.1.0"
__all__ = [
    "CANDecoder",
    "CheckResult",
    "Counterexample",
    "LTL",
    "Signal",
    "Predicate",
    "Property",
    "verify",
    "VerificationResult"
]
