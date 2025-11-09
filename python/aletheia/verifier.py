"""Main verification interface"""

from pathlib import Path
from typing import List, Any, Dict
from dataclasses import dataclass
import yaml

from aletheia._binary import call_aletheia_binary
from aletheia.decoder import CANDecoder
from aletheia.ltl import LTLFormula


@dataclass
class VerificationResult:
    """Result of LTL verification"""
    
    success: bool
    properties: List[Dict[str, Any]]
    message: str
    
    def __str__(self) -> str:
        if self.success:
            return f"✓ Verification passed: {self.message}"
        else:
            return f"✗ Verification failed: {self.message}"


def verify(
    decoder: CANDecoder,
    trace_file: str,
    properties: List[LTLFormula],
    log_level: str = "info"
) -> VerificationResult:
    """Verify temporal properties over a CAN trace
    
    Args:
        decoder: Configured CAN decoder with DBC loaded
        trace_file: Path to YAML trace file
        properties: List of LTL properties to check
        log_level: Logging verbosity (debug/info/warning/error)
        
    Returns:
        Verification result with pass/fail for each property
    """
    command = {
        'command': 'verify',
        'dbc': decoder.dbc_data,
        'trace_file': trace_file,
        'properties': [p.to_dict() for p in properties],
        'log_level': log_level
    }
    
    response = call_aletheia_binary(command)
    
    return VerificationResult(
        success=response.get('success', False),
        properties=response.get('properties', []),
        message=response.get('message', 'Unknown result')
    )
