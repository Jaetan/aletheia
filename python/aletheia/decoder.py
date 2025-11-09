"""CAN frame decoder"""

from pathlib import Path
from typing import Dict, Any
import yaml


class CANDecoder:
    """Decoder for CAN frames using DBC specification"""
    
    def __init__(self, dbc_data: Dict[str, Any]):
        """Initialize decoder with DBC data
        
        Args:
            dbc_data: Parsed DBC YAML data
        """
        self.dbc_data = dbc_data
        self._messages = {msg['id']: msg for msg in dbc_data.get('messages', [])}
    
    @classmethod
    def from_dbc(cls, dbc_file: str) -> 'CANDecoder':
        """Load DBC from YAML file
        
        Args:
            dbc_file: Path to DBC YAML file
            
        Returns:
            Configured CANDecoder instance
        """
        with open(dbc_file, 'r') as f:
            dbc_data = yaml.safe_load(f)
        return cls(dbc_data)
    
    def signal(self, signal_name: str) -> 'SignalRef':
        """Create a reference to a signal for use in LTL formulas
        
        Args:
            signal_name: Name of the signal
            
        Returns:
            SignalRef that can be used in comparisons
        """
        return SignalRef(signal_name)
    
    def decode(self, frame_id: int, data: bytes) -> Dict[str, float]:
        """Decode a CAN frame to signal values
        
        Args:
            frame_id: CAN frame identifier
            data: Frame data bytes
            
        Returns:
            Dictionary mapping signal names to values
        """
        # TODO: Call Agda backend for proven-correct decoding
        raise NotImplementedError("Decoding not yet implemented")


class SignalRef:
    """Reference to a CAN signal for use in LTL formulas"""
    
    def __init__(self, name: str):
        self.name = name
    
    def __gt__(self, other: float) -> 'Comparison':
        return Comparison(self, 'GT', other)
    
    def __lt__(self, other: float) -> 'Comparison':
        return Comparison(self, 'LT', other)
    
    def __ge__(self, other: float) -> 'Comparison':
        return Comparison(self, 'GE', other)
    
    def __le__(self, other: float) -> 'Comparison':
        return Comparison(self, 'LE', other)
    
    def __eq__(self, other: float) -> 'Comparison':  # type: ignore
        return Comparison(self, 'EQ', other)
    
    def __ne__(self, other: float) -> 'Comparison':  # type: ignore
        return Comparison(self, 'NE', other)


class Comparison:
    """Signal comparison expression"""
    
    def __init__(self, signal: SignalRef, op: str, value: float):
        self.signal = signal
        self.op = op
        self.value = value
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            'type': 'comparison',
            'signal': self.signal.name,
            'op': self.op,
            'value': self.value
        }
