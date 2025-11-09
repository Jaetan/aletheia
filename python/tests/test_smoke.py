"""Smoke tests to verify basic functionality"""

import pytest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import CANDecoder, LTL, verify
from aletheia._binary import get_binary_path


def test_binary_exists():
    """Test that the Aletheia binary can be found"""
    try:
        binary = get_binary_path()
        assert binary.exists(), f"Binary not found at {binary}"
        assert binary.is_file(), f"Binary path is not a file: {binary}"
    except FileNotFoundError as e:
        pytest.skip(f"Binary not built yet: {e}")


def test_can_decoder_creation():
    """Test CANDecoder can be instantiated"""
    dbc_data = {
        'version': '1.0',
        'messages': [
            {
                'id': 0x123,
                'name': 'TestMessage',
                'dlc': 8,
                'sender': 'TestECU',
                'signals': []
            }
        ]
    }
    decoder = CANDecoder(dbc_data)
    assert decoder is not None
    assert decoder.dbc_data == dbc_data


def test_ltl_formula_creation():
    """Test LTL formulas can be created"""
    decoder = CANDecoder({'messages': []})
    speed = decoder.signal("speed")
    
    prop1 = LTL.always(speed > 0)
    assert prop1.operator == 'always'
    
    prop2 = LTL.eventually(speed > 100, within=5.0)
    assert prop2.operator == 'eventually_within'
    
    prop3 = LTL.implies(speed > 0, LTL.eventually(speed > 50))
    assert prop3.operator == 'implies'


def test_ltl_serialization():
    """Test LTL formulas can be serialized to dict"""
    decoder = CANDecoder({'messages': []})
    speed = decoder.signal("speed")
    
    prop = LTL.always(speed > 50)
    prop_dict = prop.to_dict()
    
    assert isinstance(prop_dict, dict)
    assert 'operator' in prop_dict
    assert prop_dict['operator'] == 'always'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
