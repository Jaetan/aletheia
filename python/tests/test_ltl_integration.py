"""Integration tests for LTL model checking (Phase 2A)

Tests the complete pipeline:
  Python → YAML command → Agda binary → Response parsing

These tests exercise the CheckLTL command with various:
- Property types (always, eventually, never, until, within)
- Signal predicates (compare, between, changed_by)
- Logical connectives (and, or, implies, not)
"""

import pytest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import CANDecoder
from aletheia._binary import get_binary_path


# =============================================================================
# TEST FIXTURES
# =============================================================================

@pytest.fixture
def sample_dbc_yaml():
    """Simple DBC with a Speed signal for testing"""
    return '''version: "1.0"

messages:
  - id: 0x100
    name: "VehicleSpeed"
    dlc: 8
    sender: "ECU"
    signals:
      - name: "Speed"
        start_bit: 0
        bit_length: 16
        byte_order: "little_endian"
        value_type: "unsigned"
        factor: 0.01
        offset: 0
        minimum: 0
        maximum: 655.35
        unit: "km/h"
'''


@pytest.fixture
def decoder(sample_dbc_yaml):
    """Create decoder from sample DBC"""
    import yaml
    dbc_data = yaml.safe_load(sample_dbc_yaml)
    return CANDecoder(dbc_data, sample_dbc_yaml)


@pytest.fixture
def increasing_speed_trace():
    """Trace with speed increasing: 0, 100, 200 km/h"""
    return [
        {'timestamp': 0, 'id': 0x100, 'dlc': 8,
         'data': [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]},  # 0
        {'timestamp': 1000, 'id': 0x100, 'dlc': 8,
         'data': [0x10, 0x27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]},  # 10000 raw = 100.0
        {'timestamp': 2000, 'id': 0x100, 'dlc': 8,
         'data': [0x20, 0x4E, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]},  # 20000 raw = 200.0
    ]


@pytest.fixture
def constant_speed_trace():
    """Trace with constant speed: 150 km/h"""
    return [
        {'timestamp': 0, 'id': 0x100, 'dlc': 8,
         'data': [0x98, 0x3A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]},  # 15000 raw = 150.0
        {'timestamp': 1000, 'id': 0x100, 'dlc': 8,
         'data': [0x98, 0x3A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]},  # 150.0
        {'timestamp': 2000, 'id': 0x100, 'dlc': 8,
         'data': [0x98, 0x3A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]},  # 150.0
    ]


# =============================================================================
# EXAMPLE YAML PROPERTIES
# =============================================================================

# Property 1: Always - Speed always less than 300
ALWAYS_SPEED_LT_300 = '''type: always
formula:
  type: compare
  signal: Speed
  op: LT
  value: 300
'''

# Property 2: Eventually - Speed eventually exceeds 100
EVENTUALLY_SPEED_GT_100 = '''type: eventually
formula:
  type: compare
  signal: Speed
  op: GT
  value: 100
'''

# Property 3: Never - Speed never exceeds 250
NEVER_SPEED_GT_250 = '''type: never
formula:
  type: compare
  signal: Speed
  op: GT
  value: 250
'''

# Property 4: Between - Speed always between 0 and 200
ALWAYS_SPEED_BETWEEN = '''type: always
formula:
  type: between
  signal: Speed
  min: 0
  max: 200
'''

# Property 5: Equals - Speed eventually equals 150
EVENTUALLY_SPEED_EQ_150 = '''type: eventually
formula:
  type: compare
  signal: Speed
  op: EQ
  value: 150
'''

# Property 6: Logical AND - Speed > 50 AND Speed < 180
ALWAYS_SPEED_AND = '''type: always
formula:
  type: and
  left:
    type: compare
    signal: Speed
    op: GT
    value: 50
  right:
    type: compare
    signal: Speed
    op: LT
    value: 180
'''

# Property 7: Implies - If speed > 100 then eventually speed > 150
IMPLIES_SPEED = '''type: always
formula:
  type: implies
  left:
    type: compare
    signal: Speed
    op: GT
    value: 100
  right:
    type: eventually
    formula:
      type: compare
      signal: Speed
      op: GT
      value: 150
'''

# Property 8: Changed By - Speed doesn't change by more than 150
ALWAYS_SPEED_CHANGE = '''type: always
formula:
  type: changed_by
  signal: Speed
  delta: 150
'''


# =============================================================================
# INTEGRATION TESTS
# =============================================================================

@pytest.fixture(autouse=True)
def check_binary():
    """Skip tests if binary not built"""
    try:
        binary = get_binary_path()
        if not binary.exists():
            pytest.skip("Binary not built yet")
    except FileNotFoundError:
        pytest.skip("Binary not found")


class TestAlwaysOperator:
    """Tests for the Always (G) operator"""

    def test_always_speed_lt_300_passes(self, decoder, increasing_speed_trace):
        """Always Speed < 300 should pass (max is 200)"""
        result = decoder.check_ltl(increasing_speed_trace, ALWAYS_SPEED_LT_300)
        assert result is True, "Speed never exceeds 300, should pass"

    def test_always_speed_lt_100_fails(self, decoder, increasing_speed_trace):
        """Always Speed < 100 should fail (speed reaches 200)"""
        property_yaml = '''type: always
formula:
  type: compare
  signal: Speed
  op: LT
  value: 100
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Speed exceeds 100, should fail"


class TestEventuallyOperator:
    """Tests for the Eventually (F) operator"""

    def test_eventually_speed_gt_100_passes(self, decoder, increasing_speed_trace):
        """Eventually Speed > 100 should pass (reaches 200)"""
        result = decoder.check_ltl(increasing_speed_trace, EVENTUALLY_SPEED_GT_100)
        assert result is True, "Speed reaches 200 > 100, should pass"

    def test_eventually_speed_gt_300_fails(self, decoder, increasing_speed_trace):
        """Eventually Speed > 300 should fail (max is 200)"""
        property_yaml = '''type: eventually
formula:
  type: compare
  signal: Speed
  op: GT
  value: 300
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Speed never exceeds 300, should fail"


class TestNeverOperator:
    """Tests for the Never (¬F) operator"""

    def test_never_speed_gt_250_passes(self, decoder, increasing_speed_trace):
        """Never Speed > 250 should pass (max is 200)"""
        result = decoder.check_ltl(increasing_speed_trace, NEVER_SPEED_GT_250)
        assert result is True, "Speed never exceeds 250, should pass"

    def test_never_speed_gt_100_fails(self, decoder, increasing_speed_trace):
        """Never Speed > 100 should fail (speed reaches 200)"""
        property_yaml = '''type: never
formula:
  type: compare
  signal: Speed
  op: GT
  value: 100
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Speed exceeds 100, should fail"


class TestBetweenPredicate:
    """Tests for the Between predicate"""

    def test_always_between_0_200_passes(self, decoder, increasing_speed_trace):
        """Always 0 <= Speed <= 200 should pass"""
        result = decoder.check_ltl(increasing_speed_trace, ALWAYS_SPEED_BETWEEN)
        assert result is True, "Speed stays in [0, 200], should pass"

    def test_always_between_50_150_fails(self, decoder, increasing_speed_trace):
        """Always 50 <= Speed <= 150 should fail (starts at 0, ends at 200)"""
        property_yaml = '''type: always
formula:
  type: between
  signal: Speed
  min: 50
  max: 150
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Speed goes outside [50, 150], should fail"


class TestLogicalOperators:
    """Tests for logical connectives (and, or, implies)"""

    def test_and_operator_passes(self, decoder, constant_speed_trace):
        """Speed > 100 AND Speed < 200 should pass for constant 150"""
        # Note: and() combines properties, so we use and(always(...), always(...))
        property_yaml = '''type: and
left:
  type: always
  formula:
    type: compare
    signal: Speed
    op: GT
    value: 100
right:
  type: always
  formula:
    type: compare
    signal: Speed
    op: LT
    value: 200
'''
        result = decoder.check_ltl(constant_speed_trace, property_yaml)
        assert result is True, "150 is in (100, 200), should pass"

    def test_or_operator_passes(self, decoder, increasing_speed_trace):
        """Speed < 50 OR Speed > 150 should pass (0 < 50 or 200 > 150)"""
        # Note: or() combines properties, so we use or(eventually(...), eventually(...))
        property_yaml = '''type: or
left:
  type: eventually
  formula:
    type: compare
    signal: Speed
    op: LT
    value: 50
right:
  type: eventually
  formula:
    type: compare
    signal: Speed
    op: GT
    value: 150
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is True, "Speed 0 < 50 at start, should pass"


class TestChangedByPredicate:
    """Tests for the ChangedBy predicate (rate of change)"""

    def test_changed_by_small_passes(self, decoder, increasing_speed_trace):
        """Change by <= 150 should pass (changes are 100)"""
        result = decoder.check_ltl(increasing_speed_trace, ALWAYS_SPEED_CHANGE)
        assert result is True, "Changes are 100 <= 150, should pass"

    def test_changed_by_large_fails(self, decoder, increasing_speed_trace):
        """Change by <= 50 should fail (changes are 100)"""
        property_yaml = '''type: always
formula:
  type: changed_by
  signal: Speed
  delta: 50
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Changes are 100 > 50, should fail"


class TestEqualsPredicate:
    """Tests for equality comparisons"""

    def test_eventually_equals_passes(self, decoder, constant_speed_trace):
        """Eventually Speed == 150 should pass"""
        result = decoder.check_ltl(constant_speed_trace, EVENTUALLY_SPEED_EQ_150)
        assert result is True, "Speed is constantly 150, should pass"

    def test_eventually_equals_fails(self, decoder, increasing_speed_trace):
        """Eventually Speed == 150 should fail (values are 0, 100, 200)"""
        result = decoder.check_ltl(increasing_speed_trace, EVENTUALLY_SPEED_EQ_150)
        assert result is False, "Speed never equals 150, should fail"


# =============================================================================
# TIME-BASED OPERATOR TESTS
# =============================================================================

class TestTimeBasedOperators:
    """Tests for time-bounded operators (EventuallyWithin, AlwaysWithin)

    Note: Timestamps are in microseconds. Test trace has timestamps at 0, 1000, 2000µs.
    """

    def test_eventually_within_passes(self, decoder, increasing_speed_trace):
        """EventuallyWithin 1500µs Speed > 50 should pass (100 at t=1000µs)"""
        property_yaml = '''type: eventually_within
time_ms: 1500
formula:
  type: compare
  signal: Speed
  op: GT
  value: 50
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is True, "Speed > 50 at t=1000µs, within 1500µs window"

    def test_eventually_within_fails(self, decoder, increasing_speed_trace):
        """EventuallyWithin 500µs Speed > 50 should fail (still 0 at t=0, 100 at t=1000µs)"""
        property_yaml = '''type: eventually_within
time_ms: 500
formula:
  type: compare
  signal: Speed
  op: GT
  value: 50
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Speed > 50 not reached within 500µs"

    def test_always_within_passes(self, decoder, increasing_speed_trace):
        """AlwaysWithin 1500µs Speed < 150 should pass (0 at t=0, 100 at t=1000µs)"""
        property_yaml = '''type: always_within
time_ms: 1500
formula:
  type: compare
  signal: Speed
  op: LT
  value: 150
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is True, "Speed stays < 150 within first 1500µs"

    def test_always_within_fails(self, decoder, increasing_speed_trace):
        """AlwaysWithin 2500µs Speed < 150 should fail (200 at t=2000µs)"""
        property_yaml = '''type: always_within
time_ms: 2500
formula:
  type: compare
  signal: Speed
  op: LT
  value: 150
'''
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Speed reaches 200 at t=2000µs, violates < 150"


# =============================================================================
# EDGE CASE TESTS
# =============================================================================

class TestEdgeCases:
    """Edge cases and boundary conditions"""

    def test_empty_trace(self, decoder):
        """Empty trace should handle gracefully"""
        with pytest.raises(RuntimeError):
            decoder.check_ltl([], ALWAYS_SPEED_LT_300)

    def test_single_frame_trace(self, decoder):
        """Single frame trace should work"""
        trace = [
            {'timestamp': 0, 'id': 0x100, 'dlc': 8,
             'data': [0xB8, 0x3A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]}
        ]
        result = decoder.check_ltl(trace, ALWAYS_SPEED_LT_300)
        assert result is True, "150 < 300, should pass"

    def test_invalid_signal_name(self, decoder, increasing_speed_trace):
        """Invalid signal name returns false (signal extraction fails)

        Note: Phase 2B should improve error reporting to raise an error
        with a helpful message about the missing signal.
        """
        property_yaml = '''type: always
formula:
  type: compare
  signal: NonExistentSignal
  op: LT
  value: 100
'''
        # Currently returns false when signal extraction fails
        # TODO: Phase 2B - raise error with helpful message about missing signal
        result = decoder.check_ltl(increasing_speed_trace, property_yaml)
        assert result is False, "Should return false for non-existent signal"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
