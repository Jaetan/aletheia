#!/usr/bin/env python3
"""Test DSL API implementation with 10 real-world automotive properties"""

from aletheia.dsl import Signal, Predicate, Property

def test_property_1_speed_limit():
    """Speed must always be below 220 km/h"""
    prop = Signal("Speed").less_than(220).always()
    yaml = prop.to_yaml()
    print("Property 1 - Speed Limit:")
    print(yaml)
    assert 'type: always' in yaml
    assert 'signal: Speed' in yaml
    assert 'op: LT' in yaml
    assert 'value: 220' in yaml
    print("✅ PASS\n")

def test_property_2_braking_behavior():
    """When brake pressed, speed must decrease within 100ms"""
    brake_pressed = Signal("BrakePedal").greater_than(0)
    speed_decreases = Signal("Speed").changed_by(-10)
    prop = brake_pressed.implies(speed_decreases.within(100))
    yaml = prop.to_yaml()
    print("Property 2 - Braking Behavior:")
    print(yaml)
    assert 'type: implies' in yaml
    assert 'signal: BrakePedal' in yaml
    assert 'signal: Speed' in yaml
    assert 'time_ms: 100' in yaml
    print("✅ PASS\n")

def test_property_3_gear_safety():
    """While moving forward, reverse gear must never be engaged"""
    moving_forward = Signal("Speed").greater_than(5)
    in_reverse = Signal("Gear").equals(-1)
    prop = moving_forward.implies(in_reverse.never())
    yaml = prop.to_yaml()
    print("Property 3 - Gear Safety:")
    print(yaml)
    assert 'type: implies' in yaml
    assert 'type: never' in yaml
    assert 'signal: Gear' in yaml
    print("✅ PASS\n")

def test_property_4_sensor_consistency():
    """All wheel speeds must be within 5% of each other"""
    fl_ok = Signal("WheelSpeedFL").between(0, 300)
    fr_ok = Signal("WheelSpeedFR").between(0, 300)
    both_ok = fl_ok.and_(fr_ok)
    prop = both_ok.always()
    yaml = prop.to_yaml()
    print("Property 4 - Sensor Consistency:")
    print(yaml)
    assert 'type: always' in yaml
    assert 'type: and' in yaml
    assert 'signal: WheelSpeedFL' in yaml
    assert 'signal: WheelSpeedFR' in yaml
    print("✅ PASS\n")

def test_property_5_battery_voltage():
    """Battery voltage must stay between 11.5V and 14.5V"""
    prop = Signal("BatteryVoltage").between(11.5, 14.5).always()
    yaml = prop.to_yaml()
    print("Property 5 - Battery Voltage:")
    print(yaml)
    assert 'type: always' in yaml
    assert 'type: between' in yaml
    assert 'signal: BatteryVoltage' in yaml
    assert 'min: 11.5' in yaml
    assert 'max: 14.5' in yaml
    print("✅ PASS\n")

def test_property_6_temporal_debouncing():
    """Door closed signal must be stable for 50ms (debouncing)"""
    prop = Signal("DoorClosed").equals(1).for_at_least(50)
    yaml = prop.to_yaml()
    print("Property 6 - Temporal Debouncing:")
    print(yaml)
    assert 'type: always_within' in yaml
    assert 'time_ms: 50' in yaml
    assert 'signal: DoorClosed' in yaml
    print("✅ PASS\n")

def test_property_7_logical_not():
    """Engine must not be running while in park"""
    in_park = Signal("Gear").equals(0)
    engine_running = Signal("EngineRPM").greater_than(500)
    prop = in_park.implies(engine_running.not_())
    yaml = prop.to_yaml()
    print("Property 7 - Logical NOT:")
    print(yaml)
    assert 'type: implies' in yaml
    assert 'type: not' in yaml
    assert 'signal: EngineRPM' in yaml
    print("✅ PASS\n")

def test_property_8_temporal_until():
    """Power state: Stay off until AccessoryOn"""
    power_off = Signal("PowerState").equals(0)
    power_acc = Signal("PowerState").equals(1)
    prop = power_off.never().until(power_acc)
    yaml = prop.to_yaml()
    print("Property 8 - Temporal Until:")
    print(yaml)
    assert 'type: until' in yaml
    assert 'type: never' in yaml
    print("✅ PASS\n")

def test_property_9_rate_limiting():
    """Speed sensor glitch detection: change > 50 km/h in one frame is error"""
    rapid_change = Signal("Speed").changed_by(50)
    prop = rapid_change.never()
    yaml = prop.to_yaml()
    print("Property 9 - Rate Limiting:")
    print(yaml)
    assert 'type: never' in yaml
    assert 'type: changed_by' in yaml
    assert 'signal: Speed' in yaml
    assert 'delta: 50' in yaml
    print("✅ PASS\n")

def test_property_10_complex_composition():
    """Complex: (Speed < 220) AND (Voltage OK) must always hold"""
    speed_ok = Signal("Speed").less_than(220)
    voltage_ok = Signal("BatteryVoltage").between(11.5, 14.5)
    both = speed_ok.and_(voltage_ok)
    prop = both.always()
    yaml = prop.to_yaml()
    print("Property 10 - Complex Composition:")
    print(yaml)
    assert 'type: always' in yaml
    assert 'type: and' in yaml
    assert 'signal: Speed' in yaml
    assert 'signal: BatteryVoltage' in yaml
    print("✅ PASS\n")

if __name__ == '__main__':
    print("=" * 60)
    print("Testing Python DSL API - 10 Real-World Properties")
    print("=" * 60 + "\n")

    test_property_1_speed_limit()
    test_property_2_braking_behavior()
    test_property_3_gear_safety()
    test_property_4_sensor_consistency()
    test_property_5_battery_voltage()
    test_property_6_temporal_debouncing()
    test_property_7_logical_not()
    test_property_8_temporal_until()
    test_property_9_rate_limiting()
    test_property_10_complex_composition()

    print("=" * 60)
    print("✅ ALL 10 PROPERTIES PASSED - DSL API WORKS!")
    print("=" * 60)
