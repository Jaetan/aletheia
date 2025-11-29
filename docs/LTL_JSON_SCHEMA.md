# LTL Property JSON Schema

This document defines the JSON schema for LTL properties sent from Python to Agda.

## Signal Predicates (Atomic)

Signal predicates are the atomic propositions evaluated on signal values.

### Equals
```json
{
  "predicate": "equals",
  "signal": "Speed",
  "value": {"num": 100, "denom": 1}
}
```
- `signal`: Signal name (string)
- `value`: Rational value as object with `num` (numerator) and `denom` (denominator)

### LessThan
```json
{
  "predicate": "lessThan",
  "signal": "Speed",
  "value": {"num": 8000, "denom": 1}
}
```

### GreaterThan
```json
{
  "predicate": "greaterThan",
  "signal": "RPM",
  "value": {"num": 0, "denom": 1}
}
```

### Between
```json
{
  "predicate": "between",
  "signal": "Temperature",
  "min": {"num": 60, "denom": 1},
  "max": {"num": 90, "denom": 1}
}
```
- `min`, `max`: Rational bounds as objects

### ChangedBy
```json
{
  "predicate": "changedBy",
  "signal": "Speed",
  "delta": {"num": 10, "denom": 1}
}
```
- `delta`: Maximum allowed change (rational object)

## LTL Temporal Operators

### Atomic (wraps a signal predicate)
```json
{
  "operator": "atomic",
  "predicate": {
    "predicate": "equals",
    "signal": "Speed",
    "value": "100/1"
  }
}
```

### Not
```json
{
  "operator": "not",
  "formula": {...}
}
```

### And
```json
{
  "operator": "and",
  "left": {...},
  "right": {...}
}
```

### Or
```json
{
  "operator": "or",
  "left": {...},
  "right": {...}
}
```

### Next
```json
{
  "operator": "next",
  "formula": {...}
}
```

### Always (globally)
```json
{
  "operator": "always",
  "formula": {...}
}
```

### Eventually (finally)
```json
{
  "operator": "eventually",
  "formula": {...}
}
```

### Until
```json
{
  "operator": "until",
  "left": {...},
  "right": {...}
}
```

### EventuallyWithin (bounded eventually)
```json
{
  "operator": "eventuallyWithin",
  "timebound": 1000,
  "formula": {...}
}
```
- `timebound`: Time in microseconds (integer)

### AlwaysWithin (bounded always)
```json
{
  "operator": "alwaysWithin",
  "timebound": 1000,
  "formula": {...}
}
```

## Complete Example

Speed must always be between 0 and 8000 RPM:

```json
{
  "operator": "always",
  "formula": {
    "operator": "atomic",
    "predicate": {
      "predicate": "between",
      "signal": "Speed",
      "min": {"num": 0, "denom": 1},
      "max": {"num": 8000, "denom": 1}
    }
  }
}
```

## Python DSL Example

The Python DSL would generate this JSON:

```python
# Python code
Signal("Speed").always().must_be_between(0, 8000)

# Generates this JSON:
{
  "operator": "always",
  "formula": {
    "operator": "atomic",
    "predicate": {
      "predicate": "between",
      "signal": "Speed",
      "min": {"num": 0, "denom": 1},
      "max": {"num": 8000, "denom": 1}
    }
  }
}
```

## Notes

1. **Rational values**: Encoded as JSON objects `{"num": numerator, "denom": denominator}`
   - Parsed directly in Agda using `_/_` operator
   - No string parsing needed - type-safe from JSON to ℚ
2. **Nested structure**: Formulas can be arbitrarily nested
3. **Type safety**: The schema ensures only valid LTL formulas can be constructed
4. **Python DSL responsibility**: The Python DSL validates and generates this JSON
5. **Agda responsibility**: Agda parses and validates the JSON, rejecting malformed properties
6. **Zero denominator**: Agda's `_/_` operator handles zero denominator safely
