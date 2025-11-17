# Phase 2A Design Document

**Date**: 2025-11-18
**Phase**: 2A - LTL Core + Real-World Support
**Timeline**: 5-7 weeks
**Status**: Design Phase

---

## Overview

Phase 2A extends Aletheia with Linear Temporal Logic (LTL) reasoning capabilities and real-world automotive support through extended CAN IDs and signal multiplexing.

**Goals**:
1. Enable temporal property verification on CAN traces
2. Support extended 29-bit CAN IDs (30-40% of automotive market)
3. Support signal multiplexing (5-10% of messages, critical for VIN/diagnostics)
4. Provide rich Python DSL for non-Agda users

**Success Criteria**:
- ✅ Check property on real trace: "Speed always < SpeedLimit"
- ✅ Handle multiplexed signal in real DBC
- ✅ Python DSL: Write 3 common properties without reading docs
- ✅ User feedback: "I can express what I need"

---

## Design Decisions

### Decision 1: Extended CAN ID Representation

**Chosen**: Sum type (Standard | Extended)

```agda
data CANId : Set where
  Standard : Fin 2048 → CANId          -- 11-bit standard IDs (0-2047)
  Extended : Fin 536870912 → CANId     -- 29-bit extended IDs (0-536870911)
```

**Rationale**:
- Type-safe: Compiler enforces correct handling of both ID types
- Explicit: No ambiguity about which ID type is used
- Self-documenting: Code clearly shows intent
- Matches DBC convention: DBC files use different syntax for extended IDs

**Impact**:
- `CAN/Frame.agda`: Update Frame record to use CANId sum type
- `DBC/Parser.agda`: Parse extended ID syntax (e.g., "id: 0x18FF1234 (extended)")
- `Protocol/Parser.agda`: Support extended IDs in command input
- Backward compatible: All existing code uses Standard variant

**Implementation Effort**: 1 day

**Testing**:
- Test with Hyundai/Kia DBC files (100% extended IDs)
- Test mixed DBC files (both standard and extended)
- Verify ParseDBC, ExtractSignal, InjectSignal work with both ID types

---

### Decision 2: Signal Multiplexing Model

**Chosen**: Dependent type with SignalPresence (Option B)

```agda
-- Signal presence model
data SignalPresence : Set where
  Always : SignalPresence
  When : (multiplexor : String) → (value : ℕ) → SignalPresence

-- Extended DBCSignal type
record DBCSignal : Set where
  field
    name : String
    signalDef : SignalDef
    byteOrder : ByteOrder
    unit : String
    presence : SignalPresence  -- NEW: Conditional presence
```

**Rationale**:
- **Type-safe**: Pattern matching on presence ensures correct handling
- **Expressive**: Can extend to complex conditions (e.g., multiple multiplexors)
- **Clean semantics**: Signal is either always present or conditionally present
- **Better for LTL**: Formulas can reason about signal availability
- **Future-proof**: Easy to extend (e.g., `WhenAny : List (String × ℕ) → SignalPresence`)

**Alternative Considered** (Maybe-based):
```agda
-- Rejected Option A
record MultiplexedSignal : Set where
  field
    signal : DBCSignal
    multiplexor : Maybe String
    multiplexValue : Maybe ℕ
```
- **Problem**: Doesn't enforce that multiplexor and value are both present/absent
- **Problem**: Runtime errors if multiplexor is Just but value is Nothing
- **Problem**: More verbose to check

**Impact**:
- `DBC/Types.agda`: Add SignalPresence type, update DBCSignal record
- `DBC/Parser.agda`: Parse multiplexing syntax from DBC YAML
- `DBC/Semantics.agda`: Signal extraction checks multiplexor value first
- `CAN/Encoding.agda`: extractSignal returns Maybe (handles absent signals)
- `LTL/Semantics.agda`: Atomic propositions handle signal absence

**DBC YAML Syntax**:
```yaml
signals:
  - name: "VIN_Part1"
    start_bit: 8
    bit_length: 8
    byte_order: "little_endian"
    value_type: "unsigned"
    factor: 1
    offset: 0
    minimum: 0
    maximum: 255
    unit: ""
    multiplexor: "VIN_Index"  # NEW: Name of multiplexor signal
    multiplex_value: 0         # NEW: Value that enables this signal

  - name: "VIN_Index"         # Multiplexor signal (no multiplex fields)
    start_bit: 0
    bit_length: 8
    # ... rest of fields
```

**Signal Extraction Logic**:
```agda
-- Pseudo-code
extractSignal : Frame → DBCMessage → String → Maybe SignalValue
extractSignal frame msg signalName with findSignal signalName msg
... | nothing = nothing
... | just sig with DBCSignal.presence sig
... | Always =
    -- Extract directly
    extractBits frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
... | When muxName muxValue =
    -- First extract multiplexor signal
    case findSignal muxName msg of λ where
      nothing → nothing  -- Multiplexor not found (malformed DBC)
      (just muxSig) →
        case extractBits frame (DBCSignal.signalDef muxSig) (DBCSignal.byteOrder muxSig) of λ where
          nothing → nothing  -- Multiplexor extraction failed
          (just muxVal) →
            if toℕ muxVal == muxValue
            then extractBits frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
            else nothing  -- Multiplexor value doesn't match
```

**Implementation Effort**: 2-3 days

**Testing**:
- Test with VW DBC files (21 multiplexed signals)
- Test with Tesla DBC files (25 multiplexed signals)
- Test VIN decoding (most common multiplexed use case)
- Verify extraction returns Nothing when multiplexor doesn't match

---

### Decision 3: LTL Formula Syntax

**Chosen**: Standard LTL with signal predicates as atoms

```agda
-- LTL formula type parameterized by atomic proposition type
data LTL (Atom : Set) : Set where
  -- Atomic propositions
  Atom : Atom → LTL Atom

  -- Boolean connectives
  ⊤ ⊥ : LTL Atom
  ¬_ : LTL Atom → LTL Atom
  _∧_ _∨_ _⇒_ : LTL Atom → LTL Atom → LTL Atom

  -- Temporal operators
  X_ : LTL Atom → LTL Atom                    -- Next
  F_ : LTL Atom → LTL Atom                    -- Eventually (Future)
  G_ : LTL Atom → LTL Atom                    -- Globally (Always)
  _U_ : LTL Atom → LTL Atom → LTL Atom        -- Until
  _R_ : LTL Atom → LTL Atom → LTL Atom        -- Release (dual of Until)

-- For CAN traces, atoms are signal predicates
data SignalPredicate : Set where
  -- Basic comparisons
  Equals : String → ℚ → SignalPredicate              -- Signal("Speed") == 100
  LessThan : String → ℚ → SignalPredicate            -- Signal("Speed") < 200
  GreaterThan : String → ℚ → SignalPredicate         -- Signal("Speed") > 0
  Between : String → ℚ → ℚ → SignalPredicate         -- Signal("Speed") in [0, 200]

  -- Presence checks
  Present : String → SignalPredicate                  -- Signal("VIN_Part1") exists
  Absent : String → SignalPredicate                   -- Signal("VIN_Part1") doesn't exist

  -- Future: Rate of change (Phase 2B)
  -- Rising : String → SignalPredicate                -- Signal increasing
  -- Falling : String → SignalPredicate               -- Signal decreasing
  -- ChangedBy : String → ℚ → SignalPredicate         -- Signal changed by delta
```

**Rationale**:
- **Standard semantics**: Well-understood, extensively studied
- **Complete**: G, F, X, U, R form a complete set of temporal operators
- **Expressive**: Can encode complex temporal properties
- **Verifiable**: Semantics are well-defined for finite traces

**Operator Semantics** (finite traces):
- `X φ`: φ holds in the next state (if it exists, otherwise vacuously true)
- `F φ`: φ holds eventually in the future (in some future state)
- `G φ`: φ holds globally (in all future states, including current)
- `φ U ψ`: φ holds until ψ becomes true (strong until)
- `φ R ψ`: ψ holds until φ becomes true, or ψ holds forever (release)

**Phase 2A Scope**: Implement G, F, X, U only. Defer R and complex predicates to Phase 2B.

**Implementation Effort**: 2-3 days (syntax + basic semantics)

---

### Decision 4: Trace Representation

**Chosen**: List of timestamped frames

```agda
-- Timestamp in microseconds (natural number for simplicity)
Timestamp : Set
Timestamp = ℕ

-- Timestamped CAN frame
record TimestampedFrame : Set where
  field
    timestamp : Timestamp
    frame : Frame

-- CAN trace (finite list of frames)
Trace : Set
Trace = List TimestampedFrame

-- Trace parser input format (YAML)
-- Example:
--   - timestamp: 1000000  # 1 second in microseconds
--     id: 0x100
--     data: [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
--   - timestamp: 1100000  # 1.1 seconds
--     id: 0x101
--     data: [0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]
```

**Rationale**:
- **Simple**: List type is well-understood, easy to work with
- **Sufficient**: Bounded checking on finite traces doesn't need coinduction
- **Timestamps**: Essential for temporal reasoning ("within 100ms")
- **Memory-bounded**: Entire trace loaded into memory (streaming in Phase 2B)

**Phase 2A Limitation**: Entire trace must fit in memory. Streaming deferred to Phase 2B.

**Implementation Effort**: 1 day (type + parser)

---

### Decision 5: LTL Semantics for Finite Traces

**Chosen**: Bounded semantics with explicit trace position

```agda
-- Trace satisfaction relation
-- "trace at position i satisfies formula φ"
_⊨_at_ : Trace → LTL SignalPredicate → ℕ → Bool

-- Atomic proposition evaluation
-- Returns true if signal predicate holds in frame at position i
evalAtom : Trace → SignalPredicate → ℕ → Bool

-- Full semantics (pseudo-code):
trace ⊨ Atom p at i = evalAtom trace p i
trace ⊨ ⊤ at i = true
trace ⊨ ⊥ at i = false
trace ⊨ (¬ φ) at i = not (trace ⊨ φ at i)
trace ⊨ (φ ∧ ψ) at i = (trace ⊨ φ at i) ∧ (trace ⊨ ψ at i)
trace ⊨ (φ ∨ ψ) at i = (trace ⊨ φ at i) ∨ (trace ⊨ ψ at i)
trace ⊨ (X φ) at i = if i+1 < length(trace) then (trace ⊨ φ at (i+1)) else true
trace ⊨ (F φ) at i = ∃ j ≥ i, trace ⊨ φ at j
trace ⊨ (G φ) at i = ∀ j ≥ i, trace ⊨ φ at j
trace ⊨ (φ U ψ) at i = ∃ j ≥ i, (trace ⊨ ψ at j) ∧ (∀ k ∈ [i,j), trace ⊨ φ at k)
```

**Boundary Conditions** (finite traces):
- `X φ` at end of trace: Vacuously true (no next state exists)
- `F φ`: Search only until end of trace (may be vacuously false)
- `G φ`: Check only until end of trace
- `φ U ψ`: ψ must occur before end of trace (strong until)

**Implementation Effort**: 3-4 days (semantics + model checker)

---

### Decision 6: Python DSL Syntax

**Chosen**: Fluent API with Signal class

```python
from aletheia.ltl import Signal, always, eventually, next_state, until

# Basic predicates (returns SignalPredicate objects)
speed_positive = Signal("Speed").greater_than(0)
speed_ok = Signal("Speed").between(0, 200)
speed_exact = Signal("Speed").equals(100)

# Temporal operators (returns LTL formula objects)
always_positive = always(speed_positive)           # G (Speed > 0)
eventually_zero = eventually(speed_exact)          # F (Speed == 100)
speed_increases = next_state(speed_ok)             # X (Speed in [0,200])

# Composition
safe_speed = always(Signal("Speed").less_than(Signal("SpeedLimit")))

# Conditional (when/then sugar for implication)
from aletheia.ltl import when

braking_safe = when(
    Signal("BrakePressed").equals(1)
).then(
    Signal("Speed").decreasing()  # Phase 2B: rate predicates
)
# Desugars to: G (BrakePressed == 1 ⇒ X (Speed < Speed_prev))

# Complex example
vin_decoding = always(
    when(Signal("VIN_Index").equals(0)).then(
        Signal("VIN_Part1").present()
    )
)
# G (VIN_Index == 0 ⇒ Present("VIN_Part1"))
```

**Signal Class API**:
```python
class Signal:
    def __init__(self, name: str):
        self.name = name

    # Comparisons
    def equals(self, value: float) -> SignalPredicate: ...
    def less_than(self, value: float) -> SignalPredicate: ...
    def greater_than(self, value: float) -> SignalPredicate: ...
    def between(self, min_val: float, max_val: float) -> SignalPredicate: ...

    # Presence
    def present(self) -> SignalPredicate: ...
    def absent(self) -> SignalPredicate: ...

    # Phase 2B: Rate predicates
    # def increasing(self) -> SignalPredicate: ...
    # def decreasing(self) -> SignalPredicate: ...
    # def changed_by(self, delta: float) -> SignalPredicate: ...

# Temporal operators
def always(formula: LTLFormula) -> LTLFormula: ...
def eventually(formula: LTLFormula) -> LTLFormula: ...
def next_state(formula: LTLFormula) -> LTLFormula: ...
def until(phi: LTLFormula, psi: LTLFormula) -> LTLFormula: ...

# Composition helpers
def when(condition: SignalPredicate) -> WhenBuilder: ...
class WhenBuilder:
    def then(self, consequence: LTLFormula) -> LTLFormula: ...
```

**Serialization to YAML**:
```python
# Python objects serialize to YAML, sent to Agda
formula = always(Signal("Speed").between(0, 200))

# Serializes to:
# formula:
#   type: "Globally"
#   inner:
#     type: "Atom"
#     predicate:
#       type: "Between"
#       signal: "Speed"
#       min: 0
#       max: 200
```

**Implementation Effort**: 2 weeks (Python API + YAML serialization + Agda parser)

---

## Module Structure

### New Modules for Phase 2A

```
src/Aletheia/
├── CAN/
│   └── Frame.agda              [MODIFIED] Add CANId sum type
│
├── DBC/
│   ├── Types.agda              [MODIFIED] Add SignalPresence, update DBCSignal
│   ├── Parser.agda             [MODIFIED] Parse multiplexing syntax
│   └── Semantics.agda          [MODIFIED] Implement decodeFrame with multiplexing
│
├── LTL/                        [NEW]
│   ├── Syntax.agda             [NEW] LTL formula type, SignalPredicate
│   ├── Semantics.agda          [NEW] Trace satisfaction relation (⊨)
│   ├── Checker.agda            [NEW] Model checking algorithm
│   └── DSL/                    [NEW]
│       ├── Syntax.agda         [NEW] Python DSL AST types
│       ├── Parser.agda         [NEW] Parse YAML → Python DSL AST
│       └── Translate.agda      [NEW] Translate DSL → LTL
│
├── Trace/                      [NEW]
│   ├── Types.agda              [NEW] TimestampedFrame, Trace
│   ├── Parser.agda             [NEW] Parse YAML trace files
│   └── Properties.agda         [NEW] Trace well-formedness (Phase 3)
│
└── Protocol/
    ├── Command.agda            [MODIFIED] Add CheckProperty command
    ├── Parser.agda             [MODIFIED] Parse CheckProperty from YAML
    ├── Response.agda           [MODIFIED] Add PropertyResult response
    └── Handlers.agda           [MODIFIED] Implement handleCheckProperty
```

### Python Modules

```
python/aletheia/
├── __init__.py
├── decoder.py                  [EXISTING] CANDecoder class
├── ltl.py                      [NEW] Signal class, temporal operators
├── dsl.py                      [NEW] DSL serialization to YAML
└── checker.py                  [NEW] PropertyChecker class (subprocess wrapper)
```

---

## Implementation Plan

### Week 1: Foundations (Extended IDs + Multiplexing)

**Day 1-2: Extended CAN IDs**
- [ ] Update `CAN/Frame.agda`: Add CANId sum type
- [ ] Update `DBC/Parser.agda`: Parse extended ID syntax
- [ ] Update `Protocol/Parser.agda`: Support extended IDs in commands
- [ ] Test with Hyundai/Kia DBC files

**Day 3-5: Signal Multiplexing**
- [ ] Add `SignalPresence` to `DBC/Types.agda`
- [ ] Update `DBCSignal` record with presence field
- [ ] Update `DBC/Parser.agda`: Parse multiplexor/multiplex_value
- [ ] Update `CAN/Encoding.agda`: extractSignal checks multiplexor
- [ ] Test with VW/Tesla DBC files (multiplexed signals)

**Deliverable**: Extended IDs and multiplexing working end-to-end

---

### Week 2-3: LTL Core

**Week 2: Syntax and Semantics**
- [ ] Implement `LTL/Syntax.agda`: LTL formula type
- [ ] Implement `SignalPredicate` type (Equals, LessThan, Between, etc.)
- [ ] Implement `Trace/Types.agda`: TimestampedFrame, Trace
- [ ] Implement `LTL/Semantics.agda`: _⊨_at_ relation
- [ ] Implement `evalAtom`: Evaluate predicates on frames

**Week 3: Model Checker**
- [ ] Implement `LTL/Checker.agda`: Model checking algorithm
- [ ] Implement check for each operator (G, F, X, U)
- [ ] Add trace parser `Trace/Parser.agda`
- [ ] Unit tests: Check simple properties on hand-crafted traces

**Deliverable**: LTL model checker working in Agda

---

### Week 4-5: Python DSL

**Week 4: Python API**
- [ ] Implement `Signal` class in `python/aletheia/ltl.py`
- [ ] Implement predicates: equals, less_than, greater_than, between
- [ ] Implement temporal operators: always, eventually, next_state, until
- [ ] Implement when/then composition helper
- [ ] Unit tests: Check DSL constructs serialize correctly

**Week 5: Integration**
- [ ] Implement YAML serialization for DSL objects
- [ ] Implement `LTL/DSL/Parser.agda`: Parse DSL YAML → LTL
- [ ] Implement `LTL/DSL/Translate.agda`: Translate DSL → core LTL
- [ ] Add `CheckProperty` command to protocol
- [ ] Implement `handleCheckProperty` in handlers
- [ ] Python integration tests: End-to-end property checking

**Deliverable**: Python DSL working end-to-end

---

### Week 6: Testing & Validation

**Testing with Real Data**
- [ ] Download OpenDBC repository
- [ ] Select 3 test DBC files:
  - Hyundai/Kia (extended IDs)
  - VW/Tesla (multiplexing)
  - Toyota/Honda (standard CAN)
- [ ] Create test traces for each DBC file
- [ ] Write example properties:
  - "Speed always < SpeedLimit"
  - "When braking, speed decreases"
  - "VIN decoding works (multiplexed)"

**Performance Testing**
- [ ] Benchmark model checking on 1000-frame trace
- [ ] Benchmark model checking on 10,000-frame trace
- [ ] Identify bottlenecks (if any)

**Deliverable**: Validated against real automotive data

---

### Week 7: Buffer & Documentation

**Polish**
- [ ] Address any issues found in testing
- [ ] Improve error messages
- [ ] Add type signatures and documentation

**Documentation**
- [ ] Update `DESIGN.md` with Phase 2A status
- [ ] Update `CLAUDE.md` with Phase 2A features
- [ ] Create user guide for Python DSL
- [ ] Create example gallery (3 examples)

**Deliverable**: Ready for Phase 2B

---

## Testing Strategy

### Unit Tests (Agda)

**LTL Syntax**
- Parse and pretty-print formulas
- Test operator precedence

**LTL Semantics**
- Test each operator on simple traces
- Test boundary conditions (end of trace)
- Test nested operators

**Signal Extraction with Multiplexing**
- Extract always-present signal (should succeed)
- Extract multiplexed signal with matching multiplexor (should succeed)
- Extract multiplexed signal with non-matching multiplexor (should fail)

### Integration Tests (Python)

**Extended CAN IDs**
- Parse DBC with extended IDs
- Extract signal from extended ID frame
- Verify correct ID matching

**Multiplexing**
- Parse DBC with multiplexed signals
- Extract VIN parts (multiplexed on VIN_Index)
- Verify correct conditional extraction

**LTL Checking**
- Check "always(Speed < 200)" on valid trace (should pass)
- Check "always(Speed < 100)" on trace with Speed=150 (should fail)
- Check "eventually(Speed == 0)" on trace ending at 0 (should pass)

### Real-World Validation

**Test Data Sources**
- OpenDBC repository: https://github.com/commaai/opendbc
- DBC files: Honda Civic, Toyota RAV4, Hyundai Sonata
- Generate synthetic traces based on signal definitions

**Example Properties**
1. **Speed limit**: `always(Signal("Speed").less_than(200))`
2. **Braking**: `always(when(Signal("BrakePressed").equals(1)).then(...))`
3. **VIN decoding**: `always(when(Signal("VIN_Index").equals(0)).then(Signal("VIN_Part1").present()))`

---

## Risk Assessment

### Risk 1: Multiplexing More Complex Than Expected
- **Probability**: Medium
- **Impact**: High (blocks real traces)
- **Mitigation**: Start with simple dependent type, prototype early
- **Contingency**: Simplify to Maybe-based approach if dependent types cause issues

### Risk 2: LTL Semantics on Finite Traces
- **Probability**: Low
- **Impact**: Medium (may need to revise semantics)
- **Mitigation**: Follow standard finite-trace LTL semantics from literature
- **Contingency**: Consult formal methods papers if ambiguity arises

### Risk 3: Python DSL Too Verbose
- **Probability**: Medium
- **Impact**: Medium (poor UX)
- **Mitigation**: User testing with 3 example properties
- **Contingency**: Simplify DSL, add more sugar/helpers

### Risk 4: Performance on Large Traces
- **Probability**: Medium
- **Impact**: Low (streaming in Phase 2B)
- **Mitigation**: Benchmark early, defer optimization to Phase 2B/3
- **Contingency**: Document performance limits, require trace chunking

---

## Success Criteria (Detailed)

Phase 2A is complete when:

**Functional Requirements**
- ✅ Extended CAN IDs: Can parse and process extended 29-bit IDs
- ✅ Multiplexing: Can extract multiplexed signals conditionally
- ✅ LTL Core: Can check G, F, X, U properties on traces
- ✅ Python DSL: Can express properties fluently in Python

**Testing Requirements**
- ✅ Unit tests pass for all LTL operators
- ✅ Integration tests pass for all DBC features
- ✅ Real trace validation passes (3 DBC files, 3 properties)

**Performance Requirements**
- ✅ Check simple property on 1000-frame trace in <1 second
- ✅ Check complex property on 10,000-frame trace in <10 seconds

**Usability Requirements**
- ✅ User can write "Speed always < SpeedLimit" without reading docs
- ✅ User can handle multiplexed signals without understanding internals
- ✅ Error messages explain what went wrong

---

## Next Steps

1. ✅ Review and approve this design document
2. ⏭️ Implement extended CAN ID support
3. ⏭️ Implement signal multiplexing
4. ⏭️ Implement LTL syntax and semantics
5. ⏭️ Implement Python DSL
6. ⏭️ Test with real automotive data

---

**Document Status**: Ready for implementation
**Approved By**: [To be filled]
**Implementation Start Date**: 2025-11-18
