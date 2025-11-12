# Development Plan Review and Revision

**Date**: 2025-11-12
**Purpose**: Align development plan with real-world automotive CAN data processing and LTL reasoning

---

## GOAL VALIDATION

### Stated Goals
1. **Process real-world automotive CAN data**
2. **Reason/check temporal properties with LTL**
3. **Python DSL rich enough for non-Agda users**
4. **Extensible architecture for unknown future requirements**
5. **Support as many real-world situations as possible**

### Reality Check

**✅ ACHIEVABLE:**
- Standard CAN frame processing (dominant in automotive)
- Signal extraction with scaling/offset
- Basic LTL temporal reasoning
- Python API wrapping verified Agda core
- DBC file parsing

**⚠️ CHALLENGING BUT DOABLE:**
- Signal multiplexing support (~30% of automotive messages)
- Streaming trace analysis (large files)
- Rich Python DSL with extensibility
- Performance on production-size traces

**❌ NOT REALISTIC FOR MVP:**
- CAN-FD support (limited automotive adoption, complex)
- Full J1939 protocol support (different domain)
- Real-time analysis (Agda → Haskell overhead)
- GUI/visualization tools
- Automatic property inference from traces

**🔴 CRITICAL GAPS IN CURRENT PLAN:**
1. **Multiplexing is essential but currently deferred to Phase 5**
2. **Python DSL design not specified**
3. **No streaming/performance considerations**
4. **No validation against real traces**
5. **No incremental delivery strategy**
6. **No user feedback loop**

---

## CURRENT PLAN CRITIQUE

### Phase 1: Core Infrastructure (~85% complete)
**Status**: ✅ On track, but missing critical rational parser fix

**What's Good**:
- Strong foundation (parser combinators, encoding/decoding)
- Type-safe with --safe flag
- Build pipeline working

**What's Missing**:
- ❌ No real-world validation (testing with synthetic data only)
- ❌ No performance benchmarks
- ❌ Rational parser still broken (blocks everything)

**Recommendation**:
- Complete critical fixes (#1-4)
- **ADD**: Test with real DBC file from automotive (e.g., OpenDBC)
- **ADD**: Benchmark signal extraction performance

---

### Phase 2: LTL Foundation (Planned, Not Started)
**Current Plan**:
- LTL syntax and semantics
- Coinductive trace streams
- Basic model checker
- Temporal property verification

**CRITICAL FLAWS**:
1. **❌ No mention of signal multiplexing** - will break on real traces
2. **❌ Assumes all signals always present** - unrealistic
3. **❌ No streaming design** - will fail on large traces
4. **❌ No Python DSL design** - users can't use it
5. **❌ No bounded checking** - unbounded traces impractical

**What Real-World Automotive Needs**:
- **Bounded LTL**: "Within next 100ms, signal X must satisfy Y"
- **Conditional signals**: "If multiplexor=1, THEN signal A exists"
- **Streaming**: Process trace incrementally (can't load 1GB trace into memory)
- **Rich predicates**: "Signal rising edge", "Signal changed by >10%", etc.
- **Composition**: Build complex properties from simple ones

**Recommendation**: **MAJOR REDESIGN NEEDED**
- Split into Phase 2A (Core LTL) and Phase 2B (Extensions)
- Add multiplexing support in Phase 2A
- Add streaming in Phase 2B
- Design Python DSL early (not as afterthought)

---

### Phase 3: Temporal Bounds and Streaming (Planned)
**Current Plan**:
- Bounded LTL checking
- Streaming verification
- Grammar formalization for parsers
- Parser soundness proofs

**Issues**:
- Streaming should be in Phase 2, not Phase 3 (critical for real traces)
- Parser proofs are academic, not user-facing
- No mention of performance optimization

**Recommendation**:
- **Move streaming to Phase 2B**
- Keep parser proofs in Phase 3 (verification phase)
- Add performance profiling to Phase 3

---

### Phase 4: Robustness Improvements (Planned)
**Current Plan**:
- Comprehensive logging
- Counterexample generation
- Error recovery and reporting
- Performance profiling

**Assessment**: ✅ Good, but generic
- Counterexample generation is CRITICAL for LTL (shows violation trace)
- Should be in Phase 2B, not Phase 4

**Recommendation**:
- **Move counterexample generation to Phase 2B**
- Add user documentation to Phase 4
- Add example library to Phase 4

---

### Phase 5: Optimization and Feature Extensions (Planned)
**Current Plan**:
- Additional encoding/decoding tests
- Enhanced DBC validation
- Pretty-printer
- Round-trip properties
- Performance optimizations
- Extended features (CAN-FD, multiplexing, value tables)

**CRITICAL ERROR**:
- **Multiplexing is in Phase 5 but needed in Phase 2** for real traces
- CAN-FD is nice-to-have, not critical

**Recommendation**:
- **Remove multiplexing from Phase 5** (move to Phase 2A)
- Keep CAN-FD as optional extension
- Add "Production Hardening" tasks (error messages, edge cases)

---

## USER EXPERIENCE ANALYSIS

### Current User Journey (Planned)
1. User writes Python code
2. Calls `CANDecoder` class (subprocess to binary)
3. Binary returns results

**Problems**:
- ❌ No DSL for LTL properties (users must learn LTL syntax)
- ❌ No composition (can't build complex properties from simple ones)
- ❌ No standard library of common checks
- ❌ No debugging when property fails (no counterexample visualization)
- ❌ No incremental development (all-or-nothing)

### Desired User Journey
1. User imports aletheia library
2. Uses rich Python DSL: `Signal("EngineSpeed").within(100*ms).must_be_between(0, 8000)`
3. Composes properties: `when(GearShift).then(EngineSpeed.stable_for(50*ms))`
4. Gets clear counterexample: "Property failed at timestamp 1.234s, EngineSpeed was 9000"
5. Can validate incrementally (signal extraction works before LTL)

### DSL Extensibility Requirements

**Must Support**:
```python
# Basic predicates
Signal("Speed").equals(0)
Signal("Speed").between(min, max)
Signal("Speed").changed_by(delta)

# Temporal operators
Signal("Speed").always(predicate)
Signal("Speed").eventually(predicate)
Signal("Speed").within(timeout, predicate)

# Composition
when(Event("BrakePressed")).then(Signal("Speed").decreasing())
when(Signal("Gear").equals(0)).then(Signal("Speed").stable())

# Custom predicates (extensibility!)
def my_safety_check(trace):
    # User-defined logic in Python
    return Signal("Speed") < Signal("SpeedLimit")

Property(my_safety_check).must_hold()
```

**This requires**:
- Embedded DSL (Python objects representing LTL AST)
- Serialization to Agda-compatible format
- Agda type for user-defined predicates
- Clear semantics for composition

**Current plan has NONE of this designed!**

---

## REVISED PHASE PLAN

### **Phase 1: Core Infrastructure** (Current, ~85% complete)

**Goals**: Working signal extraction for standard CAN

**Critical Fixes** (blocking):
1. ✅ Fix rational parser (0.25 → 1/4)
2. ✅ Fix removeScaling (implement division)
3. ✅ Implement response formatting (ℚ, Vec Byte 8)
4. ✅ Implement byte array parser
5. ✅ Complete protocol parser (all 4 commands)
6. ✅ Python wrapper (basic)
7. ✅ Integration tests

**Testing** (REQUIRED before Phase 1 completion):
8. ✅ **Unit tests for all critical fixes**
   - Rational parser: Test "0.25" → 1/4, "1.5" → 3/2, negative decimals
   - Signal scaling: Test round-trip (applyScaling ∘ removeScaling ≈ id)
   - Response formatting: Test ℚ and Vec Byte 8 output formats
   - Byte array parser: Test hex parsing, case sensitivity, bounds
9. ✅ **Integration tests**
   - End-to-end: Python → binary → Python for all 4 commands
   - Real DBC file from OpenDBC (Toyota, Honda, etc.)
   - Fractional scaling factors (0.25, 1.5, 2.5, etc.)
10. ✅ Benchmark signal extraction performance (target: <1ms per signal)

**Architectural Review** (MANDATORY before Phase 2):
11. ✅ **Comprehensive constraint evaluation** (allocate 1-2 days, not 0.5!)
    - Survey: CAN-FD requirements (8-byte vs 64-byte frames)
    - Survey: Extended 29-bit CAN IDs (vs standard 11-bit)
    - Survey: Signal multiplexing prevalence (~30% of automotive messages)
    - **Decision point**: Refactor Frame type NOW (2-3 days) vs LATER (1-2 weeks)
    - Document decision rationale with cost/benefit analysis
    - **Risk**: Building Phase 2 (LTL) on Phase 1 assumptions locks us in!

**Deliverable**: Users can extract signals from standard CAN frames using Python

**Timeline**: 3-4 weeks (including critical fixes, testing, and architectural review)

---

### **Phase 2A: LTL Core + Real-World Support** (Redesigned)

**Goals**: LTL reasoning on real automotive traces

**Core LTL**:
1. ✅ LTL syntax (Always, Eventually, Until, etc.)
2. ✅ Semantics for finite traces (bounded checking)
3. ✅ Basic model checker
4. ✅ Signal multiplexing support (MOVED FROM PHASE 5)
   - Conditional signal presence
   - `Signal (Maybe ℚ)` types OR dependent types
   - Extraction checks multiplexor first

**Python DSL v1** (CRITICAL, not in original plan):
5. ✅ DSL design document
6. ✅ Basic predicates (equals, between, changed)
7. ✅ Temporal operators (always, eventually, within)
8. ✅ Composition (when/then, and/or)
9. ✅ Parser: Python DSL → Agda LTL AST
10. ✅ Serialization/deserialization

**Validation**:
11. ✅ Test with real CAN trace (automotive)
12. ✅ Example: "Speed < SpeedLimit" property
13. ✅ Example: "When braking, speed decreases"

**Deliverable**: Users can check LTL properties on real traces using Python DSL

**Timeline**: 4-6 weeks

**Risk**: Multiplexing might take longer than expected

---

### **Phase 2B: Streaming + Counterexamples** (Redesigned)

**Goals**: Handle large traces, debug failures

**Streaming**:
1. ✅ Streaming trace parser (don't load entire trace)
2. ✅ Incremental LTL checking
3. ✅ Memory-bounded operation

**Counterexamples** (MOVED FROM PHASE 4):
4. ✅ Counterexample generation (show violating trace)
5. ✅ Minimal counterexample (shrink trace)
6. ✅ Python-friendly format (timestamp, signal values)

**DSL Extensions**:
7. ✅ Custom user-defined predicates
8. ✅ Standard library of common checks
9. ✅ Composition helpers

**Deliverable**: Production-ready LTL checking with good UX

**Timeline**: 3-4 weeks

---

### **Phase 3: Verification + Performance** (Revised)

**Goals**: Prove correctness, optimize bottlenecks

**Proofs**:
1. ✅ Replace all postulates with proofs
2. ✅ **Prove unreachable cases are impossible** (replace coverage patterns with proofs)
   - Prove `power10 n` always returns `suc k` (never zero)
   - Prove valid hex characters always parse successfully
   - Prove well-formed DBC files have nonzero factors
3. ✅ Parser soundness (grammar formalization)
4. ✅ LTL semantics correctness
5. ✅ Round-trip properties (parse ∘ print ≡ id)

**Performance** (EXPLICIT profiling requirements):
6. ✅ **Profile entire pipeline systematically**
   - Rational number operations (normalization, arithmetic)
   - String conversions (ℚ → String, Vec Byte 8 → String)
   - Parser performance on large DBC files (100+ messages)
   - Signal extraction throughput (target: <1ms per signal)
   - Memory usage patterns
7. ✅ Identify and optimize hot paths based on profiling data
8. ✅ Benchmark against target: 1M frames/sec signal extraction

**Deliverable**: Fully verified, production-performance system

**Timeline**: 4-6 weeks

---

### **Phase 4: Production Hardening** (Revised)

**Goals**: Polish for real users

**UX**:
1. ✅ **Comprehensive error messages with context**
   - Parser errors: Show line/column position and expected input
   - Validation errors: Explain what constraint was violated
   - Runtime errors: Provide actionable guidance
2. ✅ **Decimal approximations for user-facing output** (internal stays rational)
   - Display format: "3/2 (≈ 1.5)" for signal values
   - Configuration option to show fractions-only or decimals-only
   - Maintains exact rational arithmetic internally
3. ✅ User documentation (tutorials, examples)
4. ✅ Standard library of checks (common properties)
5. ✅ Example gallery (real-world use cases)

**Robustness**:
6. ✅ Edge case handling
7. ✅ Graceful degradation
8. ✅ Logging and debugging support
9. ✅ Integration with common tools (pandas, etc.)

**Deliverable**: User-friendly, production-ready tool

**Timeline**: 3-4 weeks

---

### **Phase 5: Optional Extensions** (Revised)

**Goals**: Nice-to-have features, not critical

**Extensions** (prioritized):
1. 🟢 Value tables/enumerations (medium value, low cost)
2. 🟡 Extended CAN IDs (low value for automotive, medium cost)
3. 🔴 CAN-FD support (low value for now, high cost)
4. 🟢 Pretty-printer for DBC (medium value, low cost)
5. 🟢 Additional DBC validation (medium value, low cost)

**Deliverable**: Enhanced feature set based on user feedback

**Timeline**: Ongoing, based on demand

---

## CRITICAL DECISION POINTS

### Decision Point 1: End of Phase 1
**When**: Before starting Phase 2A
**Questions**:
1. ✅ Has rational parser been fixed and validated?
2. ✅ Have we tested with a real DBC file?
3. ✅ Is performance acceptable for single-frame extraction?
4. ✅ Do we have user feedback on Python API?

**Decision**: Proceed to Phase 2A OR iterate on Phase 1

---

### Decision Point 2: End of Phase 2A
**When**: Before starting Phase 2B
**Questions**:
1. ✅ Does multiplexing support work on real traces?
2. ✅ Can users express common properties in Python DSL?
3. ✅ Is LTL checking correct (validated with known properties)?
4. ✅ Do we have early user feedback?

**Decision**:
- If YES: Proceed to Phase 2B
- If NO: **PIVOT** - identify what's not working and fix
  - Possible pivots:
    - Simplify DSL (remove composition)
    - Defer multiplexing (if traces don't need it)
    - Change LTL semantics (if current approach doesn't scale)

---

### Decision Point 3: Mid-Phase 2B
**When**: After streaming implemented
**Questions**:
1. ✅ Can we handle 1GB trace files?
2. ✅ Is memory usage bounded?
3. ✅ Is performance acceptable (target: <1 minute for 1M frames)?

**Decision**:
- If YES: Continue to counterexamples
- If NO: **SIMPLIFY** - what can we drop?
  - Drop streaming, require pre-processed traces?
  - Drop complex LTL, support only basic properties?
  - Drop full verification, use heuristics?

---

### Decision Point 4: End of Phase 3
**When**: After proofs completed
**Questions**:
1. ✅ Are all critical properties proven?
2. ✅ Is performance meeting targets?
3. ✅ Do we have beta users?

**Decision**:
- If YES: Proceed to Phase 4 (production hardening)
- If NO: **DESCOPE** - what proofs can we defer?
  - Keep critical properties (LTL semantics)
  - Defer nice-to-have proofs (pretty-printer)

---

## REALISM ASSESSMENT

### What We Can Definitely Achieve

✅ **High Confidence**:
1. Signal extraction from standard CAN frames
2. DBC file parsing with multiplexing
3. Basic LTL checking (Always, Eventually)
4. Python API with subprocess interface
5. Formal verification of core algorithms

**Rationale**: These are well-understood, have clear specifications, and are mostly implemented

---

### What We Can Probably Achieve

⚠️ **Medium Confidence**:
1. Rich Python DSL with composition
2. Streaming trace analysis
3. Counterexample generation
4. Performance on large traces (1M+ frames)
5. User-friendly error messages

**Rationale**: These are more complex, require iteration, but are in scope
**Risk**: May need to simplify DSL or drop some features

---

### What's Uncertain

❓ **Low Confidence**:
1. Custom user-defined predicates (requires careful design)
2. Integration with other tools (pandas, visualization)
3. Real-time or near-real-time analysis
4. Handling all edge cases in real DBC files

**Rationale**: Depends on user requirements we don't fully know yet
**Mitigation**: User studies, early feedback, iterative development

---

### What We Should Drop

❌ **Out of Scope** (at least for initial release):
1. CAN-FD support (can add later if needed)
2. Extended 29-bit CAN IDs (unless user testing shows need)
3. J1939 protocol support (different domain)
4. GUI/visualization (use existing tools)
5. Automatic property inference (research problem)
6. Real-time analysis (architectural limitation)

**Rationale**: These don't contribute to core goal (LTL on CAN traces)
**Exception**: If user testing reveals critical need, revisit

---

## EXTENSIBILITY STRATEGY

### Problem
Users need to define checks we haven't thought of
Can't predict all future requirements
Can't bloat DSL with every possible predicate

### Solution: Three-Tier Extensibility

**Tier 1: Built-in Predicates** (Fast, type-safe)
```python
Signal("Speed").between(0, 100)  # Implemented in Agda
Signal("Temp").rising_edge()      # Implemented in Agda
```
- Verified in Agda
- Fast execution
- Limited to what we anticipate

**Tier 2: Python-Defined Predicates** (Flexible, runtime-checked)
```python
@aletheia.predicate
def speed_reasonable(trace, signal):
    # User writes Python logic
    return signal < 200 and signal >= 0

Signal("Speed").satisfies(speed_reasonable)
```
- User extensibility
- Serialized to Agda as "opaque predicate"
- Agda evaluates via FFI callback to Python
- Slower but flexible

**Tier 3: Agda Extensions** (Expert mode)
```agda
-- User can add Agda modules
speedReasonable : SignalValue → Bool
speedReasonable v = (v <ℚ 200ℚ) ∧ (v ≥ℚ 0ℚ)
```
- Full verification
- Requires Agda knowledge
- For power users / researchers

### Implementation Plan

**Phase 2A**: Tier 1 only (built-in predicates)
**Phase 2B**: Add Tier 2 (Python callbacks)
**Phase 4**: Document Tier 3 (optional)

**This gives extensibility without committing to everything upfront**

---

## TRACKING DROPPED FEATURES

### Dropped Features Log

| Feature | Reason Dropped | Reconsidered If | Decision Date |
|---------|----------------|-----------------|---------------|
| CAN-FD | Limited automotive use, high complexity | User survey shows >20% need | End of Phase 1 |
| Extended IDs | Most automotive uses 11-bit | Test DBCs show usage | End of Phase 1 |
| Value tables | Nice-to-have, not blocking | User requests | Phase 5 |
| Real-time | Architectural limitation (Agda overhead) | Never (use C++ instead) | Now |
| Auto-infer properties | Research problem, not tool feature | Never (separate tool) | Now |

**Review Schedule**: End of each phase, ask "Should we reconsider any dropped features?"

---

## VALIDATION STRATEGY

### How to Know If We're On Track

**Phase 1 Success Criteria**:
- ✅ Extract signal from real DBC file
- ✅ Python test passes: `decoder.extract_signal("EngineSpeed", frame) == 1500.0`
- ✅ Performance: <1ms per signal extraction
- ✅ User (even if just us) can use Python API without reading Agda

**Phase 2A Success Criteria**:
- ✅ Check property on real trace: "Speed always < SpeedLimit"
- ✅ Handle multiplexed signal in real DBC
- ✅ Python DSL: Write 3 common properties without reading docs
- ✅ User feedback: "I can express what I need"

**Phase 2B Success Criteria**:
- ✅ Process 1M frame trace in <1 minute
- ✅ Memory usage <1GB for any size trace
- ✅ Counterexample: Shows exactly where/why property failed
- ✅ User feedback: "I can debug failures easily"

**Phase 3 Success Criteria**:
- ✅ All critical proofs complete
- ✅ Performance: 1M frames/sec
- ✅ No postulates in --safe modules
- ✅ User feedback: "It's fast enough"

**Phase 4 Success Criteria**:
- ✅ Error messages: User can fix without asking us
- ✅ Documentation: New user productive in <1 hour
- ✅ Examples: Cover 80% of use cases
- ✅ User feedback: "I would use this in production"

---

## RISK MITIGATION

### Top Risks

**Risk 1: Multiplexing support takes too long**
- Probability: Medium
- Impact: High (blocks real traces)
- Mitigation: Prototype early (end of Phase 1), simple design first
- Contingency: Defer to Phase 5, document limitation

**Risk 2: Python DSL too complex for users**
- Probability: Medium
- Impact: High (unusable)
- Mitigation: User testing, start simple, iterate
- Contingency: Simplify DSL, drop composition

**Risk 3: Streaming doesn't perform**
- Probability: Medium
- Impact: Medium (limits trace size)
- Mitigation: Benchmark early, optimize incrementally
- Contingency: Require pre-processed traces, smaller chunks

**Risk 4: Users need features we haven't planned**
- Probability: High
- Impact: Variable
- Mitigation: Extensibility strategy (Tier 2 predicates)
- Contingency: Add to Phase 5, or accept limitation

**Risk 5: Agda → Haskell → Python overhead too high**
- Probability: Low
- Impact: High (unusable)
- Mitigation: Benchmark in Phase 1, optimize in Phase 3
- Contingency: Rewrite hot paths in Haskell (lose verification)

---

## SUMMARY: WHAT CHANGED

### Major Changes to Plan

1. **Multiplexing**: Phase 5 → **Phase 2A** (CRITICAL)
2. **Python DSL**: Not planned → **Phase 2A core deliverable**
3. **Streaming**: Phase 3 → **Phase 2B** (essential)
4. **Counterexamples**: Phase 4 → **Phase 2B** (usability)
5. **Validation**: Added real-world testing throughout
6. **Extensibility**: Added three-tier strategy
7. **Decision Points**: Added pivot opportunities
8. **Risk Tracking**: Added explicit risk management

### Phase Durations (Revised)

- Phase 1: 2-3 weeks (was ongoing)
- Phase 2A: 4-6 weeks (was "Phase 2", now split)
- Phase 2B: 3-4 weeks (new phase)
- Phase 3: 4-6 weeks (verification)
- Phase 4: 3-4 weeks (hardening)
- Phase 5: Ongoing (extensions)

**Total MVP**: ~16-23 weeks (4-6 months)

### What Makes This Realistic

✅ **Incremental delivery**: Each phase delivers value
✅ **Validation at each step**: Fail fast if wrong direction
✅ **Clear decision points**: Pivot opportunities
✅ **Extensibility**: Don't need to predict everything
✅ **Dropped features tracked**: Can reconsider later
✅ **Risk mitigation**: Contingencies for likely failures

**This is a plan to build great software, not perfect software**
