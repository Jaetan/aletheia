# Phase 1 Comprehensive Audit

**Date**: 2025-11-12
**Purpose**: Identify all limitations, deferred proofs, simplifying assumptions, and constraints before completing Phase 1

---

## CRITICAL ISSUES (Must Fix in Phase 1)

### 🔴 1. Rational Number Parser - BROKEN
**File**: `DBC/Parser.agda:99-115`
**Issue**: Parser ignores fractional parts (0.25 → 0/1)
**Impact**: All signal scaling factors are wrong, ExtractSignal/InjectSignal produce incorrect values
**Example**:
```yaml
factor: 0.25  # Parsed as 0/1 instead of 1/4
```
**Fix Required**: Implement proper decimal → rational conversion
**Phase**: **Phase 1** (moved from Phase 5 - this is correctness, not optimization)

### 🔴 2. Signal Scaling Removal - BROKEN
**File**: `CAN/Encoding.agda:46-53`
**Issue**: `removeScaling` assumes `factor ≈ 1.0`, ignores actual factor
**Impact**: InjectSignal produces completely wrong raw values for scaled signals
**Current Code**:
```agda
removeScaling signalValue factor offset =
  just (floor (signalValue -ℚ offset))  -- Ignores factor!
```
**Fix Required**: Implement division: `(signalValue - offset) / factor`
**Phase**: **Phase 1** (blocks InjectSignal functionality)

### 🔴 3. Response Formatting Incomplete
**File**: `Protocol/Response.agda:46-48`
**Issue**: Cannot output signal values or frame bytes (returns placeholders)
**Impact**: ExtractSignal/InjectSignal commands return useless output
**Placeholders**:
```agda
formatData (SignalValueData val) = "value: " ++ "<rational>" ++ "\n"  -- TODO
formatData (FrameData bytes) = "frame: <bytes>\n"  -- TODO
```
**Fix Required**:
- Implement `ℚ → String` conversion
- Implement `Vec Byte 8 → String` (hex format: "0x12 0x34 ...")
**Phase**: **Phase 1** (blocks ExtractSignal/InjectSignal output)

---

## ARCHITECTURAL CONSTRAINTS (Design Decisions)

### 📐 4. Standard CAN Only (No CAN-FD Support)
**Files**:
- `CAN/Frame.agda:16` - `payload : Vec Byte 8`
- `DBC/Types.agda:21` - `id : Fin 2048`
- `DBC/Types.agda:23` - `dlc : Fin 9`

**Constraints**:
- Fixed 8-byte payload (CAN-FD supports up to 64 bytes)
- 11-bit CAN IDs only (0-2047), no extended 29-bit IDs
- DLC fixed to 0-8 (CAN-FD has different DLC encoding)

**Rationale**: Standard CAN covers 95% of automotive use cases
**Phase to Lift**: **Phase 5** (extended features)
**Effort**: Medium - requires parameterizing Frame type over payload length

### 📐 5. Hardcoded 64-bit Address Space
**File**: `CAN/Frame.agda:19` - `BitPosition = Fin 64`
**Constraint**: Assumes 8-byte frames (8 × 8 = 64 bits)
**Phase to Lift**: **Phase 5** (with CAN-FD support)

### 📐 6. Single Protocol Parser Per Command
**File**: `Protocol/Parser.agda:79-81`
**Current**: `parseCommand = parseEcho <|> parseParseDBC`
**Limitation**: No versioning, no protocol negotiation
**Phase to Extend**: **Phase 4** (protocol v2 with capabilities negotiation)

---

## DEFERRED PROOFS (Documented but Not Implemented)

### 📝 7. Parser Combinator Monad Laws
**File**: `Parser/Properties.agda:10-11`
**Missing**:
- Left identity: `pure a >>= f ≡ f a`
- Right identity: `m >>= pure ≡ m`
- Associativity: `(m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)`

**Rationale**: Structural recursion ensures termination; monad laws are "nice to have" but not critical for correctness
**Phase**: **Phase 3** (grammar formalization)
**Impact**: Low (type system already ensures no runtime errors)

### 📝 8. DBC Parser Well-Formedness
**File**: `DBC/Properties.agda:238-243`
**Missing**: Proof that `parseDBC` success implies `dbc-well-formed dbc ≡ true`
**Current**: Hole `{!!}` - "TODO: Prove by induction on parse tree"
**Phase**: **Phase 3** (parser soundness proofs)
**Impact**: Medium (we rely on runtime checks for now)

### 📝 9. Signal Encoding Round-Trip Properties
**File**: `CAN/Encoding.agda:128-135`
**Missing**:
```agda
-- extract (inject v sig order frame) ≡ just v
-- inject v sig order (inject v sig order frame) ≡ inject v sig order frame
```
**Phase**: **Phase 5** (encoding verification)
**Impact**: High for critical applications, medium for Phase 1
**Note**: Cannot use postulate with --safe flag

### 📝 10. DBC Grammar Formalization
**File**: `DBC/Properties.agda:249-261`
**Missing**:
```agda
ValidYAML : List Char → Set
ValidDBC : List Char → DBC → Set
parseDBC-sound : parseDBC input ≡ just (dbc, rest) → ValidDBC input dbc
```
**Phase**: **Phase 3** (parser soundness)

### 📝 11. DBC Pretty-Printer and Round-Trip
**File**: `DBC/Properties.agda:263-274`
**Missing**:
```agda
printDBC : DBC → String
parse-print-inverse : parseDBC (toList (printDBC dbc)) ≡ just (dbc, [])
```
**Phase**: **Phase 5** (DBC tooling)

---

## SIMPLIFYING ASSUMPTIONS

### ⚠️ 12. Protocol Parser - Simplified Multiline Handling
**File**: `Protocol/Parser.agda:49-52`
**Current**: `multilineValue key = string key *> char ':' *> spaces *> (fromList <$> many anyChar)`
**Limitation**: Reads everything until EOF, no support for multiple commands in one input
**Impact**: Must send exactly one command per binary invocation
**Phase to Enhance**: **Phase 4** (streaming protocol)

### ⚠️ 13. No Signal Overlap Detection
**Current**: Parser accepts overlapping signals in same message
**Example**: Two signals both at startBit=0, bitLength=16 would be parsed successfully
**Impact**: Injection of one signal could corrupt another
**Phase**: **Phase 5** (enhanced DBC validation)
**Effort**: Medium - requires interval tree or conflict detection

### ⚠️ 14. No Range Validation on Parsing
**Current**: Parser accepts any ℚ values for min/max/offset/factor
**Example**: `minimum: 100, maximum: 0` would parse successfully
**Impact**: Runtime errors during signal extraction if bounds are inverted
**Phase**: **Phase 5** (enhanced validation)

### ⚠️ 15. No Unit Validation
**Current**: DBC parser accepts any string as unit
**Example**: `unit: "bananas"` is valid
**Impact**: None for Phase 1 (units are informational only)
**Phase**: **Never** (free-form units are valid in automotive industry)

---

## INCOMPLETE IMPLEMENTATIONS (Holes & Stubs)

### 🔧 16. DBC Semantics - Frame Decoding
**File**: `DBC/Semantics.agda:13`
**Status**: `decodeFrame = {!!}`
**Purpose**: Extract all signals from a frame given a DBCMessage
**Phase**: **Phase 2** (needed for LTL trace analysis)
**Priority**: Medium

### 🔧 17. LTL Semantics - Trace Satisfaction
**File**: `LTL/Semantics.agda:10`
**Status**: `trace ⊨ formula = {!!}`
**Purpose**: Define what it means for a trace to satisfy an LTL formula
**Phase**: **Phase 2** (core LTL functionality)
**Priority**: High for Phase 2

### 🔧 18. LTL Model Checker
**File**: `LTL/Checker.agda:9`
**Status**: `-- TODO: Model checking algorithm`
**Purpose**: Verify LTL formulas against traces
**Phase**: **Phase 2** (core LTL functionality)
**Priority**: High for Phase 2

### 🔧 19. Python DSL Parser
**File**: `LTL/DSL/Parser.agda:9`
**Status**: `parsePythonLTL = {!!}`
**Purpose**: Parse Python-style LTL syntax to core LTL AST
**Phase**: **Phase 2** (user-facing LTL API)
**Priority**: Medium for Phase 2

### 🔧 20. Python DSL Translator
**File**: `LTL/DSL/Translate.agda:8-9`
**Status**:
```agda
-- TODO: Translate Python DSL to core LTL
-- TODO: Prove translation preserves semantics
```
**Phase**: **Phase 2** (with proofs in Phase 3)

### 🔧 21. Trace Parser
**File**: `LTL/Trace/Parser.agda:9`
**Status**: `parseCANTrace = {!!}`
**Purpose**: Parse trace files (YAML or binary format)
**Phase**: **Phase 2** (trace analysis)
**Priority**: High for Phase 2

---

## MISSING FUNCTIONALITY (Not Yet Started)

### 🆕 22. DBC Serialization (Output)
**File**: `Protocol/Response.agda:46`
**Missing**: Convert DBC back to YAML string
**Use Case**: Echo back parsed DBC for validation
**Phase**: **Phase 1** (if needed for testing) or **Phase 5** (pretty-printer)
**Current Workaround**: Return placeholder `"<parsed>"`

### 🆕 23. Byte Array Parsing (Protocol)
**File**: `Protocol/Parser.agda` (not yet implemented)
**Missing**: Parse hex byte strings to `Vec Byte 8`
**Format**: `"0x12 0x34 0x56 0x78 0x9A 0xBC 0xDE 0xF0"`
**Phase**: **Phase 1** (blocks ExtractSignal/InjectSignal parsers)
**Priority**: Critical

### 🆕 24. Extended CAN ID Support
**Missing**: 29-bit extended CAN IDs
**Current**: Only 11-bit standard IDs (Fin 2048)
**Phase**: **Phase 5**
**Effort**: Medium (requires sum type: Standard | Extended)

### 🆕 25. Message Transmitter Information
**Missing**: DBC files can specify which ECU sends each message
**Current**: Parsed as String but not used
**Phase**: **Phase 5** (enhanced DBC model)

### 🆕 26. Value Tables (Enumerations)
**Missing**: DBC can define named values (e.g., GearPosition: 0=Park, 1=Reverse, ...)
**Phase**: **Phase 5** (extended DBC features)

### 🆕 27. Signal Multiplexing
**Missing**: Some signals are only present when a multiplexor signal has specific value
**Phase**: **Phase 5** (advanced DBC features)
**Complexity**: High (changes signal extraction logic)

---

## TECHNICAL DEBT & FUTURE IMPROVEMENTS

### 💡 28. Error Messages - Not User-Friendly
**Current**: Parsers return `nothing` on failure, no error position or message
**Impact**: Hard to debug malformed DBC files
**Enhancement**: Add error reporting with line/column numbers
**Phase**: **Phase 4** (robustness)

### 💡 29. Performance - No Optimization Yet
**Current**: Parsers rebuild lists, no memoization
**Impact**: Acceptable for Phase 1 (files < 100KB)
**Enhancement**: Profile and optimize hot paths
**Phase**: **Phase 5** (optimization)

### 💡 30. Logging - Placeholder Module
**File**: `Aletheia/Logging.agda`
**Status**: Likely minimal or stub
**Enhancement**: Structured logging for debugging
**Phase**: **Phase 4** (robustness)

---

## SUMMARY BY SEVERITY

### ❗ CRITICAL (Blocks Phase 1 Completion)
1. **Rational parser** - breaks signal scaling
2. **removeScaling** - breaks signal injection
3. **Response formatting** - blocks ExtractSignal/InjectSignal output
4. **Byte array parser** - blocks ExtractSignal/InjectSignal input

**Action Required**: All 4 must be fixed before Phase 1 completion

### ⚠️ HIGH PRIORITY (Should Address in Phase 1)
- DBC serialization (for testing output)
- Signal overlap detection (safety)

### 📝 DEFERRED TO PHASE 3 (Verification)
- Parser monad laws
- DBC parser soundness
- Grammar formalization
- Round-trip properties

### 🔧 DEFERRED TO PHASE 5 (Extensions)
- CAN-FD support
- Extended CAN IDs
- Signal multiplexing
- Value tables
- Performance optimization

---

## RECOMMENDATIONS FOR PHASE 1 COMPLETION

### Must Fix (Blocks functionality):
1. ✅ Implement proper rational parser (0.25 → 1/4)
2. ✅ Implement removeScaling with division
3. ✅ Implement ℚ → String formatting
4. ✅ Implement Vec Byte 8 → String formatting (hex)
5. ✅ Implement hex string → Vec Byte 8 parser
6. ✅ Complete ExtractSignal/InjectSignal protocol parsers

### Should Fix (Improves reliability):
7. ⚠️ Add signal overlap detection (runtime check)
8. ⚠️ Add range validation (min ≤ max)

### Can Defer (Document as known limitations):
9. 📝 All proof obligations → Phase 3
10. 🔧 All LTL/Trace implementations → Phase 2
11. 🆕 All extended CAN features → Phase 5

**Total Phase 1 Completion**: 6 critical fixes + 2 optional safety checks

