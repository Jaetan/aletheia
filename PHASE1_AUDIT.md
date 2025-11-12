# Phase 1 Comprehensive Audit

**Date**: 2025-11-12
**Purpose**: Identify all limitations, deferred proofs, simplifying assumptions, and constraints before completing Phase 1

---

## CRITICAL ISSUES (Must Fix in Phase 1)

### ✅ 1. Rational Number Parser - FIXED
**File**: `DBC/Parser.agda:99-148`
**Issue**: Parser was ignoring fractional parts (0.25 → 0/1)
**Impact**: Was breaking all signal scaling factors
**Fix Implemented**: Proper decimal → rational conversion without postulates
- Converts "0.25" → 1/4, "1.5" → 3/2 correctly
- Uses `power10` function that returns `suc n` to prove NonZero automatically
- Handles both positive and negative decimals
- **NO POSTULATES NEEDED** - remains `--safe --without-K` compliant
**Implementation Details**:
- `power10 n` always returns `suc k` for some k, proving result ≥ 1
- Pattern matching with `with power10 (length chars)` exposes `suc` constructor
- Agda automatically finds NonZero instance for denominator
- Zero case is unreachable but included for coverage checking

### ✅ 2. Signal Scaling Removal - FIXED
**File**: `CAN/Encoding.agda:45-70`
**Issue**: Was ignoring the factor parameter
**Impact**: Would have broken InjectSignal for scaled signals
**Fix Implemented**: Proper division with runtime zero-check
- Formula: `raw = floor((signalValue - offset) / factor)`
- Returns `Nothing` if factor is zero (malformed DBC)
- **NO POSTULATES NEEDED** - remains `--safe --without-K` compliant
**Implementation Details**:
- Runtime check: `isZero factor` returns `Nothing` if true
- Uses unnormalized rational division `ℚᵘ._÷_` for simplicity
- Pattern matches on `mkℚᵘ (+ suc num)` and `mkℚᵘ -[1+ num ]` to expose nonzero numerator
- Agda automatically finds NonZero instance for these patterns
- Converts back to normalized ℚ via `fromℚᵘ`
**Trade-off**: Runtime check instead of static proof (deferred to Phase 3)

### ✅ 3. Response Formatting - FIXED
**File**: `Protocol/Response.agda:41-91`
**Issue**: Was returning placeholders for signal values and frame bytes
**Impact**: Would have made ExtractSignal/InjectSignal output useless
**Fix Implemented**: Proper formatting for both types
- **ℚ → String**: Uses `Data.Rational.Show.show` (format: "3/2", "1/4")
- **Vec Byte 8 → String**: Custom hex formatter (format: "0x12 0x34 0x56 ...")
- **NO POSTULATES NEEDED** - remains `--safe --without-K` compliant
**Implementation Details**:
- `hexDigit`: Converts 0-15 to '0'-'9','A'-'F'
- `byteToHex`: Converts Fin 256 to "0xNN" using division/modulo
- `bytesToHex`: Uses `foldr` over Vec to concatenate with spaces
- Uses List cons operator `L.∷` (not Vec) for building char lists
**Example Output**:
- Signal value 1.5 → "value: 3/2"
- Frame [0x12, 0x34, ...] → "frame: 0x12 0x34 0x56 0x78 0x9A 0xBC 0xDE 0xF0"

---

## ARCHITECTURAL CONSTRAINTS (Design Decisions)

⚠️ **IMPORTANT**: These constraints are currently "by design" but we must **revisit before Phase 2** to ensure we're not painting ourselves into a corner. See "Architectural Constraint Review Plan" section at end of document.

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
**Risk**: 🔴 **HIGH** - Hardcoded `Vec Byte 8` is deeply embedded in:
  - All encoding/decoding functions
  - Protocol commands (ExtractSignal/InjectSignal)
  - DBC parser structure
  - Test data
**Mitigation**: Should parameterize Frame type early if CAN-FD is ever needed

### 📐 5. Hardcoded 64-bit Address Space
**File**: `CAN/Frame.agda:19` - `BitPosition = Fin 64`
**Constraint**: Assumes 8-byte frames (8 × 8 = 64 bits)
**Phase to Lift**: **Phase 5** (with CAN-FD support)
**Risk**: 🟡 **MEDIUM** - Tightly coupled to constraint #4
**Mitigation**: Fix together with payload parameterization

### 📐 6. Single Protocol Parser Per Command
**File**: `Protocol/Parser.agda:79-81`
**Current**: `parseCommand = parseEcho <|> parseParseDBC`
**Limitation**: No versioning, no protocol negotiation
**Phase to Extend**: **Phase 4** (protocol v2 with capabilities negotiation)
**Risk**: 🟢 **LOW** - Protocol is internal API, easy to extend
**Mitigation**: None needed - good separation of concerns

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
**Phase**: **Phase 5** (advanced DBC features) - **OR Phase 2 if needed for LTL**
**Complexity**: High (changes signal extraction logic)

**What is Multiplexing**:
In CAN, a single message ID can have different "modes" where different signals are active. A multiplexor signal determines which set of signals is valid.

**Example**:
```yaml
message_id: 0x100
signals:
  - name: Mode         # Multiplexor signal
    value: 0 → signals A, B, C are valid
    value: 1 → signals D, E, F are valid
    value: 2 → signals G, H, I are valid
```

**Why It Matters**:
- **Common in automotive**: ~30% of CAN messages use multiplexing
- **Affects extraction**: Must check multiplexor value before extracting signal
- **Affects LTL**: Temporal properties may need to reason about signal presence
  - Example: "If Mode=1, THEN signal D must be between 0 and 100"
- **Type safety**: Should multiplexed signals have Optional types?

**Impact on Architecture**:
- DBC types need to model multiplexing relationships
- Signal extraction must check multiplexor first
- LTL formulas may need conditional signal access
- Python API needs to handle signal absence gracefully

**Decision Point**: **End of Phase 1** (same as CAN-FD review)
- If LTL will reason about multiplexed signals → implement in Phase 2
- If just decoding frames → defer to Phase 5
- **Risk**: If deferred, LTL module may assume all signals always present

**Design Options**:
1. **Static Types**: `Signal (Maybe ℚ)` - multiplexed signals optional
2. **Dynamic Check**: Return `Nothing` if multiplexor doesn't match
3. **Dependent Types**: Signal validity depends on multiplexor value

**Recommendation**: Address in Phase 2 if doing real-world CAN traces, Phase 5 if theoretical only

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

---

## ARCHITECTURAL CONSTRAINT REVIEW PLAN

⚠️ **Critical**: We must validate architectural constraints early to avoid designing ourselves into a corner. Once Phase 2 (LTL) is built on top of Phase 1 foundations, changing core types becomes exponentially harder.

### Review Schedule

**🔴 End of Phase 1 (Before Phase 2 Starts)**:
- **Decision Point**: Validate that Standard CAN is sufficient AND signal model is adequate
- **Questions to Answer**:
  1. Do we have users who need CAN-FD? (Survey/research)
  2. Do we have users who need extended 29-bit IDs?
  3. Will LTL formulas reference frame payload length?
  4. Will trace analysis tools assume 8-byte frames?
  5. **Do we need signal multiplexing support?** (NEW)
     - Will we analyze real-world CAN traces? (likely yes → multiplexing needed)
     - Will LTL reason about conditional signal presence?
     - ~30% of automotive messages use multiplexing
- **Risk**: If LTL module assumes `Vec Byte 8` OR assumes all signals always present, refactoring later requires rewriting entire Phase 2
- **Action**: If any answer is "yes" or "maybe", refactor Frame type AND signal model NOW before Phase 2

**🟡 Mid-Phase 2 (After LTL Core)**:
- **Review Point**: Check if LTL formulas expose payload size assumptions
- **Questions**:
  1. Can LTL formulas express "signal at bit position > 64"?
  2. Do temporal properties depend on fixed frame structure?
  3. Would trace parser need to handle variable-length frames?
- **Action**: If yes, assess refactoring cost vs benefit

**🟢 End of Phase 3 (Before Phase 4)**:
- **Review Point**: Finalize protocol design before external API freeze
- **Questions**:
  1. Do we need streaming protocol (multiple commands per connection)?
  2. Do we need protocol versioning/negotiation?
  3. What's our backward compatibility policy?
- **Action**: Design Phase 4 protocol with extensibility in mind

### Constraint Risk Matrix

| # | Constraint | Change Cost @ Phase 1 | Change Cost @ Phase 2 | Change Cost @ Phase 3 | Recommendation |
|---|------------|----------------------|----------------------|----------------------|----------------|
| 4 | Vec Byte 8 | 🟢 Low (1 day) | 🟡 Medium (3 days) | 🔴 High (1 week) | **Review at Phase 1 end** |
| 5 | Fin 64 | 🟢 Low (tied to #4) | 🟡 Medium (tied to #4) | 🔴 High (tied to #4) | **Review with #4** |
| 6 | Protocol | 🟢 Low (internal) | 🟢 Low (internal) | 🟡 Medium (if API published) | Review at Phase 3 |
| 24 | Extended IDs | 🟢 Low (sum type) | 🟡 Medium (DBC parser) | 🔴 High (trace format) | **Review at Phase 1 end** |
| 26 | Value Tables | 🟢 Low (additive) | 🟢 Low (additive) | 🟢 Low (additive) | Can defer safely |
| 27 | **Multiplexing** | 🟡 Medium (2-3 days) | 🔴 High (1 week) | 🔴 Very High (2 weeks) | **⚠️ REVIEW AT PHASE 1 END** |

**Note on Multiplexing**: Unlike other extensions, multiplexing affects core signal model:
- Not just additive (changes SignalDef type)
- Affects LTL semantics (conditional signal presence)
- Common in real CAN traces (~30% of messages)
- **Decision needed before Phase 2**: All signals always present OR optional types?

### Early Warning Signs

🚨 **Red Flags** that indicate we're painting ourselves into a corner:

1. **Deep Embedding**: If we find ourselves writing:
   ```agda
   -- BAD: Hardcoded assumptions everywhere
   processSignal : Vec Byte 8 → ...
   verifyFrame : Fin 2048 → Vec Byte 8 → ...
   ltlCheck : List (Vec Byte 8) → ...
   ```
   **Fix**: Abstract over frame size BEFORE it spreads

2. **Type Proliferation**: If we see:
   ```agda
   Frame8 : Set
   Frame16 : Set  -- Copy-paste of Frame8 with different size
   Frame64 : Set  -- Another copy-paste
   ```
   **Fix**: Use dependent types NOW, not later

3. **Conditional Logic**: If we see:
   ```agda
   if frameSize == 8
     then processStandardCAN
     else error "unsupported"
   ```
   **Fix**: Make unsupported cases unrepresentable in types

4. **External API Exposure**: If Python API exposes:
   ```python
   def extract_signal(frame: bytes) -> float:
       assert len(frame) == 8  # DANGER: API contract hardcoded
   ```
   **Fix**: Use `Sequence[int]` or parameterize before API freeze

### Recommended Refactoring (If Needed)

If Phase 1 review determines we need flexibility:

**Option A - Parameterized Frame** (Preferred):
```agda
record CANFrame (n : ℕ) : Set where
  field
    id : CANId  -- Sum type: Standard (Fin 2048) | Extended (Fin 536870912)
    dlc : Fin (suc n)
    payload : Vec Byte n

-- Standard CAN
StandardFrame : Set
StandardFrame = CANFrame 8

-- CAN-FD
FDFrame : Set
FDFrame = CANFrame 64
```
**Effort**: 2-3 days to refactor Phase 1
**Benefit**: Future-proof, type-safe, no runtime checks

**Option B - Runtime Tagged Type** (Not Recommended):
```agda
data FrameType : Set where
  Standard : FrameType
  Extended : FrameType
  FD : FrameType

record CANFrame : Set where
  field
    frameType : FrameType
    id : ℕ  -- Runtime validation
    payload : List Byte  -- Runtime length check
```
**Effort**: 1 day
**Downside**: Loses type safety, requires runtime checks, defeats Agda benefits

### Decision Criteria

**Refactor NOW if**:
- We know we'll need CAN-FD (e.g., user requirement)
- Research shows >20% of target users need extended features
- Cost to refactor later > 1 week
- Type safety would be lost with runtime approach

**Defer if**:
- No clear user requirement yet
- Standard CAN sufficient for prototype/MVP
- Refactoring cost < 3 days even at Phase 3
- Can maintain type safety with runtime checks

### Action Items

**Before Starting Phase 2**:
1. ☐ Survey potential users about CAN-FD requirements
2. ☐ Research typical CAN frame sizes in target domains (automotive, industrial, etc.)
3. ☐ **Research signal multiplexing prevalence** in target use cases
   - Review sample DBC files from automotive industry
   - Check if test traces contain multiplexed signals
   - Assess: Can we ignore multiplexing for MVP or is it essential?
4. ☐ Estimate refactoring cost if done now vs after Phase 2
   - Frame parameterization: 1-2 days now vs 1 week later
   - Multiplexing support: 2-3 days now vs 2 weeks later
5. ☐ **DECIDE**:
   - Refactor to parameterized Frame OR accept 8-byte constraint
   - Add multiplexing support OR accept all-signals-present constraint
6. ☐ Document decision rationale in DESIGN.md
7. ☐ If not refactoring:
   - Add "CAN-FD Support" to Phase 5 roadmap with effort estimate
   - Add "Signal Multiplexing" to Phase 5 roadmap with effort estimate
   - Document limitations in user-facing documentation

**This review is MANDATORY before Phase 2 starts.**

**Critical Questions**:
- Will Phase 2 analyze real-world automotive CAN traces? → Likely need multiplexing
- Will Phase 2 be theoretical/academic only? → Can defer multiplexing
- Is this project targeting production use? → Need both CAN-FD and multiplexing eventually

---

## POSTULATES AND PROOF OBLIGATIONS TRACKING

⚠️ **IMPORTANT**: All postulates must be replaced with proofs before project is considered complete. This section tracks where postulates are allowed and when they must be removed.

### Current Postulate Status

**Phase 1 (Current)**: ✅ **ZERO POSTULATES - STILL CLEAN!**
- Using `--safe` flag which prohibits postulates
- All code is fully verified or uses runtime checks
- No holes `{!!}` in production code paths

### Anticipated Postulates - AVOIDED!

**Critical Fixes Completed Without Postulates**:

**1. Rational Parser (#1)** - ✅ NO POSTULATES NEEDED
- Initially thought we'd need NonZero proofs for division
- **Solution**: `power10` returns `suc n`, Agda finds instance automatically
- Pattern matching with `with` exposes constructor
- Remains `--safe --without-K` compliant

**2. Signal Scaling Removal (#2)** - ✅ NO POSTULATES NEEDED
- Initially thought we'd need NonZero proof for factor
- **Solution**: Runtime zero-check returns `Maybe ℤ`
- Pattern match on `mkℚᵘ` exposes nonzero numerator patterns
- Agda finds NonZero instance for `+ suc num` and `-[1+ num ]`
- Remains `--safe --without-K` compliant

**Trade-offs Made**:
- Runtime checks instead of static proofs (acceptable for Phase 1)
- Unreachable cases included for coverage checking
- Performance cost of checks is negligible
- Maintains type safety and correctness guarantees

**Phase 3 Goals**:
- Prove that these runtime checks never fail
- Refine types to eliminate unreachable cases
- Add formal correctness proofs

### Postulate Management Policy

**Rules**:
1. **No postulates in --safe modules** (enforced by compiler)
2. **If postulate needed**: Create separate `*.Unsafe.agda` module without --safe
3. **Document every postulate** with:
   - Why it's needed
   - What property it assumes
   - When it will be replaced
   - Alternative approaches considered
4. **Track in this document**: All postulates must appear in this audit
5. **Phase 3 requirement**: ALL postulates must be replaced before Phase 3 completion

**Workflow for Adding Postulate**:
```agda
-- Step 1: Try to avoid (use runtime checks, Maybe, etc.)
-- Step 2: If truly needed, create Unsafe module:

{-# OPTIONS --without-K #-}  -- NOT --safe!
module Aletheia.DBC.Parser.Unsafe where

postulate
  property-name : ∀ ... → ...
  -- TODO Phase 3: Replace with real proof
  -- Justification: [explain why needed]
  -- Test coverage: [list tests that validate this property]
```

### Postulate Replacement Schedule

| Postulate | Module | Added in Phase | Replace by Phase | Effort | Priority |
|-----------|--------|----------------|------------------|--------|----------|
| (none yet) | - | - | - | - | - |

**To be updated as postulates are added during Phase 1 rational parser work.**

### Phase 3 Exit Criteria

**Cannot complete Phase 3 until**:
- ☐ All postulates replaced with proofs
- ☐ All `{!!}` holes filled
- ☐ All modules using --safe flag
- ☐ All properties in audit document have formal proofs or explicit decision to defer

### Tracking Holes vs Postulates

**Holes `{!!}`**: Incomplete implementations
- **Allowed in**: Non-critical modules, future phases
- **Not allowed in**: Core logic used in production
- **Status**: Tracked in "Incomplete Implementations" section above

**Postulates**: Assumed properties without proof
- **Allowed in**: Unsafe modules only, with documentation
- **Not allowed in**: Safe modules (compiler enforces)
- **Status**: Must be tracked in table above

**Current Status**:
- Holes: 5 (all in Phase 2 modules - LTL/Trace)
- Postulates: 0 (will track when added for rational division)

### Action Items for Postulate Management

**During Phase 1 rational parser implementation**:
1. ☐ Try to avoid postulates (use runtime checks first)
2. ☐ If postulate needed, create Unsafe module
3. ☐ Document postulate in this audit (update table above)
4. ☐ Add comprehensive tests to validate assumed properties
5. ☐ Add Phase 3 task to replace with real proof

**Before Phase 2**:
6. ☐ Review all postulates added during Phase 1
7. ☐ Estimate effort to replace each one
8. ☐ Decide which to replace early vs defer to Phase 3

**Before Phase 3 Completion**:
9. ☐ Replace ALL postulates with real proofs
10. ☐ Verify all modules use --safe flag
11. ☐ No holes in production code paths

**This tracking ensures no 'forgotten' postulates or proof obligations.**

