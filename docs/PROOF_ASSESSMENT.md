# Proof Assessment

**Date**: 2026-03-27

This document inventories what Aletheia proves formally and identifies safety-critical gaps where proofs are missing.

---

## What Is Proven

### LTL Semantics (Adequacy)

`stepL` (the production LTL evaluator in `LTL/Incremental.agda`) is sound with respect to denotational LTLf semantics (De Giacomo & Vardi 2013). The adequacy theorem covers all 13 LTL operators including metric variants. This means: if `stepL` says a property holds/fails, the denotational semantics agrees.

- **Module**: `LTL/Adequacy.agda` (transitively checks `LTL/Semantics.agda`, `LTL/Adequacy/SoundOps.agda`)
- **Theorem**: `adequacy : Sound (runL table proc sigma) (denotation table proc sigma)`

### DBC Validation (Soundness + Completeness)

The DBC validator (`DBC/Validator.agda`) is both sound and complete for 16 structural checks (9 error, 7 warning). If the validator says a DBC is valid, it satisfies all structural invariants. If it reports an issue, the issue genuinely exists.

- **Module**: `DBC/Validity/Theorem.agda`
- **Theorems**: `soundness`, `completeness`

### Signal Encoding Roundtrip

Extracting a signal from a frame that was built by injecting that signal returns the original value. Covers both byte orders (little-endian, big-endian/Motorola), signed and unsigned signals, mixed byte-order commutativity, and scaling arithmetic.

- **Modules**: `CAN/Encoding/Properties.agda`, `CAN/Endianness/Properties.agda`, `CAN/Batch/Properties.agda`
- **Key lemma**: `extractBits-injectBits-roundtrip`
- **Scaling**: `removeScaling-applyScaling-exact` (roundtrip), `applyScaling-injective`, `ℚ-cancel` (field cancellation)
- **Batch**: `extractAll-complete` (partition completeness), `injectAll-preserves-disjoint` (value preservation)
- **Capstone**: `validDBC-roundtrip` (all 7 preconditions decidable)

### DBC Format-Parse Roundtrip

Formatting a well-formed DBC to JSON and parsing it back yields the original DBC.

- **Module**: `DBC/Formatter/Properties.agda`
- **Theorem**: `format-parse-roundtrip : WellFormedDBCRT d -> parseDBCWithErrors (formatDBC d) = inj2 d`

### Binary FFI Guards

When `handleDataFrame` is called in a non-Streaming state (WaitingForDBC or ReadyToStream), the state is returned unchanged. Also: Word8 values satisfy `n % 256 = n`, justifying the Haskell shim's `bytesToAgdaVec` skipping the modulo operation.

- **Module**: `Protocol/FrameProcessor/Properties.agda`
- **Lemmas**: `handleDataFrame-guard-waitingForDBC`, `handleDataFrame-guard-readyToStream`, `mod-identity-byte`

### Parser Framework

JSON parser is deterministic. Parser monad satisfies monad laws.

- **Module**: `Parser/Properties.agda`
- **Key lemma**: `parseJSON-deterministic`

### Initial LTL State Correctness

`initProc` produces the correct initial state: `denot table (initProc φ) ≡ mapLTL table φ`. Combined with adequacy, this gives end-to-end soundness from formula specification to runtime verdict.

- **Module**: `LTL/Coalgebra/Properties.agda`
- **Theorem**: `initProc-correct`

### Response Formatting Correctness

Each `Response` and `PropertyResult` constructor maps to the expected JSON structure. Proved by definitional equality (refl) for all 8 constructors: Ack, Success, Error, ByteArray, DBCResponse, Violation, Satisfaction, StreamComplete.

- **Module**: `Protocol/ResponseFormat/Properties.agda`

### Other Proofs

- **LTL JSON roundtrip**: `LTL/JSON/Properties.agda`
- **Protocol JSON schemas**: `Protocol/JSON/Properties.agda`
- **DBC parser well-formedness**: `DBC/JSONParser/Properties.agda` (parsed DBCs satisfy `WellFormedDBC`)
- **Batch extraction**: `extractAll-complete` (partition completeness), `injectAll-preserves-disjoint` (value preservation), `validDBC-roundtrip` (capstone: validated DBC + inject + extract = original)

---

## What Is NOT Proven

Ranked by safety impact. If any of these is wrong, LTL verdicts can be silently incorrect.

### Tier 1: Data Integrity Chain

These functions form the path from "frame received" to "stepL called." The Adequacy theorem guarantees stepL is sound, but only if the predicate table faithfully represents the formula's atoms evaluated against the frame.

**1. Predicate table construction (`mkPredTable`)** — **PROVEN**

- **File**: `Protocol/StreamState.agda:135`
- **What it does**: Maps signal predicates to a truth-value function over frames. For each atom index, extracts the relevant signal from the frame and evaluates the predicate.
- **Status**: ✅ Proven in `Protocol/FrameProcessor/Properties.agda`. The `Faithful` relation establishes that for every atom index `i`, `lookupAtom (collectAtoms φ) i ≡ just pred_i` where `pred_i` is the `i`-th predicate in left-to-right tree order. `mkPredTable-lookup` then shows `mkPredTable` evaluates that predicate. Key lemmas: `collectAtoms-faithful`, `faithful-gen`, `collectAtomsAcc-spec`, `indexHelper-counter`.

**2. Signal cache update (`updateCacheFromFrame`)** — **PROVEN**

- **File**: `Protocol/StreamState.agda:148`
- **What it does**: Updates a three-valued signal cache (maps signal names to their last-known value). The cache enables "changed-by" and temporal predicates that compare current vs previous values.
- **Status**: ✅ Proven in `Protocol/FrameProcessor/Properties.agda`. Four properties cover the cache update chain:
  - `lookupCache-updateCache-hit`: after update, the target key maps to the new value
  - `lookupCache-updateCache-miss`: updating one key doesn't affect lookups of other keys
  - `updateSignals-step-hit/miss`: `updateSignals` decomposes into `updateCache` + recursion
  - `updateCacheFromFrame-no-match/match`: `updateCacheFromFrame` decomposes into `updateSignals` via `findMessageById`

**3. Frame processing in Streaming phase (`handleDataFrame`)** — **PROVEN**

- **File**: `Protocol/StreamState.agda:285`
- **What it does**: In Streaming phase: updates signal cache, evaluates each property's LTL formula via `stepL`, collects violations, advances state.
- **Status**: ✅ Proven in `Protocol/FrameProcessor/Properties.agda`. 15 properties covering the full frame processing pipeline:
  - Guards: non-Streaming state returns unchanged (properties 1-2)
  - Streaming decomposition: `handleDataFrame ≡ dispatchIterResult ∘ iterate ∘ stepProperty` (property 6)
  - Ack soundness + completeness: Ack iff no property's `stepL` returned `Violated` (properties 7, 14)
  - Violation soundness + completeness: `PropertyResponse` iff some `stepL` returned `Violated` (properties 8, 15)
  - `stepProperty` faithfulness: halt iff `stepL` returned `Violated` (properties 3-4)
  - `dispatchIterResult` characterization: `nothing → Ack`, `just → PropertyResponse` (property 5)
  - Predicate table faithfulness: atom indices map to correct predicates (properties 8-9)
  - Signal cache correctness: hit/miss/decomposition (properties 10-13)

**4. Frame parsing (`parseDataFrame`)** — **REMOVED**

- **Status**: Dead code removed. All language bindings (Python, C++, Go) use binary FFI (`aletheia_send_frame` → `processFrameDirect`). The JSON data frame path (`parseDataFrame`, `parseRequest`, `Request.DataFrame`, `processStream`) has been eliminated. No proof obligation remains.

### Tier 2: Signal Extraction Correctness

**5. Signal extraction from real frames (`extractSignal`, `scaleExtracted`)** — **PROVEN** (algebraic correctness)

- **File**: `CAN/Encoding.agda:62-77`
- **What IS proven**:
  - Roundtrip — `extract(inject(v)) = v` for both byte orders and signedness (`extractSignal-injectSignal-roundtrip`)
  - Scaling algebraic correctness — `removeScaling(applyScaling(raw, f, o), f, o) ≡ just raw` when `f ≢ 0` (`removeScaling-applyScaling-exact` in `Encoding/Properties.agda`). `scaleExtracted` is definitionally `applyScaling raw (factor sig) (offset sig)`, so this covers it completely.
  - Scaling injectivity — `applyScaling raw₁ f o ≡ applyScaling raw₂ f o → raw₁ ≡ raw₂` (`applyScaling-injective`)
  - Field cancellation — `((x * f + o) - o) / f ≡ x` (`ℚ-cancel`)
  - Disjoint signal preservation — injecting at one position preserves extraction at physically disjoint positions, for all four byte-order combinations (`injectSignal-preserves-disjoint-bits-physical`)
- **What is NOT proven**: That `extractSignal` applied to a frame received from a CAN bus (not one we constructed) returns the value the sender intended. This requires the DBC signal layout to match the physical bus encoding — a real-world specification correspondence outside Agda's scope.

**6. Batch extraction correctness (`extractAllSignals`)** — **PROVEN**

- **File**: `CAN/BatchExtraction.agda`
- **Modules**: `CAN/Batch/Properties.agda`
- **What IS proven**:
  - Completeness — every signal produces exactly one entry across three partitions (`extractAll-complete`)
  - Value preservation — injecting multiple signals preserves extraction of disjoint signals (`injectAll-preserves-disjoint`)
  - Capstone — `validDBC-roundtrip`: for a validated DBC, injecting signal values and extracting them back returns the originals (composes DBC validation, disjointness, and encoding roundtrip)
- **What is NOT proven**: Same real-world correspondence as item 5 — the DBC must match the physical bus.

### Tier 3: FFI Boundary Trust

**7. MAlonzo constructor fidelity** — **TRUST BOUNDARY**

- **File**: `haskell-shim/src/AletheiaFFI.hs`
- **What it does**: `bytesToAgdaVec`, `C_constructor_26`, `C_Standard_10`, etc. manually construct MAlonzo internal types from raw C values.
- **Why it can't be proven**: MAlonzo constructor layout is a GHC implementation detail outside Agda's type system. No formal correspondence exists between the Haskell constructors and Agda's record definitions.
- **Mitigation**: (1) The Shakefile checks mangled function names at build time. (2) `haskell-shim/test/ConstructorTest.hs` is a smoke test that sends binary-constructed frames through `processFrameDirect` in a Streaming session and checks for expected ack/violation responses — catches constructor layout drift. Run: `cd haskell-shim && cabal test constructor-fidelity`.

**8. `unsafeCoerce` in AletheiaFFI.hs**

- **File**: `haskell-shim/src/AletheiaFFI.hs`
- **What it does**: Used 4 times to bridge MAlonzo's erased type parameters (proof fields erased at compile time).
- **Risk**: If the wrong type is coerced, the GHC runtime won't catch it (same representation). Type-safe by construction (MAlonzo erases proofs to unit), but not machine-verified.

### Tier 4: Lower Risk

**9. Response formatting (`formatResponse`)** — **PROVEN**

- **File**: `Protocol/ResponseFormat.agda`
- **Status**: ✅ Proven in `Protocol/ResponseFormat/Properties.agda`. Definitional equalities (refl) for each Response and PropertyResult constructor, establishing the exact JSON output structure. Covers Ack, Success, Error, ByteArray, DBCResponse, Violation, Satisfaction, and StreamComplete.

**10. Initial LTL state (`initProc`, `denot`)** — **PROVEN**

- **File**: `LTL/Coalgebra.agda`
- **Status**: ✅ Proven in `LTL/Coalgebra/Properties.agda`. The `initProc-correct` theorem establishes `denot table (initProc φ) ≡ mapLTL table φ` — the initial process state correctly represents the user's formula with atoms mapped through the predicate table. Combined with adequacy, this gives end-to-end soundness from formula specification to runtime verdict.

---

## Proof Coverage Summary

| Domain | Status | Key Gap |
|--------|--------|---------|
| LTL evaluation (`stepL`) | Proven sound | Assumes correct predicate table |
| DBC validation | Proven sound + complete | Individual checkers not proven |
| Signal encode/decode roundtrip | **Proven** | Real-world DBC-bus correspondence assumed |
| Signal scaling (`scaleExtracted`) | **Proven** | Roundtrip + injectivity via `applyScaling` |
| Batch extraction | **Proven** | Completeness + value preservation + capstone |
| DBC format/parse roundtrip | Proven | — |
| Binary FFI guards | **Proven** | — |
| Predicate table construction | **Proven** | — |
| Signal cache integrity | **Proven** | — |
| Streaming frame processing | **Proven** | Ack/violation iff, decomposition, 15 properties |
| Initial LTL state (`initProc`) | **Proven** | — |
| Response formatting | **Proven** | All constructors verified |
| FFI type construction | **Trust boundary** | Outside Agda's reach; smoke test guards |

## Recommended Priority

1. ~~**Tier 1, item 3**: `handleDataFrame` Streaming case~~ — ✅ **DONE** (commit `65c4080`)

2. ~~**Tier 1, item 1**: `mkPredTable` faithfulness~~ — ✅ **DONE** (this commit)

3. ~~**Tier 1, item 2**: Signal cache correctness~~ — ✅ **DONE** (this commit)

4. ~~**Tier 3, item 7**: MAlonzo constructor test~~ — ✅ **DONE** (this commit)

5. ~~**Tier 4, item 10**: `initProc` correctness~~ — ✅ **DONE**

6. ~~**Tier 4, item 9**: Response formatting correctness~~ — ✅ **DONE**

Items 1-6 are complete. All Tier 1, Tier 2, and Tier 4 gaps are closed. The only remaining items (7-8) are the MAlonzo FFI trust boundary, which is outside Agda's type system by nature and mitigated by build-time checks and smoke tests. All 64 Agda modules use `--safe`.

---

## Notes

### Existing proofs are all needed

Every proof listed in "What Is Proven" remains necessary:

- **Signal extraction roundtrip** — the only proof the encoding scheme is internally consistent. Without it, signal extraction code cannot be trusted even for self-constructed frames.
- **LTL JSON roundtrip** — formulas are sent as JSON from language bindings; this proves they survive serialization.
- **Protocol JSON schemas** — validates the JSON protocol contract between bindings and the Agda core.
- **DBC parser well-formedness** — proves parsed DBCs satisfy structural invariants that feed into the validation soundness chain.
- **Batch extraction completeness** — proves no signals are silently dropped during extraction.

### DBC validation covers CAN-FD

The validator works for both CAN 2.0B and CAN-FD. `checkDLCOutOfRange` uses `bytesToDlc` which accepts all CAN-FD payload sizes (12, 16, 20, 24, 32, 48, 64 bytes). `checkSignalExceedsDLC` validates signal bit ranges against `dlc * 8` where `dlc` is the byte count. The `ValidDBC` record's 9 conditions are all CAN-FD-aware. Soundness and completeness are proven for all 9 error checks.

### Remaining unproven items

The only unproven items (7-8) are the MAlonzo FFI trust boundary — constructor layout and `unsafeCoerce` usage in `AletheiaFFI.hs`. These are outside Agda's type system by nature: MAlonzo's internal representation is a GHC implementation detail. Mitigation is via build-time name checks and the `constructor-fidelity` smoke test. All items that can be proven in Agda have been proven.
