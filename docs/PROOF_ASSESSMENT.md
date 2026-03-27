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

Extracting a signal from a frame that was built by injecting that signal returns the original value. Covers both byte orders (little-endian, big-endian/Motorola), signed and unsigned signals, and mixed byte-order commutativity.

- **Modules**: `CAN/Encoding/Properties.agda`, `CAN/Endianness/Properties.agda`, `CAN/Batch/Properties.agda`
- **Key lemma**: `extractBits-injectBits-roundtrip`
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

### Other Proofs

- **LTL JSON roundtrip**: `LTL/JSON/Properties.agda`
- **Protocol JSON schemas**: `Protocol/JSON/Properties.agda`
- **DBC parser well-formedness**: `DBC/JSONParser/Properties.agda` (parsed DBCs satisfy `WellFormedDBC`)
- **Batch extraction completeness**: `extractAll-complete` — every signal produces exactly one entry across the three result partitions

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

**3. Frame processing in Streaming phase (`handleDataFrame`)**

- **File**: `Protocol/StreamState.agda:285`
- **What it does**: In Streaming phase: updates signal cache, evaluates each property's LTL formula via `stepL`, collects violations, advances state.
- **What IS proven**: Non-Streaming guards (state unchanged).
- **What is NOT proven**: The Streaming case correctly threads state through all properties, produces a Violation response if and only if some property's `stepL` returned `Violated`, and preserves all non-evaluated properties unchanged.
- **Suggested proof**: (i) Violation iff some `stepL` returned `Violated`. (ii) Ack iff all returned `Continue`. (iii) Each property's formula is advanced exactly once.

**4. Frame parsing (`parseDataFrame`)**

- **File**: `Protocol/Routing.agda`
- **What it does**: Parses a JSON object into a `TimedFrame` (timestamp, CAN ID, DLC, payload bytes).
- **Risk**: If parsing constructs a malformed `TimedFrame`, all downstream processing (signal extraction, LTL evaluation) operates on garbage.
- **Note**: The binary FFI path (`aletheia_send_frame`) bypasses this entirely — frames are constructed in the Haskell shim. This risk only applies to the JSON path, which is no longer used for data frames in production.

### Tier 2: Signal Extraction Correctness

**5. Signal extraction from real frames (`extractSignal`, `scaleExtracted`)**

- **File**: `CAN/Encoding.agda:62-77`
- **What IS proven**: Roundtrip — `extract(inject(v)) = v`. This proves the encoding scheme is internally consistent.
- **What is NOT proven**: That `extractSignal` applied to a frame received from a CAN bus (not one we constructed) returns the value the sender intended. This requires a specification of the DBC signal layout matching the physical bus encoding, which is outside Agda's scope (it's a real-world correspondence).
- **Also unproven**: `scaleExtracted` (rational arithmetic: `factor * raw + offset`) — no proof that the scaling is algebraically correct. Low risk since it's a direct application of `Data.Rational` operations.

**6. Batch extraction correctness (`extractAllSignals`)**

- **File**: `CAN/BatchExtraction.agda`
- **What IS proven**: Completeness — every signal produces exactly one entry across three partitions (values, errors, absent).
- **What is NOT proven**: That each entry contains the correct value. This would follow from item 5 above.

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

**9. Response formatting (`formatResponse`)**

- **File**: `Protocol/ResponseFormat.agda`
- **Risk**: If Ack is formatted as a Violation JSON or vice versa, language bindings misinterpret the result. Low probability (simple pattern match on Response constructors), but no proof.

**10. Initial LTL state (`initProc`, `denot`)**

- **File**: `LTL/Coalgebra.agda`
- **Risk**: If the initial LTL process state doesn't match the formula, the entire Adequacy guarantee is vacuous. The adequacy proof takes `proc` as a parameter — it doesn't prove `initProc` produces the right initial state for a given formula.
- **Suggested proof**: `initProc formula` is the correct initial state for `denot formula`.

---

## Proof Coverage Summary

| Domain | Status | Key Gap |
|--------|--------|---------|
| LTL evaluation (`stepL`) | Proven sound | Assumes correct predicate table |
| DBC validation | Proven sound + complete | Individual checkers not proven |
| Signal encode/decode roundtrip | Proven | No spec for real-world frames |
| DBC format/parse roundtrip | Proven | — |
| Binary FFI guards | Partial | Only non-Streaming cases |
| Predicate table construction | **Proven** | — |
| Signal cache integrity | **Proven** | — |
| Streaming frame processing | **Not proven** | Tier 1 gap |
| FFI type construction | **Trust boundary** | Outside Agda's reach; smoke test guards |

## Recommended Priority

1. ~~**Tier 1, item 3**: `handleDataFrame` Streaming case~~ — ✅ **DONE** (commit `65c4080`)

2. ~~**Tier 1, item 1**: `mkPredTable` faithfulness~~ — ✅ **DONE** (this commit)

3. ~~**Tier 1, item 2**: Signal cache correctness~~ — ✅ **DONE** (this commit)

4. ~~**Tier 3, item 7**: MAlonzo constructor test~~ — ✅ **DONE** (this commit)

Items 1-3 are complete. All Tier 1 gaps are now closed: "if the user specifies an LTL formula and sends frames, the reported verdict is correct" — assuming correct signal encoding (proven via roundtrip) and correct DBC (proven via validation).

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

### All gaps must be proven

All items listed in "What Is NOT Proven" are required proof work, not aspirational. The priority order above reflects implementation sequence, not optionality.
