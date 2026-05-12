# R20 Review Round — Findings

**Branch:** `review-r20` (forked from `main` at `2e79ed8` 2026-05-12 post-R19 merge + tidy).
**Started:** 2026-05-12.
**Scope:** All code, proofs, documentation. Per AGENTS.md — universal rules + every per-language category + system-level review + CI/CD + docs.

## Round metadata

- **Step 0 carry-over** read from `DEFERRALS.md` + in-source `DEFER` comments + memory files `project_review_round{18,19}.md`. Permanently-deferred / NO-FIX items below not to be re-raised without new evidence.
- **Step 1 agents** (12 in parallel): Agda A/B/C, Go A/B, C++ A/B, Python A/B, CI/CD A, Docs A/B.
- **Step 2 agents** (4 in parallel): Agda D, Go System, C++ System, Python System.
- **Single tracking document** per `feedback_review_round_dispositions.md` rule 3.

## Carry-over (NOT to be re-raised without new evidence)

From `DEFERRALS.md` (2026-05-10 last updated):

### Permanently deferred
- **D1** — `mkPredTable` atom index `ℕ → Fin` (`StreamState/Internals.agda:91`) — MAlonzo Peano `Fin` compilation cost dominates Stream-LTL hot path; ~40-line in-source caution block documents the trade-off.

### NO-FIX (per prior rounds)
- **R5-B1 / R6-B7.1** — `bitLength` admits 0 (`CAN/Signal.agda:22`) — validator + `physicalGate` defend in depth.
- **R5-A11** — `M.map` closure on cache fallback (`SignalPredicate/Evaluation.agda:84,98`) — micro-opt, cache hits only.
- **R5-C2** — Validation issue codes lack `validation_` prefix — namespaced by response structure.
- **R6-B7.2** — Metric `window`/`startTime` raw ℕ (`LTL/Syntax.agda:45`) — dimensionally distinct from `Timestamp μs`.
- **R6-B7.3** — `CachedSignal.lastObserved` unrefined ℕ — internal bookkeeping, comparison sites unwrap via `timestampℕ`.
- **R6-B7.4** — `PropertyState.index : ℕ vs Fin` — cold-path construction + JSON-format need for ℕ.
- **R6-B8.1** — SimplifySound truth-table helpers repetitive — Path G `with` scrutinee-abstraction limitation.
- **R6-B8.2** — SoundOps `sound-and`/`sound-or` 380 lines each — generic combinator would be more code.
- **R6-B9.1** — `classifyStepResult` Satisfied stability informal — non-trivial proof effort, safety already covered.
- **R6-P1.1** — `_client.py` 1030 lines marginal overshoot — already decomposed (currently 995 lines, see PY-A-6.1).

### R19 carry-over RE-DEFER
- **R19-CARRY-1 final** — Bool fast-path for `mkPredTable` post `@0`-erasure — 4 distinct approaches all hit Agda's `with ... in eq` outer-abstraction barrier. Future revisit needs either Agda upstream fix or `Dec`-dispatch elimination. Lesson in `feedback_with_in_eq_outer_abstraction_barrier.md`.

### In-source DEFER (do not re-raise without new info)
- `src/Aletheia/CAN/Endianness.agda:26-31` — DEFER-stdlib-mandate Cat 29.
- `src/Aletheia/CAN/Encoding/Properties/Arithmetic/Rational.agda:29-36` — DEFER-stdlib-mandate Cat 29.
- `src/Aletheia/Data/BitVec/Conversion.agda:12-19` — DEFER-stdlib-mandate Cat 29.
- `src/Aletheia/Protocol/StreamState/Internals.agda:91-97` — D1 in-source caution block.
- `src/Aletheia/CAN/Encoding.agda:102-121` — Bool fast-path `with...in eq` barrier (R19-CARRY-1).
- `go/aletheia/json.go:45-53` — GO-B-25.2 `serializeDataFrame` sync.Pool deferral (mock-only path).

---

## Coverage

17 agents launched per AGENTS.md mapping:

| Step | Agent | Scope | Status |
|---|---|---|---|
| 1 | Agda A | Hygiene (cats 1/2/4/16/21/28/29 + G-A1/A8) | ✅ done |
| 1 | Agda B | Semantics (cats 7/8/9/18/20/22/23/24/25/26 + G-A2-A12) | ✅ done |
| 1 | Agda C | Cross-file (cats 3/5/6/27 + G-A14/A15/A16) | ✅ done |
| 1 | Go A | Hygiene & Style (cats 1-6, 30) | ✅ done |
| 1 | Go B | Correctness & Runtime (cats 7-14, 23-29, 33) | ✅ done |
| 1 | C++ A | Hygiene & Style (cats 1-6, 30) | ✅ done |
| 1 | C++ B | Correctness & Runtime (cats 7-14, 23-29, 33) | ✅ done |
| 1 | Python A | Hygiene & Style (cats 1-6, 27, 28, 32, 33) | ✅ done |
| 1 | Python B | Correctness & Runtime (cats 7-14, 23-26, 29-30, 34) | ✅ done |
| 1 | CI/CD A | Workflows, cache, perms, isolation, release (cats 1-5) | ✅ done |
| 1 | Docs A | Hygiene (cats 1-9) | ✅ done |
| 1 | Docs B | Deep (cats 10-22) | ✅ done |
| 2 | Agda D | Specification + Architecture (cats 10-15, 17, 19, 30-32 + G-A) | ✅ done |
| 2 | Go System | Architecture + Specification (cats 15-22, 31-32) | ✅ done |
| 2 | C++ System | Architecture + Specification (cats 15-22, 31-32) | ✅ done |
| 2 | Python System | Architecture + Specification (cats 15-22, 31) | ✅ done |

**Approximate finding counts** (per agent self-report):
- Agda A: 33 — Agda B: ~50 — Agda C: 30
- Go A: ~35 — Go B: 14
- C++ A: ~40 — C++ B: ~30
- Python A: ~30 — Python B: ~20
- CI/CD A: ~22 — Docs A: ~30 — Docs B: ~50
- Agda D: 30 — Go System: ~35 — C++ System: ~35 — Python System: ~30
- **Total raw findings: ~514** (some overlap across step-1 and step-2 agents; dedup is part of clustering).

---

# Findings

## Agda

### Agda Agent A — Hygiene

#### Coverage
- Files scanned: ~50 modules (Main + Main/{JSON,Binary}, Protocol/{Handlers,Routing,Message,StreamState,StreamState/Internals,ResponseFormat,Adequacy/StreamingWarm,JSON/{Parse,Types},FrameProcessor/Properties/Step}, Limits, Error, Prelude, LTL/{Coalgebra,JSON,JSON/Format,Syntax}, Trace/{CANTrace,Time}, CAN/{Frame,DLC,DLC/Properties,Constants,Encoding,SignalExtraction,BatchExtraction,BatchFrameBuilding}, DBC/{Identifier,Formatter/Bounded,Formatter/WellFormed,TextParser/WellFormed}, Data/BitVec/Conversion, plus headers/structure across all 247 modules).
- Categories covered: 1 / 2 / 4 / 16 / 21 / 28 / 29.

#### Findings

##### Cat 1 — Dead code

1. `[ ]` AGDA-A-1.1 — `src/Aletheia/Main.agda:101-118` — Public facade `Aletheia.Main` re-exports `Aletheia.Protocol.Message` but omits ctors shipped after this facade was last touched: `SendFrame` (R19 P2 cluster 18, `a8ade07`), `ParseDBCText` (Track B.3.e), `FormatDBCText` (Track E.10), `DBCTextResponse`, `ParsedDBCResponse`. External callers using the facade see a stale subset.
2. `[ ]` AGDA-A-1.2 — `src/Aletheia/CAN/BatchFrameBuilding.agda:79-100` — `LookupStrategy` record + three generic consumers parameterised over key type `K` but only ever instantiated with `indexStrategy : LookupStrategy ℕ`. YAGNI dead architectural overhead.
3. `[ ]` AGDA-A-1.3 — `src/Aletheia/Protocol/Handlers.agda:112-125` ↔ `src/Aletheia/Protocol/Handlers/ParseDBCText.agda:58-72` — `signalsBound` + `firstDBCOverBound` cardinality-bound helpers duplicated; comment documents the cycle-avoidance rationale but a sibling helper module would close the drift risk.
4. `[ ]` AGDA-A-1.4 — `src/Aletheia/Protocol/JSON/Parse.agda:41` — `digitToNat _ = 0` catch-all; only callers come through `parseNatural` filtering via `some (satisfy isDigit)`.
5. `[ ]` AGDA-A-1.5 — `src/Aletheia/Protocol/JSON/Parse.agda:115-118` — `power10 (suc n) ... | zero` "unreachable" clause.
6. `[ ]` AGDA-A-1.6 — `src/Aletheia/Protocol/JSON/Parse.agda:135` — `buildNumber n (just fracChars) ... | zero` unreachable.
7. `[ ]` AGDA-A-1.7 — `src/Aletheia/Protocol/JSON/Parse.agda:145` — `applyExp q (just -[1+ e ]) ... | zero = q` unreachable.
8. `[ ]` AGDA-A-1.8 — `src/Aletheia/CAN/BatchExtraction.agda:84` — `resultToString _ (Success _) = ""` unreachable.
9. `[ ]` AGDA-A-1.9 — `src/Aletheia/CAN/BatchExtraction.agda:136` — `resultToCode _ (Success _) = ExtractionFailed` structurally misleading.
10. `[ ]` AGDA-A-1.10 — `src/Aletheia/Trace/Time.agda:38, 40, 41` — `ns`, `ms`, `s` constructors "Reserved for future use". Borderline; user adjudication needed.
11. `[ ]` AGDA-A-1.11 — `src/Aletheia/CAN/DLC.agda:32` — `dlcToBytes n = n` total-coverage catch-all returns input value (wrong if reached).

##### Cat 2 — Magic numbers

12. `[ ]` AGDA-A-2.1 — `src/Aletheia/Protocol/Routing.agda:41-42` — `byte-bound = 256` local; should be lifted to `Aletheia.Limits` or `CAN.Constants`.
13. `[ ]` AGDA-A-2.2 — `src/Aletheia/CAN/Constants.agda:13-17` — `standard-can-id-max = 2048` / `extended-can-id-max = 536870912` as literals; prefer `2 ^ 11` / `2 ^ 29`.
14. `[ ]` AGDA-A-2.3 — `src/Aletheia/CAN/DLC/Properties.agda:33-104` — Hardcoded 16 explicit DLC cases. Cross-reference R19 closed adjudication.
15. `[ ]` AGDA-A-2.4 — `src/Aletheia/CAN/DLC.agda:50-54, 97-101` — Literal byte counts (20, 24, 32, 48, 64) duplicated in `bytesToDlc` and `bytesToValidDLC`.

##### Cat 4 — Comments

16. `[ ]` AGDA-A-4.1 — `src/Aletheia/DBC/Identifier.agda:6-13` — Closed-work historical narrative (Pre-3d.4 / After 3d.4) is stale.
17. `[ ]` AGDA-A-4.2 — `src/Aletheia/CAN/Encoding.agda:118-121` — In-source post-Round-8 benchmark numbers; stale stamps.
18. `[ ]` AGDA-A-4.3 — `src/Aletheia/CAN/Encoding.agda:82-88` — `extractSignal`'s `nothing`-branch reachability comment; tighten with named caller.
19. `[ ]` AGDA-A-4.4 — `src/Aletheia/Protocol/StreamState/Internals.agda:136-188` — 50-line stale-cache narrative with stale date.
20. `[ ]` AGDA-A-4.5 — `src/Aletheia/CAN/BatchFrameBuilding.agda:34-48` — Header refers to `physicallyDisjoint?` — verify still exists.
21. `[ ]` AGDA-A-4.6 — `src/Aletheia/Protocol/Handlers.agda:11-12` — Line-range citation (`StreamState.agda:62-72`) may drift.
22. `[ ]` AGDA-A-4.7 — `src/Aletheia/LTL/JSON/Format.agda:63` — Header-level invariant about formatter never producing 'never'/'implies' belongs in module docstring.

##### Cat 16 — Performance

23. `[ ]` AGDA-A-16.1 — `src/Aletheia/Protocol/Handlers.agda:114, 119, 123, 184` — `length` re-traversed in inequality check AND in `just` argument; bind once.
24. `[ ]` AGDA-A-16.2 — `src/Aletheia/CAN/BatchExtraction.agda:91-92` — `extractAllSignalsFromMessage` `foldr combinePartitioned` is O(N²) in list ops.
25. `[ ]` AGDA-A-16.3 — `src/Aletheia/CAN/SignalExtraction.agda:48-50` — `matchMuxValue` rebuilds `(+ v) / 1` per call; precompute once.
26. `[ ]` AGDA-A-16.4 — `src/Aletheia/Prelude.agda:70-86` — `lookupByKey` cold-path Dec allocation; verify R19 P2 cluster 18 SendFrame additions didn't push onto per-frame path.

##### Cat 21 — Safety flag audit

27. `[ ]` AGDA-A-21 — **Clean.** 247 modules; 246 `--safe --without-K` (or `--safe --without-K --no-main` for 4 Main-family modules); 1 allowlisted `--without-K`-only (`Substrate.Unsafe`). Audit clean.

##### Cat 28 — Pragma abuse

28. `[ ]` AGDA-A-28 — **Clean.** 11 hits across codebase: 10 `NOINLINE` on FFI export functions (`Main/Binary.agda` + `Main/JSON.agda`) — legitimate per MAlonzo export discoverability. 1 comment-only reference (`DBC/Identifier.agda:162`). Audit clean.

##### Cat 29 — Instance discipline

29. `[ ]` AGDA-A-29 — **Clean.** DEFER blocks verified at 3 sites: `Endianness.agda:26-32`, `Data/BitVec/Conversion.agda:12-20`, `Encoding/Properties/Arithmetic/Rational.agda:29-36`. Stdlib `_mod_`/`_%_` mandate with explicit `{{m^n≢0 …}}` / `{{m*n≢0 …}}` witnesses at every call site. Audit clean.

##### G-A1 — Import hygiene

30. `[ ]` AGDA-A-G-A1.1 — `src/Aletheia/Protocol/Handlers.agda:30, 32, 37, 40, 41` — Unused names in `using (...)` lists: `formatIssuesText`, `SignalPredicate`/`SignalCache`, `lookupString`/`getObject`/`lookupRational`, `Timestamp`, `TimedFrame`.
31. `[ ]` AGDA-A-G-A1.2 — `src/Aletheia/Protocol/Routing.agda:14, 23` — `Bool`/`T`/`true`/`false`/`if_then_else_` imported but unused (only `ifᵀ_then_else_` from Prelude is used); `JObject` imported, never referenced.

##### G-A8 — Flag hygiene

32. `[ ]` AGDA-A-G-A8 — **Clean.** All 247 modules use correct flag combinations.

---

### Agda Agent B — Semantics

#### Coverage
Files scanned (depth): `Protocol/StreamState/{Internals,Types}.agda`, `Protocol/StreamState.agda`, `Protocol/FrameProcessor/Properties/{Bounded,Step,Cache,Handlers,Monotonic}.agda`, `Protocol/Handlers.agda`, `Protocol/Adequacy/StreamingWarm.agda`, `LTL/{Syntax,Coalgebra,Simplify,SimplifySound,Adequacy}.agda`, `LTL/Coalgebra/Properties.agda`, `LTL/Adequacy/{Agreement,SoundOps}.agda`, `LTL/SignalPredicate/Cache.agda`, `LTL/SignalPredicate/Cache/Properties.agda`, `DBC/{Validity,Validator,Identifier}.agda`, `DBC/Validity/{Theorem,Combinators,ErrorChecks,WarningChecks}.agda`, `DBC/Validator/Checks.agda`, `DBC/Formatter/{WellFormed,Bounded}.agda`, `DBC/TextParser/Format.agda`, `CAN/{Frame,Signal,DLC,Encoding,Endianness}.agda`, `Data/BitVec/Conversion.agda`, `Trace/{Time,CANTrace}.agda`, `Limits.agda`, `Error.agda`, `Prelude.agda`, `Parser/Combinators.agda`. Pointer-scanned remainder of 247 modules.

#### Findings

##### Cat 7 — Type tightness

33. `[ ]` AGDA-B-7.1 — `src/Aletheia/CAN/DLC.agda:21` `dlcToBytes : ℕ → ℕ` — accepts any ℕ; contract is "DLC code in 0..15"; tighten to `DLC → ℕ` (already exists as `dlcBytes`).
34. `[ ]` AGDA-B-7.2 — `src/Aletheia/CAN/DLC.agda:37` `bytesToDlc : ℕ → Maybe ℕ` — `bytesToValidDLC` already returns validated `Maybe DLC`; audit callers and retire bare-ℕ form.
35. `[ ]` AGDA-B-7.3 — `src/Aletheia/Parser/Combinators.agda:27` `Position` `line column : ℕ` — both positive by construction; cascade cost > benefit. FLAG only.
36. `[ ]` AGDA-B-7.4 — `src/Aletheia/LTL/Syntax.agda:82` `atomCount` returns ≥ 1 always; could be ℕ⁺. FLAG only.
37. `[ ]` AGDA-B-7.5 — `src/Aletheia/LTL/Coalgebra.agda:121` `metricElapsed` — first `ℕ` is `startTime`; wrap in `StartTime` newtype.
38. `[ ]` AGDA-B-7.6 — `src/Aletheia/Limits.agda:88+` `max-*-*` — all positive; `MaxBound` newtype with `@0` positivity proof. FLAG only.
39. `[ ]` AGDA-B-7.7 — `src/Aletheia/CAN/Endianness.agda:80` `lookupSafe` defaults to 0 on OOB; `Fin n` would make dead default unrepresentable (different cost calculus than D1).
40. `[ ]` AGDA-B-7.8 — `src/Aletheia/LTL/Coalgebra.agda:91,101` `combineAnd/combineOr` return `StepResult LTLProc` no atom-bound; `BoundedStepResult b` record candidate.

##### Cat 8 — Proof simplification

41. `[ ]` AGDA-B-8.1 — `src/Aletheia/Protocol/FrameProcessor/Properties/Bounded.agda:349-388` `indexHelper-bound` — 6 binary-ctor clauses spell same pattern; `binary-bound-step` helper opportunity (~40 LOC).
42. `[ ]` AGDA-B-8.2 — `Bounded.agda:320-346` `indexHelper-mono` — same 6×repeated pattern; mirror refactor (~30 LOC).
43. `[ ]` AGDA-B-8.3 — `Bounded.agda:297-317` `AllBelow-mono` — `binary-allbelow-mono` helper (~25 LOC).
44. `[ ]` AGDA-B-8.4 — `LTL/Coalgebra/Properties.agda:304-347` `finalize-empty-equiv` — 6 And cases + 6 Or cases identical pattern; centralise via 3-valued helper.
45. `[ ]` AGDA-B-8.5 — `LTL/Adequacy.agda:528-562` — Always/Eventually/Until/Release follow identical `subst (...) (sym ...)` pattern; extract `adequacy-via-decomp` (~40 LOC).
46. `[ ]` AGDA-B-8.6 — `Cache.agda:152-292` `updateSignals-{monotone,timestamps≤,coherent-split}` — same `with extractTruthValue` pattern; `step-on-extraction` helper (~25 LOC).
47. `[ ]` AGDA-B-8.7 — `LTL/Adequacy.agda:91-144` `runL-{and,or}-decomp` — 7 chained `rewrite` cases each; `combine-decomp` parametric helper (~30 LOC).
48. `[ ]` AGDA-B-8.8 — `LTL/Adequacy.agda` `runL-metric-*-decomp` — 4 metric variants on top of 4 unbounded; `runL-metric-decomp-via` parametric helper (~80-100 LOC).
49. `[ ]` AGDA-B-8.9 — `WarningChecks.agda:92-104` `checkGlobalNamePair-allW` — private `go` recursion collapses to `All.map` + small combinator.
50. `[ ]` AGDA-B-8.10 — `Bounded.agda:500-516` `simplify-bound` — 12 identity clauses; collapse to 2 + `simplify-identity-bound` lemma.
51. `[ ]` AGDA-B-8.11 — `Bounded.agda:483-497` `absorb-bound` — 12 identity + 2 dispatcher; same pattern as 8.10.
52. `[ ]` AGDA-B-8.12 — `Adequacy/Agreement.agda:269-298` — same wrapper as Cat 8.5.

##### Cat 9 — Proof soundness

53. `[ ]` AGDA-B-9.1 — `Protocol/Adequacy/StreamingWarm.agda` — no top-level `streaming-pipeline-sound : Monotonic σ → AllObserved … → runL = ⟦ ⟧ₘ` composition. Users wire 4-layer chain manually.
54. `[ ]` AGDA-B-9.2 — `StreamState/Internals.agda:238` `classifyStepResult Satisfied prop = advance prop` — stability informal; per R6-B9.1 NO-FIX but new angle: `stepL-satisfied-stable` lemma is now-feasible given closed Adequacy chain.
55. `[ ]` AGDA-B-9.3 — `Adequacy/Agreement.agda:240` `agreement` requires `TwoValued table`; production callers can't discharge. Downgrade to `private` OR add WARNING docstring on theorem signature.
56. `[ ]` AGDA-B-9.4 — `DBC/Validity.agda:82` `MuxAcyclic sigs presence = walkMux (length sigs) sigs presence ≡ true` — fuel-based; verify `walkMux` enforces visit-set-shrinking, not just fuel-decreasing.
57. `[ ]` AGDA-B-9.5 — `LTL/SimplifySound.Composition` — missing headline `simplify-stepL-correct` composition: `runL table (simplify proc) σ ≡ runL table proc σ × AllBelow b proc → AllBelow b (simplify proc)`.

##### Cat 18 — Dead-branch provability

58. `[ ]` AGDA-B-18.1 — `Endianness.agda:81` `lookupSafe zero _ _ = 0` — `lookupSafe-total` lemma analogous to `mkPredTable-bounded` would close soundness gap.
59. `[ ]` AGDA-B-18.2 — `CAN/DLC.agda:32` `dlcToBytes n = n` catch-all — split into explicit identity for 0..8 + validated invariant clause.
60. `[ ]` AGDA-B-18.3 — `CAN/Encoding.agda:130` `injectHelper` `with <? 2 ^ bitLength` `no _ = nothing` — reachable post-R19 cluster D `@0`; tied to AGDA-B-26.5 RE-DEFER scope.

##### Cat 20 — Termination metric hygiene

61. `[ ]` AGDA-B-20.1 — `Parser/Combinators.agda:176` `manyHelper` — `sameLengthᵇ` no-progress guard could be replaced by direct length comparison.
62. `[ ]` AGDA-B-20.2 — `Validator.walkMux` — fuel-based; tied to AGDA-B-9.4.

##### Cat 22 — Irrelevance

63. `[ ]` AGDA-B-22.1 — `DBC/Formatter/WellFormed.agda:41-114` — `WellFormedSignalDef`/`WellFormedSignal`/`WellFormedMessage`/`WellFormedMessageRT`/`WellFormedDBC`/`WellFormedDBCRT` records — fields propositional witnesses; `.(…)` irrelevance candidate.
64. `[ ]` AGDA-B-22.2 — `DBC/Formatter/WellFormed.agda:63-73` — `PhysicallyValid` data ctors carry 4 hypothesis fields for BE; irrelevance candidate.
65. `[ ]` AGDA-B-22.3 — `DBC/Validity.agda:101-127` — `ValidDBC` record — 8 conjunction fields proof-only; verify relevance not load-bearing.
66. `[ ]` AGDA-B-22.4 — `TimedFrame.dlcValid : .(payloadSize ≡ ...)` — worked example; no finding.

##### Cat 23 — Erasure @0

67. `[ ]` AGDA-B-23.1 — `DBC/Formatter/WellFormed.agda:43-44` `startBit-bound`/`bitLength-bound` — proof fields used only at proof time; `@0` candidate.
68. `[ ]` AGDA-B-23.2 — `DBC/Formatter/WellFormed.agda:105` `WellFormedDBC.messages-wf` — proof field, no `@0`. Candidate per AGDA-B-22.1.

##### Cat 24 — Pattern coverage & clause order

69. `[ ]` AGDA-B-24.1 — `LTL/Simplify.agda:81-82` `_≡ᵇ-proc_` catch-all — silent-false drift hazard on new ctor; add `_≡ᵇ-proc_-refl` coverage lemma.
70. `[ ]` AGDA-B-24.2 — `LTL/Simplify.agda:110-111` `absorb` catch-all — proof-relevant; lift to explicit 11 non-absorbed ctors.
71. `[ ]` AGDA-B-24.3 — `LTL/Simplify.agda:121-122` `simplify` catch-all — same as 24.2.
72. `[ ]` AGDA-B-24.4 — `CAN/DLC.agda:32` — tied to AGDA-B-7.1.

##### Cat 25 — Universe level hygiene

73. `[ ]` AGDA-B-25.1 — `DBC/TextParser/Format.agda:86` `Format : Set → Set₁` — `Set₁` bump documented + intentional. No action.

##### Cat 26 — Equality discipline

74. `[ ]` AGDA-B-26.1 — `DBC/Validator/Checks.agda:44,48` — Dec uses on parse-time validator; acceptable. No finding.
75. `[ ]` AGDA-B-26.2 — `Prelude.lookupByKey` — cold-path; documented DEFER. No finding.
76. `[ ]` AGDA-B-26.3 — `CAN/Encoding.agda:128` `injectHelper` Dec on frame-build hot path — R19-CARRY-1 RE-DEFER. No new finding.

##### G-A guideline findings

77. `[ ]` AGDA-B-GA2.1 — `Cache/Properties.agda:80-91` `lookupEntries-updateEntries-miss` — chained `rewrite ... | ≡csᵇ-refl-eq` is textbook G-A2 example.
78. `[ ]` AGDA-B-GA2.2 — `Coalgebra/Properties.agda` `finalize-empty-equiv` — small-goal `rewrite sym ih` chains acceptable per G-A2.
79. `[ ]` AGDA-B-GA3.1 — Surveyed reviewed modules; all `with` scrutinee+eq pairs use modern `in eq` syntax. No finding.
80. `[ ]` AGDA-B-GA9.1 — `CAN/Encoding.agda:122-151` `injectHelper` canonical where-block on runtime path; R19 cluster D `with...in eq` barrier blocks promotion.

---

### Agda Agent C — Cross-file comparison

#### Coverage
Files compared: `Error.agda`, `Protocol/Message.agda`, `Protocol/Routing.agda`, `Protocol/ResponseFormat.agda`, `Main.agda`, `Main/Binary.agda`, `Limits.agda`, `Prelude.agda`, `Parser/Combinators.agda`, `DBC/JSONParser.agda`, `DBC/Formatter.agda`, `DBC/TextParser.agda`, `DBC/TextFormatter.agda`, `DBC/TextFormatter/Emitter.agda`, `DBC/TextParser/Lexer.agda`, `Protocol/JSON.agda`, `Protocol/JSON/{Types,Lookup,Format,Parse}.agda`, `JSON.agda`, `LTL/JSON.agda`, `Trace/CANTrace.agda`, `DBC/Types.agda` (IssueCode), `DBC/Validity/Combinators.agda`, `DBC/Validator/Formatting.agda`, plus grep for `_++_` / `_≟_` / `InContext` / `dispatch*Table` / `parseObjectList` sites.

#### Findings

##### Cat 3 — Naming

81. `[ ]` AGDA-C-3.1 — `Error.agda:64,147,181,221,285` vs `:381` — Five per-ADT context-wrapping ctors `InContext`, top-level `Error` uses `WithContext`. Unify.
82. `[ ]` AGDA-C-3.2 — `Protocol/Message.agda:83-116` — `Response` ctor naming inconsistent: unsuffixed `Success`/`Error`/`Ack`/`Complete` vs `*Response` suffix on 6 others.
83. `[ ]` AGDA-C-3.3 — `Error.agda:373` vs `CANTrace.agda:104` vs `Message.agda:88` — `Error` overloaded 3 ways; `Main.agda` renames on re-export but latent for other importers. Rename at definition site.
84. `[ ]` AGDA-C-3.4 — `Error.agda:30,211,34,212,217-220` — `MissingField` mixes generic-by-string-key (`ParseError`) vs nullary-specific (`RouteError`); also inside `ParseError`.
85. `[ ]` AGDA-C-3.5 — `DBC/TextFormatter/Emitter.agda:96,102,112,116` — Hand-rolled show family asymmetric: `showNat-chars` / `showInt-chars` vs `showℕ-dec-chars` / `showℤ-dec-chars`.
86. `[ ]` AGDA-C-3.6 — `DBC/Formatter.agda:72-` vs `DBC/TextFormatter/Emitter.agda` / `TextFormatter/SignalGroups.agda:52,63,78` — JSON `format*` vs DBC text `emit*` prefix; parse side uses `parse*` for both. Inconsistent.
87. `[ ]` AGDA-C-3.7 — `DBC/TextFormatter/Emitter.agda:31` vs `DBC/TextParser/Lexer.agda:29` — Paired primitive modules `Emitter` vs `Lexer` asymmetric naming.
88. `[ ]` AGDA-C-3.8 — `Prelude.agda:38` vs `Main/Binary.agda:49` — Two different rename targets for `Data.Sum`: `mapₑ` (Prelude) vs `bimapₑ` (Main/Binary). Centralise.

##### Cat 5 — Error messages

89. `[ ]` AGDA-C-5.1 — `Error.agda:84-89` — `ExtCANIdOutOfRange`/`StdCANIdOutOfRange`/`DefaultCANIdOutOfRange` — three ctors, three wire codes; fold into `Error.InputBoundExceeded` with `BoundKind.CANIdStandard/CANIdExtended`.
90. `[ ]` AGDA-C-5.2 — `DBC/JSONParser.agda:121,130` — `InvalidPresence` misused for non-presence type-mismatch errors; introduce `NotANumber` or generalise.
91. `[ ]` AGDA-C-5.3 — `Error.agda:73,225` — `MissingField` / `RouteMissingField` emit byte-identical format strings. After AGDA-C-3.4 unification, becomes Cat 6 redundancy.
92. `[ ]` AGDA-C-5.4 — `Error.agda:157,189` — Asymmetric quoting: `BitExtractionFailed reason` no-quotes vs `InjectionFailed n` quoted. Pick one.
93. `[ ]` AGDA-C-5.5 — `Error.agda:64,147,181,221,285,381` — Six context-wrapping clauses emit same format `ctx ++ₛ ": " ++ₛ formatXError inner`. After AGDA-C-3.1 unification, one line.
94. `[ ]` AGDA-C-5.6 — `Error.agda:323-339` (DispatchError) — only ADT missing `InContext` ctor; document or add.
95. `[ ]` AGDA-C-5.7 — `DBC/Types.agda:330-351` — `IssueCode` lives in `DBC.Types` not `Aletheia.Error`; two parallel error systems for same architectural role.

##### Cat 6 — Redundant patterns

96. `[ ]` AGDA-C-6.1 — `Protocol/Routing.agda:86-89,141-144,157-160` — Three `try*DBC*` parsers share lookup-`"dbc"`-then-ctor shape; combinator `withRequiredObjectField` generalises (incl. `tryParseDBCText`).
97. `[ ]` AGDA-C-6.2 — `DBC/JSONParser.agda:290-297` vs `:195-202` — `parseSignalList` hand-rolled, `parseObjectList` generic; generalise to `parseObjectListIndexed`.
98. `[ ]` AGDA-C-6.3 — `DBC/JSONParser.agda:285` vs `:202` — `parseSignalList` reports `InContext context (NotAnObject ...)` (depth 2); `parseObjectList` reports `NotAnObject` (depth 1). Inconsistent.
99. `[ ]` AGDA-C-6.4 — `DBC/JSONParser.agda:464-486, 504-513, 522-542, 551-...` — 4 parsers dispatch on `kind` discriminator via if-then-else chains; extract dispatch-table pattern.
100. `[ ]` AGDA-C-6.5 — `DBC/JSONParser.agda` — 57× `require (MissingField "X") (lookup* "X" obj) >>= …` pattern; analogous helpers needed beyond `lookupDecRat`.
101. `[ ]` AGDA-C-6.6 — `Protocol/JSON/Format.agda:56-60,66-69` — `formatJSONList` + `formatFields` + `Validator/Formatting.agda:35-38` `formatIssuesText` all reimplement comma/`"; "`-separated rendering; `intersperse` generic.
102. `[ ]` AGDA-C-6.7 — `Protocol/JSON/Format.agda:55,61` — Whitespace inconsistency `++ₛ"]"` vs `++ₛ "\""`.

##### Cat 27 — Stdlib coverage

103. `[ ]` AGDA-C-27.1 — `Parser/Combinators.agda:165-169` `sameLengthᵇ` — hand-rolled; could be `length xs ≡ᵇ length ys`.
104. `[ ]` AGDA-C-27.2 — `Parser/Combinators.agda:128-133` `elem` — hand-rolled; `Data.Bool.ListAction.any` covers it.
105. `[ ]` AGDA-C-27.3 — `DBC/JSONParser.agda:105-106` `_≟-LC_ = ListProps.≡-dec _≟ᶜ_` — uses hyphen separator instead of subscript convention.

##### G-A14..A16 — guideline findings

106. `[ ]` AGDA-C-G-A14.1 — `Trace/CANTrace.agda:102-105` — `TraceEvent.Error` is the CAN-bus error frame, not parse error; rename (`ErrorFrame`?) to untie 3-way clash.
107. `[ ]` AGDA-C-G-A15.1 — `DBC/JSONParser.agda:464-486` — `parseCommentTarget` combinator-first form via dispatch table.
108. `[ ]` AGDA-C-G-A16.1 — Stdlib's `Data.List.intercalate`/`intersperse` used nowhere; multiple formatter modules use explicit foldr+++. (See Cat 6.6.)

##### Cross-file Cat 1/4 findings

109. `[ ]` AGDA-C-G-A1.1 — `Main.agda:101-118` — Main facade misses 3 recent `StreamCommand` ctors (`SendFrame`, `ParseDBCText`, `FormatDBCText`) + 2 Response ctors. (Cross-references AGDA-A-1.1.)
110. `[ ]` AGDA-C-4.1 — `Limits.agda:15-16` — Docstring "InputBoundExceeded constructors (ParseError, DBCTextParseError, FrameError)" stale post-R19 cluster 14 consolidation.
111. `[ ]` AGDA-C-4.2 — `Protocol/Message.agda:6-7` — Docstring lists 4 `StreamCommand` ctors vs actual 10.

---

## Go

### Go Agent A — Hygiene & Style

#### Coverage
Files scanned (source, non-test): `go/aletheia/{backend.go, ffi.go, ffi_nocgo.go, mock.go, client.go, types.go, dbc.go, *_string.go (6 generated), doc.go, enrich.go, error.go, json.go, limits.go, loader.go, ltl.go, result.go, yaml.go, check.go}`; `go/benchmarks/main.go`; `go/excel/excel.go`. Tools: `gofmt -l` clean, `go vet` clean, `CGO_ENABLED=0 go build` RC=0 (mask, see GO-A-3.1).

#### Findings

##### Cat 1 — Dead code

112. `[FIX]` GO-A-1.1 — `go/aletheia/ffi_nocgo.go:29` — ✅ Cluster B: stub extended to 7-arg + `var _ Backend = (*FFIBackend)(nil)` added to ffi.go + ffi_nocgo.go + mock.go.
113. `[FIX]` GO-A-1.2 — ✅ Cluster F: TODO replaced with closure comment + brs/esi threading.
114. `[ ]` GO-A-1.3 — `go/aletheia/enrich.go:204` — `collectSignalsInto`'s `default:` branch unreachable (`Formula` sealed); comment phrasing misleading.
115. `[ ]` GO-A-1.4 — `go/aletheia/enrich.go:229` — symmetric to 1.3 (`predicateSignal`).
116. `[ ]` GO-A-1.5 — `go/aletheia/yaml.go:122-144` — `parseYAMLChecks` double-decodes YAML (map+typed); dead work.

##### Cat 2 — Magic numbers

117. `[ ]` GO-A-2.1 — `go/aletheia/check.go:155, 159, 272, 275` — `1000` (ms→μs) 4× literal; reuse `usPerMillisecond`.
118. `[ ]` GO-A-2.2 — `go/aletheia/json.go:1128` — `255` byte-range; use `math.MaxUint8`.
119. `[ ]` GO-A-2.3 — `go/aletheia/json.go:2065, 2072` — `511` / `64` repeat named constants `MaxBitPosition` / `MaxBitLength`.
120. `[ ]` GO-A-2.4 — `go/aletheia/types.go:230` — `NewDLC` raw `15`; add `MaxDLCCode` constant.
121. `[ ]` GO-A-2.5 — `go/aletheia/json.go:1147, 1162, 1178, 1195` — extraction-bin offsets `6/18/3/2` magic; hoist to named constants.
122. `[ ]` GO-A-2.6 — `go/excel/excel.go:587, 588` — same `15` issue as 2.4.
123. `[ ]` GO-A-2.7 — `go/excel/excel.go:816` — `const scale = 1_000_000` no symbolic name; cf. `rationalDenominator int64 = 1_000_000_000`.

##### Cat 3 — Naming

124. `[FIX]` GO-A-3.1 — ✅ Cluster B: assertions added to ffi.go + ffi_nocgo.go + mock.go.
125. `[ ]` GO-A-3.2 — `go/aletheia/dbc.go:281-285` — `DBCRawValueDesc.CANID` field name stutters; rename to `ID CANID`.
126. `[ ]` GO-A-3.3 — `go/aletheia/dbc.go:67, 599`; `excel.go:126`; `json.go:120, 1471, 1953, 2033`; `backend.go:66-75` — `Dbc*`/`DBC*` mixed acronym casing. Sweep to one style.
127. `[ ]` GO-A-3.4 — `go/aletheia/error.go:222, 224` — `wrapValidation` private + `WrapValidationError` public; naming asymmetry.
128. `[ ]` GO-A-3.5 — `go/aletheia/dbc.go:144` — `MuxValues()` method shadows `Multiplexed.MuxValues` field name.
129. `[ ]` GO-A-3.6 — `go/aletheia/types.go:184, 200` — `StandardID`/`ExtendedID` have `Value() uint32` but `BitPosition`/`BitLength` typedefs don't; asymmetric.
130. `[ ]` GO-A-3.7 — `go/aletheia/client.go:47-63` — `lockCh` vs `closeOnce` style split; minor.

##### Cat 4 — Comments

131. `[ ]` GO-A-4.1 — `go/aletheia/dbc.go:189-191` — `SignalByName` docstring says "deep copy" but implementation is shallow.
132. `[ ]` GO-A-4.2 — `go/aletheia/json.go:1214-1217` — `signalNameByIndex` doc says "empty SignalName on OOB"; implementation returns synthetic `"signal_%d"`.
133. `[ ]` GO-A-4.3 — `go/aletheia/json.go:2086-2088` — Comment claims "log via error return" but code silently defaults `isSigned = false`.
134. `[ ]` GO-A-4.4 — `go/aletheia/ffi.go:257-274` — Required-symbols comment incomplete (missing `aletheia_init_rts`).
135. `[ ]` GO-A-4.5 — `go/aletheia/client.go:62` — `lockWaiters` field comment "production callers do not read" is redundant with unexported visibility.
136. `[ ]` GO-A-4.6 — `go/aletheia/error.go:115-117` — `CodeFrameInjectionFailed` doc too vague.
137. `[ ]` GO-A-4.7 — `go/aletheia/json.go:879` — `// AGDA-D-13.4 phase 2a` references closed work item by ID.
138. `[ ]` GO-A-4.8 — `go/aletheia/json.go:45-53` — GO-B-25.2 DEFER comment lacks concrete revisit signal.
139. `[ ]` GO-A-4.9 — `go/aletheia/dbc.go:212-216` — SIG_GROUP_ comment missing cross-reference to Agda module.
140. `[ ]` GO-A-4.10 — `go/aletheia/limits.go:7` — "Mirrored here verbatim" claim has no CI check enforcing value parity.

##### Cat 5 — Error messages

141. `[ ]` GO-A-5.1 — `go/aletheia/error.go:48-52` — Error messages capitalised; non-idiomatic Go (multiple sites: `client.go:213, 217, 225, 642, 706, 720, 758, 763`).
142. `[ ]` GO-A-5.2 — `go/aletheia/error.go:272-274` — `InputBoundExceededError.Error()` prefix `aletheia validation error:` but Kind not declared on struct; `errors.As(err, &aletheia.Error{})` misses it.
143. `[ ]` GO-A-5.3 — `go/aletheia/yaml.go:170` — Mixed quote styles in error string.
144. `[ ]` GO-A-5.4 — `go/aletheia/client.go:679` — `SendFrames frame %d:` breaks per-public-function prefix invariant.
145. `[ ]` GO-A-5.5 — `go/aletheia/json.go:155` — `"invalid byte order %d"` should use `%v` with stringer.
146. `[ ]` GO-A-5.6 — `go/aletheia/json.go:325, 346, 369, 386, 417` — Mixed `%T`/`%d`/`%q` across `serialize*` family.
147. `[ ]` GO-A-5.7 — `go/excel/excel.go:744-746, 753, 765, 774, 779, 786, 796` — Mixed column-name quoting.
148. `[ ]` GO-A-5.8 — `go/aletheia/check.go:153, 270` — Generic `"time must be non-negative"` lacks `within_ms` field name.

##### Cat 6 — Formatting / godoc

149. `[FIX]` GO-A-6.1 — ✅ Cluster B closure.
150. `[ ]` GO-A-6.2 — `go/benchmarks/main.go:778` — `enc.Encode(out)` return error discarded.
151. `[ ]` GO-A-6.3 — `go/benchmarks/main.go:800` — `fs.Parse(args)` return error discarded.
152. `[ ]` GO-A-6.4 — `go/benchmarks/main.go` — 13× `for i := 0; i < N; i++ {` could use Go 1.24 `for range N`.
153. `[ ]` GO-A-6.5 — `go/aletheia/error.go:66-191` — 51 `Code*` constants in one `const ( ... )` block; split per group for godoc rendering.
154. `[ ]` GO-A-6.6 — `go/aletheia/types.go:124` — `ByteOrder int` godoc doesn't enumerate legal values.
155. `[ ]` GO-A-6.7 — `go/aletheia/json.go` — 2173 lines; pending split since R18.
156. `[ ]` GO-A-6.8 — `go/aletheia/client.go` — 1043 lines; same concern, extract `enrich_client.go` candidate.
157. `[ ]` GO-A-6.9 — `go/aletheia/ffi.go` — 831 lines; split per-method wrappers into `ffi_streams.go` + `ffi_frames.go`.
158. `[ ]` GO-A-6.10 — `go/aletheia/json.go:1226` — `const maxFormulaDepth = 100` unexported but bounds user-visible behavior; hoist to `limits.go`.

##### Cat 30 — Logging discipline

159. `[ ]` GO-A-30.1 — `go/aletheia/client.go:783-787, 790-794, 711, 741, 952, 957` — `LogAttrs` calls allocate `slog.Attr` even when Debug disabled; add `Enabled(ctx, slog.LevelDebug)` outer guard mirroring Python R19 cluster 19 PY-B-14.1.
160. `[ ]` GO-A-30.2 — `go/aletheia/ffi.go:363-367` — `rts.cores_mismatch` uses `context.Background()` — should be `context.TODO()` or documented choice.
161. `[ ]` GO-A-30.3 — `go/aletheia/doc.go:69-83` — 15-event vocabulary alphabetically out of order vs `docs/LOG_EVENTS.yaml` grouping.
162. `[ ]` GO-A-30.4 — `go/aletheia/client.go:921, 971, 1007, 1028, 1036` — Warn-level enrichment events allocate unconditionally; minor.
163. `[ ]` GO-A-30.5 — `go/aletheia/ffi.go:154-165` — `stablePtrCount` increment/decrement has no log event; symmetry gap with structured-log discipline.

---

### Go Agent B — Correctness & Runtime

#### Findings (FIX-NOW)

164. `[FIX]` GO-B-31.1 [FIX-NOW] — ✅ Cluster B: stub signature extended + compile-time assertions added; `CGO_ENABLED=0 go build ./aletheia/` clean.
165. `[FIX]` GO-B-24.1 [FIX-NOW] — ✅ Cluster C: `rationalLess` now uses `math/big.Int` cross-product.
166. `[ ]` GO-B-12.1 [FIX-NOW] — `go/aletheia/json.go:696-726` `parseRational` — truncates wire floats to int64 without range check; sibling `parseNumberAsInt64:765-796` does check. Also denominator 0.5 silently truncates to 0.
167. `[FIX]` GO-B-14.1 [FIX-NOW] — ✅ Cluster F: `serializeDataFrame` extended with optional `brs, esi *bool` params, emit `"brs"`/`"esi"` fields when non-nil; `MockBackend.SendFrameBinary` threads through; `check_test.go` callsites pass `nil, nil`. Go race test ok 7.887s.
168. `[FIX]` GO-B-7.1 [FIX-NOW] — ✅ Cluster B closure.

#### Findings (FIX-LATER)

169. `[ ]` GO-B-26.1 [FIX-LATER] — `go/aletheia/json.go:29-39` `serializeCommand` — map+json.Marshal allocates per call; benchmark gate.
170. `[ ]` GO-B-12.2 [FIX-LATER] — `go/aletheia/json.go:799-836` `getString`/`getBool`/`getArray`/`getObject` — silent zero-default on type mismatch; ~30 callsites should migrate to `requireString`.
171. `[ ]` GO-B-23.1 [FIX-LATER] — `go/aletheia/client.go:162-166` `IsClosed` — lock acquisition, not ctx-aware; cross-binding API asymmetry. (See GO-D-15.4.)
172. `[ ]` GO-B-13.1 [FIX-LATER] — `go/aletheia/error.go:34-56` — No `errors.Is(err, ErrXxx)` sentinel match support; add `Is(target error) bool` method.
173. `[ ]` GO-B-9.1 [FIX-LATER] — `go/aletheia/ffi.go:650-688, 727-764` — `BuildFrameBin`/`UpdateFrameBin` write `outBuf` even on `status != 0`; clarify partial-write contract.
174. `[ ]` GO-B-28.1 [FIX-LATER] — `go/aletheia/json.go:1768-1816, 1818-1850` — `parseAttrType "enum"` allocates 100M-string list without cardinality bound before kernel rejects.

#### Findings (INFO)

175. `[ ]` GO-B-26.2 [INFO] — `go/aletheia/json.go:281-292` `serializeDBC` — probes JSON size via double marshal; expensive defense-in-depth.
176. `[ ]` GO-B-29.1 [INFO] — `go/aletheia/yaml.go:14-83` — No symlink validation on `loadYAMLData`; out-of-threat-model.
177. `[ ]` GO-B-7.2 [INFO] — `go/aletheia/result.go:71-82, 99-108, dbc.go:234-246` — Integer enums (`Verdict`/`IssueSeverity`/`DBCVarType`) — verified correct; non-finding.
178. `[ ]` GO-B-22.1 [INFO] — `go/aletheia/json.go:1106-1134` — `parseFrameDataResponse` mock-vs-real bypass asymmetry; cat 14d follow-up candidate.

---

## C++

### C++ Agent A — Hygiene & Style

#### Coverage
All `cpp/include/aletheia/`, `cpp/src/`, `cpp/tests/`, `cpp/benchmarks/`, `cpp/CMakeLists.txt`, `.clang-tidy`.

#### Findings

##### Cat 1 — Dead code

179. `[ ]` CPP-A-1.1 — `cpp/include/aletheia/limits.hpp:54-72` — Six `inline constexpr` bound constants unused. Either wire to parser/handler boundaries or remove with comment.
180. `[ ]` CPP-A-1.2 — `cpp/include/aletheia/limits.hpp:32-38` — Six of seven `bound_kind_*` string_view constants unused.
181. `[ ]` CPP-A-1.3 — `cpp/include/aletheia/types.hpp:5` — `<cassert>` include with zero `assert()` calls.
182. `[ ]` CPP-A-1.4 — `cpp/src/json_serialize.cpp:28-30` — Stale comment about R19 cluster 14 consolidation.

##### Cat 2 — Magic numbers

183. `[ ]` CPP-A-2.1 — `cpp/src/client.cpp:275-340` — Raw `6/18/3/2` extraction layout literals; add named constants.
184. `[ ]` CPP-A-2.2 — `cpp/src/json_serialize.cpp:408` — `max_formula_depth = 100` SSOT violation vs `limits.hpp:max_nesting_depth = 64`.
185. `[ ]` CPP-A-2.3 — `cpp/include/aletheia/detail/cache_keys.hpp:119,120,132` — `0x9e3779b9` golden ratio constant repeated 3×.
186. `[ ]` CPP-A-2.4 — `cpp/src/json_serialize.cpp:506,535` — `data.size() * 4` magic for CSV byte expansion.
187. `[ ]` CPP-A-2.5 — `cpp/src/ffi_backend.cpp:247` — `out.reserve(256)` no rationale.
188. `[ ]` CPP-A-2.6 — `cpp/include/aletheia/types.hpp:162,178` — `(1U << 11U) - 1` self-documenting but error messages embed decimals `"0-2047"`.
189. `[ ]` CPP-A-2.7 — `cpp/include/aletheia/types.hpp:224` — `if (v > 15)` literal DLC max.
190. `[ ]` CPP-A-2.8 — `cpp/include/aletheia/client.hpp:194` — `max_cache_size = 256` duplicated in `LOG_EVENTS.yaml:94` description.

##### Cat 3 — Naming

191. `[ ]` CPP-A-3.1 — `cpp/include/aletheia/types.hpp:127,130,132` — `Delta`/`Tolerance` strong typedefs; cross-binding divergence with Python `Fraction` and Go `Rational` undocumented.
192. `[ ]` CPP-A-3.2 — `cpp/src/detail/mock_backend.hpp:19` — `static inline char sentinel = 0` no trailing underscore per `.clang-tidy`.
193. `[ ]` CPP-A-3.3 — `cpp/src/json_serialize.cpp:32-470` — `static auto …` vs `json_parse.cpp:26-99` anonymous namespace; mixed file-linkage conventions.

##### Cat 4 — Comments

194. `[FIX]` CPP-A-4.1 — ✅ Cluster F: TODO replaced; serialize_send_frame extended with optional brs/esi; MockBackend threads through.
195. `[ ]` CPP-A-4.2 — `cpp/include/aletheia/client.hpp:198-202` — Runtime-cost note on field decl; should live at call site.
196. `[ ]` CPP-A-4.3 — `cpp/src/ffi_backend.cpp:213-214` — Lifecycle invariant in destructor; promote to class-level docstring.
197. `[ ]` CPP-A-4.4 — `cpp/include/aletheia/client.hpp:74` — Constructor missing doxygen on `default_checks`.
198. `[ ]` CPP-A-4.5 — `cpp/src/client.cpp:243-247` — `extraction_error_messages` "must match Agda categorizeIndexed" lacks file/line ref.
199. `[ ]` CPP-A-4.6 — (See 1.4 stale comment.)
200. `[ ]` CPP-A-4.7 — `cpp/include/aletheia/log.hpp:18-28` — Usage example doesn't mention `add_sink` API (R19 cluster 9 / CPP-D-17.4).

##### Cat 5 — Error messages

201. `[ ]` CPP-A-5.1 — `cpp/include/aletheia/types.hpp:78-80` — `Rational` ctor throws vs `make` returns `std::unexpected`; different messages for same precondition.
202. `[ ]` CPP-A-5.2 — `cpp/src/ffi_backend.cpp:279,337,371-374,396-399` — Same validation uses throw OR `std::expected` inconsistently.
203. `[ ]` CPP-A-5.3 — `cpp/src/client.cpp:259,265` — `std::format(... std::string_view{name} ...)` wrap pattern repeated; provide `std::formatter<SignalName>`.
204. `[ ]` CPP-A-5.4 — `cpp/src/client.cpp:397` — Single-quote convention inconsistent.
205. `[ ]` CPP-A-5.5 — `cpp/include/aletheia/types.hpp:225` — `"DLC must be 0-15"` hardcodes bound; use `std::format`.

##### Cat 6 — Formatting / structure

206. `[ ]` CPP-A-6.1 — `cpp/src/client.cpp:617-625` — `send_remote` hand-rolls `std::visit` instead of using consolidated `can_id_value(id)` from R19 cluster 14 / CPP-A-6.2.
207. `[ ]` CPP-A-6.2 — `cpp/src/client.cpp:549-559` — Two near-identical `logger_.debug("frame.processed", ...)` blocks; extract helper.
208. `[ ]` CPP-A-6.3 — `cpp/src/client.cpp:710-731, 733-752` — `enrich_violation`/`enrich_property_result` share 80%; extract shell.
209. `[ ]` CPP-A-6.4 — `cpp/include/aletheia/check.hpp:104-113, 153-157, 176-186, 211-216` — Precondition pattern repeated 4×; extract `check_time_non_negative`/`check_lo_le_hi`.
210. `[ ]` CPP-A-6.5 — `cpp/include/aletheia/error.hpp:14-32` — `InputBoundExceeded` multi-line rationale buried in enum body; promote to docstring.
211. `[ ]` CPP-A-6.6 — `cpp/include/aletheia/client.hpp:73-218` — 145-line class decl; `send_frame(Frame)` overload defined inline (137-139) — move to .cpp.
212. `[ ]` CPP-A-6.7 — `cpp/src/client.cpp:99-109,111-134` — Move-ctor/assign hand-enumerate 9 fields; ABI risk.
213. `[ ]` CPP-A-6.8 — `cpp/include/aletheia/client.hpp:194` — `max_cache_size` private; tests duplicate the literal.
214. `[ ]` CPP-A-6.9 — `cpp/src/ffi_backend.cpp:189-194` — 4 named std::string locals exist only for `.data()` pointers.

##### Cat 30 — Logging discipline

215. `[ ]` CPP-A-30.1 — Multiple `client.cpp` debug-log sites pre-build `initializer_list<LogField>` before level check; mirror Python `isEnabledFor` fast path.
216. `[ ]` CPP-A-30.2 — `cpp/src/client.cpp:550-559` — Hot-path `frame.processed` initializer-list construction even when Debug disabled.
217. `[ ]` CPP-A-30.3 — `cpp/include/aletheia/log.hpp` — `min_level()` accessor not public; blocks fast-path guards.
218. `[ ]` CPP-A-30.4 — `cpp/include/aletheia/log.hpp:30` — `LogLevel::Error` declared but unused.
219. `[ ]` CPP-A-30.5 — `cpp/src/client.cpp:621-622` — `remote_event.sent` inlined `std::visit` differs from every other site.
220. `[ ]` CPP-A-30.6 — `cpp/src/client.cpp:765-767, 784-786` — Log-field casing inconsistent (`canId` vs `index` vs `numResults`).
221. `[ ]` CPP-A-30.7 — `cpp/docs/LOG_EVENTS.yaml` — `cache.full` description duplicates literal `256`.
222. `[ ]` CPP-A-30.8 — `cpp/src/ffi_backend.cpp:202-205` — `rts_mismatch_` recording-vs-emit split undocumented at recording site.

---

### C++ Agent B — Correctness & Runtime

#### Findings

##### Cat 7 — Type tightness

223. `[ ]` CPP-B-7.1 — `cpp/include/aletheia/check.hpp:50,64` — `severity`/`check_severity()` raw `std::string`; should reuse `IssueSeverity` enum.
224. `[ ]` CPP-B-7.2 — `cpp/include/aletheia/check.hpp:65-66,72-73` — `CheckResult::signal_name`/`condition_desc` `std::string` not `SignalName` (strong typedef).
225. `[ ]` CPP-B-7.3 — `cpp/include/aletheia/error.hpp:14-32` + `ffi_backend.cpp:130,147,157,159,279,337` — `ErrorKind::Ffi` enumerated, never constructed in production. Cross-binding parity broken vs Python `FFIError` / Go `ErrFFI`.
226. `[ ]` CPP-B-7.4 — `cpp/src/excel.cpp:501` — `MessageKeyExt = std::tuple<...>` positional-access brittle.

##### Cat 8-9 — Ownership / Memory safety

227. `[ ]` CPP-B-8.1 — `cpp/src/ffi_backend.cpp:158-159` — `dlopen` in member-initialiser, outside try block.
228. `[ ]` CPP-B-8.2 — `cpp/src/ffi_backend.cpp:215` — `~FfiBackend()` default; no static_assert no-owned-resources.
229. `[ ]` CPP-B-9.1 — `cpp/src/ffi_backend.cpp:128-135` — `load_sym<Fn>` doesn't `dlerror()` clear+check defense-in-depth.
230. `[ ]` CPP-B-9.2 — `cpp/src/client.cpp:773-777` — `cache_.emplace` allocates fresh `FramePayload` per miss; consider `find`-then-`assign` like `last_frames_`.
231. `[ ]` CPP-B-9.3 — `cpp/src/ffi_backend.cpp:425-428` — `std::span` from null guard correct; document `[span.cons]` reference.

##### Cat 10-11 — Threading / Serialization

232. `[ ]` CPP-B-10.1 — `cpp/src/ffi_backend.cpp:92-101,183-205` — `rts_state()` Meyers singleton; `rts_mismatch_` write outside lock (single-threaded ctor — OK but document).
233. `[ ]` CPP-B-10.2 — `cpp/include/aletheia/client.hpp:41-43` — Thread-safety docstring (one-client-per-thread); document divergence vs Go's `sync.Mutex`.
234. `[FIX]` CPP-B-11.1 — ✅ Cluster F closure.
235. `[ ]` CPP-B-11.2 — `cpp/src/json_parse.cpp:194-197` — `parse_signal_value` silently degrades float `0.5` via `Rational::from_double` (10⁹ scaling) — Python/Go are stricter.
236. `[ ]` CPP-B-11.3 — `cpp/src/json_parse.cpp:282-297` — `parse_rational_as_int` overflow guard only catches `INT64_MIN / -1`; missing rounded-toward-zero corner.
237. `[FIX]` CPP-B-11.4 — ✅ Cluster C: `INT64_MIN` guard added before any negation / `std::abs`; defense-in-depth raw emission mirrors `Rational::make` invariant.
238. `[ ]` CPP-B-11.5 — `cpp/src/json_parse.cpp:733-767` — `parse_validation` Validation vs other parsers' Protocol; minor asymmetry.

##### Cat 12 — Parsing robustness

239. `[ ]` CPP-B-12.1 — `cpp/src/json_parse.cpp:131-140` — `parse_bounded` callback throws; `bound_kind/observed/limit` not lifted into `AletheiaError::bound_info()`.
240. `[ ]` CPP-B-12.2 — `cpp/src/json_parse.cpp:705-993` — `parse_*` catches `std::exception&`; loses distinction between syntax errors / numeric overflow / nesting.
241. `[ ]` CPP-B-12.3 — `cpp/src/json_parse.cpp:823-828` — `parse_frame_response` byte-level fast path; whitespace-trimming gap.

##### Cat 13 — FFI lifecycle

242. `[ ]` CPP-B-13.1 — `cpp/src/ffi_backend.cpp:154-211` — `RTLD_LOCAL` vs Python's ctypes mode; document chosen mode.
243. `[ ]` CPP-B-13.2 — `cpp/src/ffi_backend.cpp:185-200` — `hs_init` argv lifetime; document GHC memcpy semantics.
244. `[ ]` CPP-B-13.3 — `cpp/src/ffi_backend.cpp:215` — Multiple `FfiBackend` construction leaks dlopen handle + StablePtrs.

##### Cat 14 — Test adequacy

245. `[ ]` CPP-B-14.1 — `cpp/tests/fuzz/fuzz_decode_binary_frame.cpp:42-48` — Fuzz harness is a no-op; replace with actual `parse_extraction_bin` call.
246. `[FIX]` CPP-B-14.2 — ✅ Cluster F closure.
247. `[ ]` CPP-B-14.3 — `cpp/tests/test_cross_binding_integration.cpp:266-288` — Test fires at depth 65; no boundary test at depth 64.
248. `[ ]` CPP-B-14.4 — `cpp/tests/unit_tests_cancel.cpp:91,176,181` — `std::this_thread::sleep_for` violates `feedback_no_physical_time_in_tests.md`.
249. `[ ]` CPP-B-14.5 — `cpp/CMakeLists.txt:94-136` — `ALETHEIA_MUTATION` opt-in; no surviving-mutant report.
250. `[ ]` CPP-B-14.6 — No test exercises `signal_index_.empty()` post-`parse_dbc_text` build_frame.

##### Cat 23-25 — Exception safety / UB / races

251. `[ ]` CPP-B-23.1 — `cpp/src/client.cpp:85-97` — `~AletheiaClient()` swallows `backend_->close(state_)` exceptions silently; no log.
252. `[ ]` CPP-B-23.2 — `cpp/src/client.cpp:111-134` — Move-assign `noexcept` swallows + no log; same as 23.1.
253. `[ ]` CPP-B-23.3 — `cpp/src/client.cpp:493-495` — `add_checks` only public method with try/catch; audit all public methods.
254. `[ ]` CPP-B-23.4 — `cpp/src/ffi_backend.cpp:279,337` — `send_frame_binary` throws across FFI boundary; pure-virtual lacks noexcept contract.
255. `[ ]` CPP-B-24.1 — `cpp/src/types.cpp:53` — `std::llround` errno not checked.
256. `[ ]` CPP-B-24.2 — `cpp/include/aletheia/types.hpp:92-99` — `__int128` operator; verify static_assert ordering. (Confirmed safe.)
257. `[ ]` CPP-B-25.1 — `cpp/src/ffi_backend.cpp:98-101` — Singleton lock-guard pattern OK (documented).
258. `[ ]` CPP-B-25.2 — `cpp/include/aletheia/log.hpp:67-75` — `sinks_` / `min_` read without lock; document `Logger` thread-safety contract.

##### Cat 26-28 — Hot-path / stdlib / security

259. `[ ]` CPP-B-26.1 — `cpp/src/client.cpp:550-558,766-767,785-786` — Hot-path Debug logs build `LogField` list pre-filter; add `is_enabled()` predicate.
260. `[ ]` CPP-B-26.2 — `cpp/src/client.cpp:763` — `cache_` uses `std::map` (O(log n) tree); Python/Go use hash. Switch to `std::unordered_map` with transparent hash.
261. `[ ]` CPP-B-26.3 — `cpp/src/client.cpp:472-481` — `add_checks` clones every formula via `ltl::clone(*f)` then immediately consumed.
262. `[ ]` CPP-B-26.4 — `cpp/src/client.cpp:147-148` — `populate_signal_lookup` allocates `names` vector per message; hoist.
263. `[ ]` CPP-B-27.1 — `cpp/src/excel.cpp:48-61` — `dbc_headers` etc. construct std::string at static-init; use `std::array<std::string_view>`.
264. `[ ]` CPP-B-27.2 — `cpp/src/yaml.cpp:213-235` — `parse_yaml_checks` mixes iteration + try/catch; modern alternative.
265. `[ ]` CPP-B-27.3 — `cpp/src/json_parse.cpp:194-211, 262-280, 282-297` — 3 near-duplicate rational parsers; factor.
266. `[ ]` CPP-B-28.1 — `cpp/src/ffi_backend.cpp:262-265` — `process` builds `std::string{input}.c_str()`; embedded `\0` truncates silently.
267. `[ ]` CPP-B-28.2 — `cpp/src/ffi_backend.cpp:239-261` — Oversize-JSON error built via string concat; minor style.
268. `[ ]` CPP-B-28.3 — `cpp/src/client.cpp:187-198` — `parse_dbc_text` size-checked then re-checked at FFI; OK defense-in-depth.

##### Cat 29 — File I/O

269. `[ ]` CPP-B-29.1 — `cpp/src/excel.cpp:444-452, yaml.cpp:243-249` — No `is_symlink` / canonicalisation; symlink-to-/dev/zero opens.
270. `[ ]` CPP-B-29.2 — `cpp/src/excel.cpp:444-452, yaml.cpp:243-249` — Excel loader no file-size cap; ZIP-bomb resistant 0.
271. `[ ]` CPP-B-29.3 — `cpp/src/excel.cpp:617-624` — `create_excel_template` no parent-dir / typed error.

##### Cat 33 — Dynamic correctness

272. `[ ]` CPP-B-33.1 — `cpp/CMakeLists.txt:31-91` — ASan/UBSan/TSan configurable; verify CI lane exists.
273. `[ ]` CPP-B-33.2 — `cpp/tests/fuzz/` — Fuzz target dead.
274. `[ ]` CPP-B-33.3 — `cpp/tests/` — No Catch2 GENERATE property tests; adopt for wire-roundtrip pairs.
275. `[ ]` CPP-B-33.4 — `cpp/tests/test_cross_binding_integration.cpp:77-288` — Tests "PROTOCOL.md shape" not byte-corpus parity; document tradeoff.

---

## Python

### Python Agent A — Hygiene & Style

#### Coverage
Files scanned: all `python/aletheia/`, `python/aletheia/client/`, `python/aletheia/asyncio/`, `python/stubs/can/`, `pyproject.toml`, repo-root `conftest.py`, spot-checked `python/tests/`, `benchmarks/_common.py`. Baseline: pylint 10.00/10, basedpyright 0/0/0.

#### Findings

276. `[FIX]` PY-A-1.1 [BLOCKING] — `conftest.py:46,193` — imports `ProcessError` from `aletheia` which was REMOVED in R19 cluster 17 / PY-D-20.1 (`5b8791a`). ✅ Closed by cluster A: removed `ProcessError` from imports + `_make_globals` dict (no doc fence references it). Import-time block lifted; downstream 7-tuple-unpack fence failures from cluster 18 BRS/ESI drift surfaced — tracked under cluster F+L.
277. `[ ]` PY-A-1.2 — `python/aletheia/asyncio/_client.py:48-50` — Stale "retained as imports" rationale comment; live imports defend against accidental removal but read defensively.
278. `[ ]` PY-A-2.1 — `python/aletheia/dsl.py:377, 403, 698, 724` — `time_ms * 1000` 4× literal; add `_MS_TO_US` const.
279. `[ ]` PY-A-2.2 — `python/aletheia/client/_enrichment.py:97-101` — `1_000_000` / `1_000` literals duplicate `_MS_TO_US`.
280. `[ ]` PY-A-2.3 — `python/aletheia/can_log.py:167` — `1_000_000` bare literal.
281. `[ ]` PY-A-2.4 — `python/aletheia/client/_enrichment.py:13` — `_MAX_FORMULA_DEPTH = 100` not in `aletheia.limits`; diverges from `MAX_NESTING_DEPTH = 64`.
282. `[ ]` PY-A-2.5 — `python/aletheia/client/_types.py:341,342` — `_MAX_STANDARD_ID`/`_MAX_EXTENDED_ID` no `Final[int]` annotation.
283. `[ ]` PY-A-2.6 — `python/aletheia/client/_types.py:297` — `MAX_EXTRACT_CACHE = 256` no docstring/rationale.
284. `[ ]` PY-A-3.1 — `python/aletheia/checks_runner.py:38` — `Violation` TypedDict naming inconsistent with `CheckRunResult`/`CheckResult`; consider `CheckViolation`.
285. `[ ]` PY-A-3.2 — `python/aletheia/checks.py:38-75` — `CheckResult._property` field collides with `@property` decorator semantics; rename `_formula`.
286. `[ ]` PY-A-3.3 — `python/aletheia/checks.py:54` — `check_severity: str` field + `.severity()` setter chained API; asymmetric.
287. `[ ]` PY-A-4.1 — `python/aletheia/cli.py:1-16` — Module docstring lists 5 subcommands, registers 6 (missing `format-dbc`).
288. `[ ]` PY-A-4.2 — `python/aletheia/_dbc_types.py:64-67` — Docstring on `DBCSignalMultiplexed` references wrong `presence` Literal narrowing.
289. `[ ]` PY-A-4.3 — `python/aletheia/client/_types.py:365-374` etc. — Missing `Raises:` sections on functions that raise ValueError.
290. `[ ]` PY-A-4.4 — `python/aletheia/client/_client.py:594-600` — `_ACK_BYTES`/`_ACK_BYTES_SPACED` dead aliases after R19 cluster 19 hoist to `_ACK_RESPONSES`.
291. `[ ]` PY-A-4.5 — `python/aletheia/dsl.py:80-99` — `Signal` docstring three-point coupling admonition borderline-stale.
292. `[ ]` PY-A-4.6 — `python/aletheia/cli.py:24` — Verified `_die` PEP-257-compliant; flagged for completeness.

##### Cat 5 — Error messages

293. `[ ]` PY-A-5.1 — `python/aletheia/client/_{client,signal_ops}.py` — `"Client not initialized — use 'with' statement"` literal 11× duplicated; lift to helper.
294. `[ ]` PY-A-5.2 — `python/aletheia/client/_client.py:231,245,675,820,868` — `"FFI returned null pointer"` literal 5×; lift to helper.
295. `[ ]` PY-A-5.3 — Multiple `_types.py` / `dsl.py` / `checks.py` / loaders raise `ValueError` instead of typed `ValidationError`; 20+ sites. (Carry-over: PY-B-8.1.)
296. `[ ]` PY-A-5.4 — Three different "value out of range" error message shapes across `dsl.py` / `_types.py` / `checks.py`.
297. `[ ]` PY-A-5.5 — `_signal_ops.py:133` — `"Unexpected status: {response.get('status')}"` lacks `!r` and `"(expected …)"` suffix used elsewhere.
298. `[ ]` PY-A-5.6 — `_response_parsers.py:67-72,73-78` — Mixed multi-string vs single-fstring formats.

##### Cat 6 — Module organization

299. `[ ]` PY-A-6.1 — `python/aletheia/client/_client.py` 995 LOC; 5 under pylint C0302 1000-cap. Marginal; identify next extraction candidate.
300. `[ ]` PY-A-6.2 — `python/aletheia/client/_helpers.py` 762 LOC; 5 distinct concerns (`_json_encoding.py` + `_wire_normalize.py` + `_signal_parsing.py` split).
301. `[ ]` PY-A-6.3 — `python/aletheia/dsl.py` 915 LOC; 7 truly-shared methods repeat across `Predicate`/`Property`.

##### Cat 27 — File I/O

302. `[ ]` PY-A-27.1 — `dbc_converter.py:99` — Single-quoted `'utf-8'` vs double-quoted `"utf-8"` elsewhere.
303. `[ ]` PY-A-27.2 — `python/aletheia/client/_ffi.py:241-267` — `os.lstat` symlink check only on `ALETHEIA_LIB`; build-dir / dist-newstyle paths bypass. (Reaffirmed PY-B-26.2.)

##### Cat 28 — Logging discipline

304. `[ ]` PY-A-28.1 — `python/aletheia/client/_client.py:686-720` — Three consecutive `if _logger.isEnabledFor(logging.DEBUG):` guards duplicate; extract `_log_frame_processed` helper.
305. `[ ]` PY-A-28.2 — `python/aletheia/client/_client.py:822, 869` — `send_error`/`send_remote` `log_event` without outer guard; kwargs allocated unconditionally.
306. `[ ]` PY-A-28.3 — `python/tests/test_logging.py::test_log_levels` — 6 of 15 LogEvents not asserted.
307. `[ ]` PY-A-28.4 — `python/aletheia/client/_signal_ops.py:122-125` — `cast(str, error_msg)` runtime no-op; use `str(error_msg)`.

##### Cat 32 — Doctest validity

308. `[FIX]` PY-A-32.1 — Tied to PY-A-1.1. ✅ Cluster A unblocks import-time fail; downstream fence-execution failures from cluster 18 7-tuple drift tracked under cluster F+L.
309. `[ ]` PY-A-32.2 — `test_doc_examples_harness.py:37-50` — `DOC_FILES` validation structural-only, not runnable.

##### Cat 33 — CLI quality

310. `[ ]` PY-A-33.1 — `python/aletheia/cli.py:1-16` — Module docstring missing `format-dbc`.
311. `[ ]` PY-A-33.2 — `python/aletheia/cli.py:742-747` — `format-dbc` subparser no `--json` flag; convention divergence.
312. `[ ]` PY-A-33.3 — `python/aletheia/cli.py:793-805` — Verified `main()` exception coverage; no fix needed.
313. `[ ]` PY-A-33.4 — `python/aletheia/cli.py:99-102` — `_die` docstring should explicitly state "CLI-layer only" given R19 PY-D-20.3 inversion.

---

### Python Agent B — Correctness & Runtime

#### Findings

314. `[ ]` PY-B-8.1 [FIX] — `python/aletheia/client/_types.py:354,374,404` — `validate_can_id`, `dlc_to_bytes`, `bytes_to_dlc` raise `ValueError`. Should be `ValidationError`. Cross-binding parity: Go `ErrValidation`, C++ `ErrorKind::Validation`.
315. `[FIX]` PY-B-8.2 [FIX] — ✅ Cluster C: `<= 0` rejection added at both sites; cross-binding parity with Go `validateRational` / C++ `Rational::make`. Hypothesis test split into accept-positive + reject-non-positive pair.
316. `[ ]` PY-B-8.3 [FIX] — `python/aletheia/client/_client.py:157-172` — `__enter__` leaks RTS refcount on `aletheia_init() → null`. Wrap post-acquire init in try/except.
317. `[ ]` PY-B-8.4 — `python/aletheia/client/_types.py:198-211` — `validate_payload_length` docstring lies (raises `ValueError` via `dlc_to_bytes`, not `ValidationError`). Resolves with 8.1.
318. `[ ]` PY-B-7.1 [FIX] — `_signal_ops.py:60,149,186`, `_client.py:252`, `_helpers.py:184`, `asyncio/_client.py:281,294` — Signal-ops typed `Mapping[str, float | Fraction]`; missing `int` from `_RationalInput`. Pyright rejects natural `{"Speed": 50}` callers.
319. `[ ]` PY-B-7.2 — `python/aletheia/protocols.py:68-80` — `is_str_dict` O(N) key scan; fast-path consideration.
320. `[ ]` PY-B-25.1 — `python/aletheia/client/_client_bin.py:255-257, 281-283` — `(c_uint32 * n)(*signals.indices)` O(N) splat; benchmark vs `struct.pack` threshold.
321. `[ ]` PY-B-25.2 — `python/aletheia/client/_client_bin.py:188-201` — `BinaryFFI` per-call construction; cache instance on `__enter__`.
322. `[ ]` PY-B-26.1 [FIX] — `python/aletheia/client/_client_bin.py:226-234` — `out_size.value` from FFI consumed without upper bound; malicious 4 GiB allocation possible.
323. `[ ]` PY-B-12.1 — `python/tests/test_cancellation.py:369-373` — 10000-cycle poll bound informational; use `asyncio.wait_for`.
324. `[ ]` PY-B-12.2 — `python/aletheia/asyncio/testing.py:113, 117` — `setattr` monkey-patch defeats type-checking; promote `Hook` interface. (See PY-D-24.2.)
325. `[ ]` PY-B-25.3 — `_signal_ops.py:135-137` — `is_object_list` tuple rebuilt per call; hoist.
326. `[ ]` PY-B-14.1 — `python/aletheia/client/_ffi.py:96-101` — `RTSState.release` silent skip; add WARN log on asymmetry.
327. `[ ]` PY-B-26.2 [FIX] — `python/aletheia/client/_ffi.py:217-296` — `ALETHEIA_LIB` permission check (R19 cluster 12) not applied to fallback paths.
328. `[ ]` PY-B-9.1 — `python/aletheia/client/_helpers.py:65-77` — `dump_json` no `sort_keys`; cross-binding wire-bytes parity hazard if test fixtures shuffle.
329. `[ ]` PY-B-22.1 — `python/aletheia/client/_client.py:594-600` — `_ACK_RESPONSES` parity contract not documented for Go/C++.
330. `[ ]` PY-B-23.1 — `python/aletheia/client/_client.py:556-561`, `_types.py:297` — `MAX_EXTRACT_CACHE = 256` skip-insert on full, no LRU eviction → perf cliff post-256 unique keys.
331. `[ ]` PY-B-29.1 — `python/aletheia/client/_helpers.py:300-303` — `parse_rational` swallows `ValueError`/`ZeroDivisionError` without `from exc`.
332. `[ ]` PY-B-30.1 — `python/aletheia/client/_client.py:928-963` — `_extract_last_known_values` sorted iteration verified parity; informational.
333. `[ ]` PY-B-10.1 — `python/aletheia/client/_ffi.py:16-28` — `parse_json_object` no nesting-depth bound; 64 MiB cap allows few-thousand-deep dict skeleton blowing recursion stack.
334. `[ ]` PY-B-22.2 — `python/aletheia/testing.py:14-19` — `MockBackend` documented but not provided; parity gap. (See PY-D-24.1.)

---

## CI/CD

### CI/CD Agent A

#### Coverage
`.github/workflows/gha-checks.yml`, `.github/dependabot.yml`, `.actrc`, `Dockerfile.runtime`, `tools/check_action_pins.py`, `tools/check_workflow_permissions.py`, `tools/check_reproducible_build.py`, `tools/check_changelog.py`, `tools/check_gate_claim.py`, `tools/check_mutation_setup.py`, `tools/check_runbook_coverage.py`, `tools/check_stability_bench.py`, `tools/sbom_generate.py`, `tools/run_ci.py`, `tools/install_hooks.py`, `tools/mutation_run.py`, `tools/stability_run.py`, `Shakefile.hs` `dist`/`install`/`install-python`/`docker` phonies, `docs/development/RELEASE.md`, `docs/development/CI_LOCAL.md`, `AGENTS.md` § CI/CD. Tools clean: `actionlint`, `check_action_pins.py`, `check_workflow_permissions.py`.

#### Findings

335. `[ ]` CICD-1.1 — `.github/workflows/gha-checks.yml:34,63,74` — `actions/checkout@v4` tag-pinned; AGENTS.md L727 mandates 40-char SHA. Either tighten script or relax AGENTS.md to match implemented "GitHub-owned tag, third-party SHA" policy.
336. `[ ]` CICD-1.2 — `tools/check_action_pins.py:31` `USES_RE` regex three issues: (a) matches commented `# uses:`, (b) greedy second group absorbs inline comments, (c) doesn't anchor on `^\s*uses:`.
337. `[ ]` CICD-1.3 — `tools/check_workflow_permissions.py:52-58` — unrecognized top-level `permissions:` scalar form falls through silently; harden.
338. `[ ]` CICD-1.4 — `gha-checks.yml:38-45` — actionlint download verified via SHA-256 but not Sigstore signature; informational (upstream support gap).
339. `[ ]` CICD-1.5 — `.actrc:13` — `ubuntu-latest=catthehacker/...` but workflow uses `ubuntu-24.04`; key mismatch — act silently falls back.
340. `[ ]` CICD-1.6 — `gha-checks.yml` — No `if: always()` / `if: failure()` clauses; vacuously met today, watch for future jobs.
341. `[ ]` CICD-1.7 — `gha-checks.yml:14-15` — `on: push: / pull_request:` no path filter; runs on docs-only PRs.
342. `[ ]` CICD-2.1 — No `actions/cache` for actionlint binary; marginal optimization.
343. `[ ]` CICD-2.2 — `Dockerfile.runtime:35` — `DEBIAN_SNAPSHOT=20250509T000000Z` is one year stale; dependabot doesn't cover it.
344. `[ ]` CICD-2.3 — `tools/check_reproducible_build.py:103` — `cabal run shake -- clean` doesn't clear `dist-newstyle/`; gate is "two-incremental-build" not "two-clean-build" determinism.
345. `[ ]` CICD-3.1 — Workflow-level `permissions: { contents: read }` clean.
346. `[ ]` CICD-3.2 — `tools/check_workflow_permissions.py:38-79` — Doesn't cross-check per-scope minimums; v0 limitation undocumented.
347. `[ ]` CICD-3.3 — `Shakefile.hs::install-python:1015-1029` — Env-var strip list incomplete (missing `COSIGN_PASSWORD`, `PYPI_TOKEN`, `AWS_*`, `PIP_INDEX_URL` poisoning, etc.). Prefer positive whitelist.
348. `[ ]` CICD-3.4 — `Shakefile.hs:967` — cosign signing constructs `Shell` command with string concatenation; single-quote wrap protects but key paths with single quote break.
349. `[ ]` CICD-4.1 — Three jobs in `gha-checks.yml` parallel via `needs:`-free; concurrency group set on `${{ github.ref }}`. Clean.
350. `[ ]` CICD-4.2 — `tools/run_ci.py` redirects to `/tmp/aletheia-pylint.out` etc.; concurrent invocations clobber. Use `tempfile.mkstemp`.
351. `[ ]` CICD-4.3 — `tools/run_ci.py:443-446` random-order lane wired; informational.
352. `[ ]` CICD-4.4 — `Shakefile.hs::dist:769` `removePathForcibly` no lock; concurrent dist runs race.
353. `[ ]` CICD-5.1 [FIX] — `tools/check_reproducible_build.py` not in always-on `run_ci.py` lanes (cost-justified) AND **no `.github/workflows/release.yml` exists** to gate release-cut commits on reproducible-build verification. Wire into a `push: tags: [ 'v*' ]` workflow.
354. `[ ]` CICD-5.2 — `Shakefile.hs::dist:954-979` — Signing path emits `putWarn` and continues when cosign unavailable; no error-out on intentional release. Add `ALETHEIA_RELEASE=1` gate.
355. `[ ]` CICD-5.3 — `tools/sbom_generate.py:118` — `_ghc_dep_components` regex doesn't match `.so.0` style; recorded `purl` package type not standardized.
356. `[ ]` CICD-5.4 — `tools/sbom_generate.py:189-192` — Direct invocation without `--source-epoch` falls back to wall-clock; require or default deterministically.
357. `[ ]` CICD-5.5 — `Shakefile.hs::docker:1031-1056` — SBOM not embedded as Docker label; image not cosign-signed.
358. `[ ]` CICD-5.6 — `tools/check_changelog.py:24-30` — Documented v0 limitations: doesn't verify "Unreleased" heading presence; branch-level not per-commit.
359. `[ ]` CICD-5.7 — `tools/check_gate_claim.py:52-57` — Regex misses "tests pass" / "CI passes" / "all green" forms.
360. `[ ]` CICD-5.8 — `keys/cosign.pub` exists but `keys/README.md` rotation/revocation procedure undocumented.
361. `[ ]` CICD-5.9 — `docs/development/RELEASE.md:127-138` — Cosign pin not auto-enforced; macOS path not covered.

---

## Documentation

### Docs Agent A — Hygiene

#### Findings

362. `[FIX]` DOC-A-1.1 — ✅ Cluster E: 246 → 247.
363. `[FIX]` DOC-A-1.2 — ✅ Cluster E: 244 → 246-of-247.
364. `[FIX]` DOC-A-1.3 — ✅ Cluster E: 22 → 32.
365. `[FIX]` DOC-A-1.4 — ✅ Cluster E: 735 → 826.
366. `[FIX]` DOC-A-1.5 — ✅ Cluster E: 34 → 38.
367. `[FIX]` DOC-A-1.6 — ✅ Cluster E: 17 → 28.
368. `[FIX]` DOC-A-1.7 — ✅ Cluster E: 1263 → 1440 (826 + 331 + 283).
369. `[FIX]` DOC-A-1.8 — ✅ Cluster G: Quick-start fence rebuilt — `AletheiaClient` + `std::stop_token{}` first arg + `parse_dbc_text` + `Frame` overload of `send_frame`.
370. `[FIX]` DOC-A-1.9 — ✅ Cluster G: Quick-start `SendFrame` extended to 7-arg with `f.BRS, f.ESI`.
371. `[FIX]` DOC-A-1.10 — ✅ Cluster G: CANCELLATION.md Go signature gains `brs, esi *bool`; C++ signature gains `std::optional<bool> brs, esi`.
372. `[FIX]` DOC-A-1.11 [FIX] — ✅ Cluster E: 5 sites updated 3.12 → 3.13.
373. `[ ]` DOC-A-1.12 — `docs/architecture/DESIGN.md:65` — "~470 lines across 3 files"; verified correct.
374. `[ ]` DOC-A-1.13 — `CHANGELOG.md:289-291` — Lists `CodeParseInputBoundExceeded`/etc. as Added; R19 cluster 14 consolidated to `CodeInputBoundExceeded`.
375. `[ ]` DOC-A-1.14 — `AGENTS.md:751` — Future-tense paragraph "first review round under this section will surface" already closed.
376. `[FIX]` DOC-A-2.1 — ✅ Cluster E: 2026-05-10 → 2026-05-12.
377. `[FIX]` DOC-A-2.2 — ✅ Cluster E: 2026-05-10 → 2026-05-12.
378. `[FIX]` DOC-A-2.3 — ✅ Cluster E: 2026-05-10 → 2026-05-12.
379. `[FIX]` DOC-A-2.4 — ✅ Cluster E: 2026-05-10 → 2026-05-12.
380. `[ ]` DOC-A-2.5 — `PROJECT_STATUS.md:439` — R17 Track A/B verification block has stale 1263 total.
381. `[ ]` DOC-A-2.6 — `docs/development/BUILDING.md:12` — "Currently active phase" + PROJECT_STATUS.md "No active phase" — moving target.
382. `[FIX]` DOC-A-2.7 — ✅ Cluster G: closed via the same edit as DOC-A-1.10.
383. `[ ]` DOC-A-2.8 — `CHANGELOG.md:242-243` — `parse_input_bound_exceeded`/`dbc_text_input_bound_exceeded`/`frame_input_bound_exceeded` not reflected in cluster-14 consolidation entry.
384. `[FIX]` DOC-A-3.1 — ✅ Cluster E: PROJECT_STATUS.md aligned with CLAUDE.md (247).
385. `[ ]` DOC-A-3.2 — `tools/run_ci.py` step count narrative: CHANGELOG 17→20→21→22, CI_LOCAL 27. Reader has to follow the trail.
386. `[ ]` DOC-A-3.3 — Wire code for adversarial-input bounds: CHANGELOG 3 codes vs PROTOCOL.md consolidated.
387. `[FIX]` DOC-A-3.4 — ✅ Cluster E.
388. `[FIX]` DOC-A-3.5 — ✅ Cluster G: README + CANCELLATION.md aligned with INTERFACES on 7-arg.
389. `[ ]` DOC-A-4.1 [FIX] — `cpp/README.md` and `go/README.md` NOT in doc-example harnesses; `python/README.md` IS covered. Drift hides DOC-A-1.8/1.9 from gate.
390. `[ ]` DOC-A-4.2 — `docs/architecture/PROTOCOL.md` § Error Code Reference (L1154-1238) missing `input_bound_exceeded` entry.
391. `[ ]` DOC-A-4.3 — `PROTOCOL.md:48` Type Tags missing `format_dbc_text`/`parse_dbc_text`.
392. `[ ]` DOC-A-4.4 — `PROTOCOL.md` missing `parseDBCText`/`formatDBCText` JSON command sections.
393. `[ ]` DOC-A-5.1 — Module count stated in 5 places; SSOT should be one.
394. `[ ]` DOC-A-5.2 — Haskell shim "~470 LOC across 3 files" duplicated CLAUDE.md + DESIGN.md.
395. `[ ]` DOC-A-5.3 — "4.3× / 9.1×" throughput appears in 4+ docs.
396. `[ ]` DOC-A-5.4 — Module flag breakdown (242/4/1 vs 241/4/1) stated 3 ways.
397. `[ ]` DOC-A-5.5 — Cosign install snippet duplicated `keys/README.md` + `RELEASE.md`.
398. `[ ]` DOC-A-6.1 to 6.3 — Commands all verified runnable. **Clean.**
399. `[ ]` DOC-A-7.1 — `CONTRIBUTING.md:101` `#contributing` anchor doesn't exist in CLAUDE.md.
400. `[ ]` DOC-A-7.2 to 7.4 — Verified anchors. **Clean.**
401. `[ ]` DOC-A-8.1 — `CHANGELOG.md` carries internal cluster IDs (R18 cluster 1 phase 2, AGDA-D-10.1, PY-D-22.5); audience violation.
402. `[ ]` DOC-A-8.2 — `PROJECT_STATUS.md:3` + `CLAUDE.md:252-254` — 200+ word single-paragraph cluster recaps; audience violation.
403. `[ ]` DOC-A-8.3 — `CANCELLATION.md:153` — `default_checks=` kwarg introduced without prior reference.
404. `[ ]` DOC-A-9.1 — `README.md:11` "six-figure-fps range" vague qualifier.
405. `[ ]` DOC-A-9.2 — `docs/PITCH.md:234` "requires ~8,000 fps" — ~ qualifier on hard derivation.
406. `[ ]` DOC-A-9.3 — `PROJECT_STATUS.md:485` 2x headroom precise; flagging for derivation accessibility.
407. `[ ]` DOC-A-9.4 — `docs/operations/MUTATION.md:51-55` per-binding hot path table precise. **Clean.**

---

### Docs Agent B — Deep

#### Findings

408. `[ ]` DOC-B-10.1 — `docs/PITCH.md` 369-line doc lacks TOC.
409. `[ ]` DOC-B-10.2 — `docs/INDEX.md:97,150` — References `presentation/index.html`; directory not enumerated in find scan.
410. `[ ]` DOC-B-10.3 — `docs/reference/PYTHON_API.md` ~1043 lines no TOC.
411. `[ ]` DOC-B-10.4 — `docs/INDEX.md` § Documentation Map — doesn't annotate `(SSOT)` / `(reference)`.
412. `[ ]` DOC-B-11.1 — `examples/README.md:53-59` — Describes 2 messages / 4 signals; actual `example.dbc` has 3 messages / 6 signals.
413. `[ ]` DOC-B-11.2 — `docs/reference/INTERFACES.md:105,124` — C++ snippet doesn't show BRS/ESI defaults.
414. `[ ]` DOC-B-11.3 — `PYTHON_API.md` Quick Start has no worked examples for `validate_dbc()`, `format_dbc()`, `format_dbc_text()`, `parse_dbc_text()`, `send_error()`, `send_remote()`, `add_checks()`, binary FFI extraction.
415. `[ ]` DOC-B-11.4 — `docs/guides/COOKBOOK.md:180,189` — Inconsistent 4-tuple vs 5-tuple comment.
416. `[ ]` DOC-B-11.5 — `PYTHON_API.md:351,359,376,393,423,444,459` — Pre-R17 4-tuple iter_can_log unpacks alongside 5-field Quick Start at L44.
417. `[ ]` DOC-B-12.1 — `CHANGELOG.md` § Unreleased lacks "Migration notes" sub-section despite calling out Go/C++ Client signature breaks.
418. `[ ]` DOC-B-12.2 — `docs/architecture/CGO_NOTES.md` — Strong rationale for chosen option, no rejected-alternative analysis.
419. `[ ]` DOC-B-12.3 — `PROTOCOL.md:1015` Rational Number Encoding "may differ" ambiguous post-R19 cluster 17.
420. `[ ]` DOC-B-12.4 — `DESIGN.md` § "Why Haskell" thinner rationale than `MUTATION.md` operational rationale; asymmetric.
421. `[ ]` DOC-B-12.5 — `RELEASE.md:41-42` reproducible-build rationale incomplete.
422. `[ ]` DOC-B-13.1 — `QUICKSTART.md § 0` Prerequisites missing Go ≥ 1.24 / CMake ≥ 3.25 / g++ ≥ 14 / clang ≥ 21.
423. `[ ]` DOC-B-13.2 — `QUICKSTART.md:23` verify step has no inline troubleshooting hint.
424. `[ ]` DOC-B-13.3 — `TUTORIAL.md` Path 1 § Step 1 doesn't mention `aletheia[xlsx]` extras.
425. `[ ]` DOC-B-13.4 — `TUTORIAL.md:13` Path 1 "Technician" assumes `cabal run shake -- build` prereq.
426. `[ ]` DOC-B-13.5 — `PITCH.md:222` "four interface tiers" unqualified.
427. `[FIX]` DOC-B-14.1 — ✅ Cluster E.
428. `[ ]` DOC-B-14.2 — `go/README.md:55` + `CLAUDE.md:167` claim `sync.Mutex`; CANCELLATION.md:76,304 claims `chan struct{}` semaphore.
429. `[ ]` DOC-B-14.3 — `tools/run_ci.py` step count: CHANGELOG 17→20→21→22 vs CI_LOCAL 27; 22→27 transition undocumented.
430. `[ ]` DOC-B-14.4 — Version `1.1.1` in DISTRIBUTION.md / BUILDING.md / `pyproject.toml` / `aletheia.cabal`; CHANGELOG declares 2.0.0 Unreleased.
431. `[ ]` DOC-B-14.5 — Benchmark numbers concentrated in PROJECT_STATUS, paraphrased in PITCH.
432. `[ ]` DOC-B-14.6 — STABILITY.md restates source paths from STABILITY_BENCH.yaml; duplication.
433. `[ ]` DOC-B-14.7 — MUTATION.md hot-path paths duplicated from MUTATION_BENCH.yaml.
434. `[ ]` DOC-B-14.8 — Cosign pin duplicated keys/README.md + RELEASE.md; prose-discipline-only invariant.
435. `[ ]` DOC-B-14.9 — `DESIGN.md:65` GHC mention without version; concentrate in BUILDING.md.
436. `[ ]` DOC-B-15.1 — `PYTHON_API.md` Quick Start uses `set_properties` but README uses `add_checks`; enrichment differs.
437. `[ ]` DOC-B-15.2 — `PROTOCOL.md` § 1 ParseDBC example missing multiplexed case.
438. `[ ]` DOC-B-15.3 — `PROTOCOL.md § 7 SendFrame` example shows `brs/esi` but doesn't show omission case.
439. `[ ]` DOC-B-15.4 — `docs/reference/CLI.md:161,372` — Four hex-data formats advertised, only one shown.
440. `[ ]` DOC-B-15.5 — `PROTOCOL.md § 2 ExtractAllSignals` shows decimal `100.0` response vs spec saying rational.
441. `[ ]` DOC-B-15.6 — `INTERFACES.md:105,117,109,119` — `[[maybe_unused]] auto _` doc-harness scaffolding confuses readers.
442. `[ ]` DOC-B-16.1 — `PROTOCOL.md:585` "4.3x/9.1x" no language qualifier.
443. `[ ]` DOC-B-16.2 — `DESIGN.md:67` restates without qualifier.
444. `[ ]` DOC-B-16.3 — `PITCH.md:11` / `PROJECT_STATUS.md:483` "1.08× growth" no binding qualifier.
445. `[ ]` DOC-B-16.4 — `DESIGN.md:67` no `(C++, AMD Ryzen 9...)` qualifier.
446. `[ ]` DOC-B-16.5 — `PITCH.md:233` no binding-meeting-1Mbps qualifier.
447. `[ ]` DOC-B-16.6 — `PITCH.md:51` "six-figure-fps" no CAN protocol qualifier.
448. `[ ]` DOC-B-17.1 — `PROJECT_STATUS.md` 246 vs 244 internal contradiction.
449. `[ ]` DOC-B-17.2 — `PROTOCOL.md:1248,25,1190` — "four entry points" vs body lists 6.
450. `[ ]` DOC-B-17.3 — `PROTOCOL.md § 2` decimal response vs § Rational rational; contradiction.
451. `[ ]` DOC-B-17.4 — `BUILDING.md:30-31,37-38` — Strict pin in commands, flexible recommendation in prose.
452. `[ ]` DOC-B-17.5 — `RUNBOOK.md:53-66,103` + `INTERFACES.md:705` — Same fact different wordings.
453. `[ ]` DOC-B-17.6 — `DESIGN.md:53` "All production modules" vs `PROJECT_STATUS.md:489` "All 244"; doesn't reconcile.
454. `[ ]` DOC-B-17.7 — `BUILDING.md:642` "~1 minute" vs `230` "~1 minute" vs sub-claim "~70s" upper bound; consistency OK overall.
455. `[ ]` DOC-B-18.1 — `PYTHON_API.md` lacks `(Python only)` scope labels.
456. `[ ]` DOC-B-18.2 — `PROTOCOL.md § Structured Logging:1274` correct cross-binding label.
457. `[ ]` DOC-B-18.3 — `STABILITY.md` sub-checks scope-label adequate.
458. `[ ]` DOC-B-18.4 — `PITCH.md:298` explicit `(Python only)` correct example.
459. `[ ]` DOC-B-18.5 — `README.md:14` "cross-binding corpus" but path is `python/tests/...`.
460. `[ ]` DOC-B-19.1 [FIX] — `client.send_error()`/`send_remote()` NOT in `PYTHON_API.md`/`INTERFACES.md`/`COOKBOOK.md`/`TUTORIAL.md`/`QUICKSTART.md`. Public method ships in 2.0.0.
461. `[ ]` DOC-B-19.2 [FIX] — CAN-FD BRS/ESI absent from `PYTHON_API.md`/`INTERFACES.md`/`COOKBOOK.md § CAN logs`/`TUTORIAL.md`/`CHANGELOG.md` [Added].
462. `[ ]` DOC-B-19.3 — `CLI.md` no `format-dbc-text` subcommand (`format_dbc_text` is implemented).
463. `[ ]` DOC-B-19.4 — `RUNBOOK.md` no entry for MAlonzo C-ABI arg-count drift.
464. `[ ]` DOC-B-19.5 — `RUNBOOK.md` no entry for doc-example-harness regression.
465. `[ ]` DOC-B-19.6 — `PYTHON_API.md:996,999` — `dbc_to_json`/`convert_dbc_file` asymmetric coverage.
466. `[ ]` DOC-B-19.7 — `PYTHON_API.md:956` Exceptions section lacks per-exception field documentation.
467. `[ ]` DOC-B-19.8 — `PARITY_PLAN.md:54-462` lacks top-of-doc active/closed status table.
468. `[ ]` DOC-B-19.9 — No doc explains `aletheia.testing` / `aletheia.checks_runner` / `aletheia.cli` relationship after R19 cluster 17 layering inversion.
469. `[ ]` DOC-B-20.1 — `CLI.md` extract example math verified ✓.
470. `[ ]` DOC-B-20.2 — `PROTOCOL.md § Rational` `1.5 → {3,2}` verified ✓.
471. `[ ]` DOC-B-20.3 — `COOKBOOK.md:425` `ts_ms / 1000` correct only when denominator=1; document.
472. `[ ]` DOC-B-20.4 — `PROTOCOL.md § ParseDBC:116` DLC mapping verified ✓.
473. `[ ]` DOC-B-20.5 — `PROTOCOL.md § 7` data array math verified ✓.
474. `[ ]` DOC-B-20.6 — `STABILITY.md:43` math verified ✓.
475. `[ ]` DOC-B-20.7 — `BENCHMARKS.md:27` defaults claim — verify against script.
476. `[ ]` DOC-B-20.8 — `CLI.md § signals:209-217` `bits[0:16]` notation ambiguous.
477. `[ ]` DOC-B-21.1 — `PYTHON_API.md` no per-method cross-binding link.
478. `[ ]` DOC-B-21.2 — `send_error`/`send_remote` no parity row in `INTERFACES.md § Binding parity`.
479. `[ ]` DOC-B-21.3 — `canfd_brs_esi_fields` matrix row exists but per-binding docs don't echo the field names.
480. `[ ]` DOC-B-21.4 — `INTERFACES.md § Binding parity` shorter than FEATURE_MATRIX.yaml; new rows not mirrored.
481. `[ ]` DOC-B-21.5 — `CLI.md` doesn't state `(Python only)` at top.
482. `[ ]` DOC-B-21.6 — `CANCELLATION.md § 3.1-3.3` per-binding partial-commit shapes; no cross-reference table.
483. `[ ]` DOC-B-22.1 — Runbook coverage strong (15-event vocabulary covered).
484. `[ ]` DOC-B-22.2 — Missing entry: MAlonzo C-ABI arg-count drift (post cluster 18 11-arg).
485. `[ ]` DOC-B-22.3 — Missing entry: `hs_init` double-call.
486. `[ ]` DOC-B-22.4 — Missing entry: pre-push hook failure recovery.
487. `[ ]` DOC-B-22.5 — Missing entry: doc-example harness regression.
488. `[ ]` DOC-B-22.6 — Missing entry: `rts.cores_mismatch` caller-side resolution.
489. `[ ]` DOC-B-22.7 — Missing entry: `cabal build -j -A64M -M3G` memory-budget regime.

---

# System-Level Findings

## Agda Agent D — Specification + Architecture

#### Findings

490. `[ ]` AGDA-D-10.1 — `Trace/CANTrace.agda:102-105` — `TraceEvent` cannot model overload-frame / tx-attempts-exhausted / bus-off; document Phase 6 wire-version pin.
491. `[ ]` AGDA-D-10.2 — `Trace/CANTrace.agda:45-54` — `TimedFrame` no `crc`/`errorActivePassive`; document boundary.
492. `[ ]` AGDA-D-10.3 — `Protocol/Message.agda:51-52` — `SendFrame.brs/esi` end-to-end docstring overstates; kernel doesn't consume.
493. `[ ]` AGDA-D-10.4 — `Protocol/StreamState/Types.agda:40` — No `Faulted`/`Closing` terminal state; clients can't distinguish never-loaded from rejected.
494. `[ ]` AGDA-D-11.1 — `Protocol/Handlers.agda:112-125` vs `ParseDBCText.agda:60-74` — `firstDBCOverBound` duplicated; cycle-avoidance documented but shared helper module would close drift.
495. `[ ]` AGDA-D-11.2 [FIX] — `Protocol/Handlers.agda` `firstDBCOverBound` — does NOT walk `comments`/`nodes`/`valueTables`/`valueDescriptions`. `max-value-descriptions-per-file = 1000000` declared in `Limits.agda` but never consulted. 10M VAL_ entries pass cardinality refinement.
496. `[ ]` AGDA-D-11.3 — `classifyStepResult Satisfied prop` informal stability (R6-B9.1 NO-FIX). New angle in AGDA-D-19.x.
497. `[ ]` AGDA-D-11.4 — `Protocol/StreamState.agda:67-69` — `checkMonotonic` rejection skips cache update; document.
498. `[ ]` AGDA-D-11.5 — `Protocol/Handlers.agda:75-79` + `Marshal.hs:42-46` — `validateDLCAndLen` runtime check is precondition for `.dlcValid = refl`; document FFI-validation→Agda-`refl` chain.
499. `[ ]` AGDA-D-12.1 — `Main.agda:34-50` — Adequacy "unconditional soundness" misleading; `AllObserved` is hypothesis FFI doesn't check.
500. `[ ]` AGDA-D-12.2 — `streaming-adequacy` chain holds; document closure in Main.agda for discoverability.
501. `[ ]` AGDA-D-12.3 — JSON-wire `Response.Complete` results to `⟦ ⟧` not proven; `finalizeProperties` → `verdictToResult` bridge unproven.
502. `[ ]` AGDA-D-12.4 — `Monotonic` lifted via `checkedFrames-monotonic`. Chain closed.
503. `[ ]` AGDA-D-13.1 — `Marshal.hs:50` `mkAgdaDLC` — no `check-erasure` guard for `DLC`'s single-Integer ctor shape parallel to existing CAN ID guard.
504. `[ ]` AGDA-D-13.2 — `Marshal.hs:73-76` `bytesToAgdaVec` — `check-erasure` doesn't verify `Vec`'s length parameter is erased.
505. `[ ]` AGDA-D-13.3 — `AletheiaFFI.hs:98-104` — TimedFrame / CANFrame / Timestamp `C_constructor_NN` numeric tags absent from `ffi-exports.snapshot`.
506. `[ ]` AGDA-D-13.4 — `AletheiaFFI.hs:110,119` — `C_Error_38`/`C_Remote_40` TraceEvent ctor tags unguarded.
507. `[ ]` AGDA-D-13.5 — `BinaryOutput.hs:93` — `d_extractionErrorCodeToℕ_148` suffix highly drift-susceptible; not in snapshot.
508. `[ ]` AGDA-D-13.6 — `Marshal.hs:54-55` — `Constants.agda` CAN ID bounds accessors not in snapshot.
509. `[ ]` AGDA-D-13.7 — `Marshal.hs:81-93` `mkAgdaRational` — document Int64-to-Integer widening explicitly.
510. `[ ]` AGDA-D-19.1 — Runtime pipeline never discharges `AllObserved`; users can't attribute `Unresolved` results. Add `unobserved_signals` field to `Complete`.
511. `[ ]` AGDA-D-19.2 — `TwoValued→Bounded` is convenience exit ramp; document NOT on streaming path.
512. `[ ]` AGDA-D-19.3 — `StreamingWarm.agda:91-99` `nothing≢just` re-invents stdlib `Maybe.Properties.just≢nothing`.
513. `[ ]` AGDA-D-19.4 — `StreamState/Internals.agda:241-245` — `stepProperty` builds with OLD cache; `updateEntries-self-lookup` lemma unwritten. Track as proof gap.
514. `[ ]` AGDA-D-32.1 — `Limits.agda:56-57,115-116` — `IdentifierLength` BoundKind declared with wire-code `"identifier_length"` but NO code emits it (`validIdentifierᵇ` rejects at construction, surfaces as ParseFailure). **Wire code unreachable.**
515. `[ ]` AGDA-D-32.2 — `Limits.agda:58-59,119-120` — `StringLength`/`max-string-length-bytes` never emitted by any error site.
516. `[ ]` AGDA-D-32.3 — `Limits.agda:62-63,127-128` — `FrameByteCount`/`max-frame-byte-count` never emitted as typed `InputBoundExceeded`.
517. `[ ]` AGDA-D-32.4 [FIX] — `Limits.agda:112` `max-value-descriptions-per-file = 1000000` declared, never consulted. (Same as AGDA-D-11.2.)
518. `[ ]` AGDA-D-32.5 [FIX] — **3-of-7 enforcement gap on universal rule.** 4 BoundKind ctors enforced as typed `InputBoundExceeded`, 3 not. Add `check-bound-enforcement` Shake gate that greps for emitting sites.
519. `[ ]` AGDA-D-14.1 — `Main.agda:89` — `checkMonotonic` re-exported but no real external consumer.
520. `[ ]` AGDA-D-14.2 — `Main.agda:99-119` — `Response` re-exports asymmetric (omits 4 ctors).
521. `[ ]` AGDA-D-14.3 — `Main.agda:101-119` — `StreamCommand` re-exports omit `SendFrame`/`ParseDBCText`/`FormatDBCText`.
522. `[ ]` AGDA-D-14.4 — `Main/Binary.agda:117-120` — `withDBCBin` private helper used 3×; re-use opportunity.
523. `[ ]` AGDA-D-15.1 — `mkPredTable` design note in `Internals.agda` not visible from `Properties.Bounded`; cross-reference.
524. `[ ]` AGDA-D-15.2 — `Handlers/ParseDBCText.agda`/`FormatDBCText.agda` heavy-import split documented; track regression post-R19 P2.
525. `[ ]` AGDA-D-15.3 — `StreamingWarm.agda` 367 LOC; in-range, tracking.
526. `[ ]` AGDA-D-15.4 — `Limits.agda` re-exports clean. **No action.**
527. `[ ]` AGDA-D-17.1 — `AletheiaFFI.hs:52,159,226` — 3 `unsafeCoerce ... :: T_StreamState_28` sites; `check-erasure` doesn't verify `d_fst_28 :: T_Σ_14 -> AgdaAny` signature.
528. `[ ]` AGDA-D-17.2 — `AletheiaFFI.hs:160,227` — 2 `unsafeCoerce` to `T__'8846'__30` (Sum); same hazard.
529. `[ ]` AGDA-D-17.3 — `BinaryOutput.hs` — 15 unsafeCoerce sites total (BinaryOutput 7 + AletheiaFFI 4 + Marshal 4); factor `coerceTo` newtype hint.
530. `[ ]` AGDA-D-17.4 — `AletheiaFFI.hs:11` lifecycle docstring misleading; bindings rely on GHC RTS init-on-load.
531. `[ ]` AGDA-D-17.5 — `AletheiaFFI.hs:152-162` `runBinDispatch` — state writes before binary-output dispatch; document.
532. `[ ]` AGDA-D-17.6 — `Marshal.hs:81-93` + `bytesToAgdaVec` — Cross-layer assumption that `validateDLCAndLen` IS precondition for Agda's `.dlcValid` `refl`; document.
533. `[ ]` AGDA-D-30.1 [FIX] — `haskell-shim/ffi-exports.snapshot` — Lists 11 `d_*` + 7 helpers. Does NOT list any `C_*`/`T_*` constructor mangled tags. **Snapshot has no constructor-numbering guard.** Extend snapshot format with `F:` / `C:` / `T:` mode markers.
534. `[ ]` AGDA-D-30.2 — `Shakefile.hs:496-562 check-ffi-exports` — Walks modules from `nub (map fst expected)`; doesn't walk `CAN/Constants`, `CAN/Frame`, `Trace/CANTrace` for constructor existence.
535. `[ ]` AGDA-D-30.3 — `Shakefile.hs:564-606 regen-ffi-exports` — Only handles `d_*` definitions; extend to emit `C_*_NN` lines.
536. `[ ]` AGDA-D-31.1 — `aletheia.agda-lib` — `standard-library-2.3` exact pin; stdlib 3.0 hazard tracked.
537. `[ ]` AGDA-D-31.2 — `haskell-shim/aletheia.cabal` — GHC version constraint discipline; track at Phase 6 native bignum work.
538. `[ ]` AGDA-D-GA20.1 — `StreamingWarm.agda:96-99` `nothing≢just` re-invents stdlib; use `Data.Maybe.Properties.just≢nothing`. (See AGDA-D-19.3.)
539. `[ ]` AGDA-D-GA19.1 — `Main.agda:34-50` Adequacy docstring is excellent G-A19 example; cross-reference from `streaming-adequacy` headline.

---

## Go System Agent

#### Findings

540. `[ ]` GO-D-15.1 [HIGH] — Cluster-5 rename incomplete: `NewDbcMessage`/`NewDbcDefinition`/`Backend.FormatDbcBinary`/`WithDbcSheet` kept old casing; unexported `parseDbc*`/`formatDbcFn` drift too. Mass-rename to `NewDBCMessage`/etc.
541. `[ ]` GO-D-15.2 [HIGH] — `DBCRawValueDesc.CANID CANID` stutters with type name; rename `ID CANID`. (See GO-A-3.2.)
542. `[ ]` GO-D-15.3 [MED] — `NewMockError(msg)` wraps `errors.New` for one test use; remove or document.
543. `[ ]` GO-D-15.4 [MED] — `Client.IsClosed()` blocks on lock without ctx; cross-binding asymmetry vs Python property.
544. `[ ]` GO-D-15.5 [MED] — `Respond` / `RespondErr` / `RespondParseDBC` mock helpers naming inconsistent.
545. `[ ]` GO-D-15.6 [LOW] — `Frame.BRS *bool` / `Frame.ESI *bool` no helper `PtrBool(bool) *bool` at public API.
546. `[ ]` GO-D-15.7 [LOW] — `Client.SendFrame` 7 positional args; consider `FrameOption` options pattern.
547. `[FIX]` GO-D-16.1 [HIGH] — ✅ Cluster B closure.
548. `[FIX]` GO-D-16.2 [HIGH] — ✅ Cluster F closure.
549. `[ ]` GO-D-16.3 [MED] — `MockBackend.ExtractSignalsBin` unconditionally returns `ErrBinaryPathUnsupported`; test author can't inject canned binary.
550. `[ ]` GO-D-16.4 [MED] — `Backend` 14 methods mixing `*Binary`/`*Bin` naming for different sides; document or rename.
551. `[ ]` GO-D-16.5 [LOW] — Sealed interface comment "Sealed:" duplicated across 10+ types; consolidate in `doc.go`.
552. `[FIX]` GO-D-17.1 — ✅ Cluster G: CHANGELOG gains 4 BREAKING sections (Python `ProcessError` removal, Go `Dbc*`→`DBC*`, Go predicate `float64`→`Rational`, Go `SendFrame` BRS/ESI args).
553. `[ ]` GO-D-17.2 [MED] — Sum-type extensibility: 5× type-switch dispatch on `Predicate`/`Formula`; no `default` enforcement. Wire `exhaustive` lint or Visitor pattern.
554. `[ ]` GO-D-17.3 [MED] — No `type LogEvent string` enum exposed; consumers must hardcode strings. Cross-binding parity gap.
555. `[ ]` GO-D-17.4 [LOW] — `BoundKind*` const block has bare untyped string; should be `type BoundKind string` (matching `IssueCode`).
556. `[ ]` GO-D-17.5 [LOW] — No `internal/` package; `extractCache`/`frameKey`/`lastFrameData` could move there.
557. `[ ]` GO-D-18.1 — `gopkg.in/yaml.v3 v3.0.1` (no newer release); record.
558. `[ ]` GO-D-18.2 — `excel/v2 v2.10.1` ↔ upstream v2.11.0; bump pending.
559. `[ ]` GO-D-18.3 — `go.work.sum` checked-in; verify policy.
560. `[ ]` GO-D-18.4 — `excel/go.mod` 9 indirect deps; isolation justified.
561. `[ ]` GO-D-19.1 [HIGH] — `Rational.Float64()` used in enrichment loses precision; promote `Rational.String() string` matching wire form.
562. `[ ]` GO-D-19.2 [MED] — `RationalFromFloat` silently converts NaN/Inf to `Rational{0,1}`; Python raises. Cross-binding asymmetry.
563. `[ ]` GO-D-19.3 [MED] — `CANID.Value() uint32` widens 11-bit; consider `StandardID.Value16()`.
564. `[ ]` GO-D-19.4 [LOW] — `MaxBitPosition`/`MaxBitLength` aligned with Agda `Limits`; **clean.**
565. `[ ]` GO-D-19.5 [LOW] — `bytesToDlcTable`/`dlcTable` aligned with C++/Python; **clean.**
566. `[ ]` GO-D-20.1 [HIGH] — `Backend` mixes JSON-command + binary-FFI surfaces; root of GO-D-16.2 routing bug. Document or split `CommandBackend` + `BinaryBackend`.
567. `[ ]` GO-D-20.2 [MED] — `Client.SendFrames([]Frame)` exists but no `Client.SendFrame(Frame)` single-frame struct overload; API surface asymmetric.
568. `[ ]` GO-D-20.3 [MED] — `*ParsedDBC`/`*ValidationResult`/`*StreamResult` pointer-returns; Python/C++ return by value. Cross-binding asymmetry.
569. `[ ]` GO-D-20.4 [LOW] — `Client.AddChecks(checks)` overwrites despite "add" naming; rename `SetChecks` or true-append.
570. `[FIX]` GO-D-21.1 [MED] — ✅ Cluster F closure.
571. `[ ]` GO-D-21.2 [MED] — `SendFrames` holds lock for full batch; cooperative cancellation at frame boundaries; document.
572. `[ ]` GO-D-21.3 — Mux helpers aligned with Python/C++. **Clean.**
573. `[ ]` GO-D-21.4 — Consider Go 1.23 `iter.Seq2` streaming over `[]FrameResponse`; Phase 6 candidate.
574. `[FIX]` GO-D-22.1 [HIGH] — ✅ Cluster B closure.
575. `[ ]` GO-D-22.2 [HIGH] — `call_send_frame` 11-arg ABI symmetric with Haskell shim; **clean** (documented).
576. `[ ]` GO-D-22.3 [MED] — `Rational` binary FFI; no Go-side cross-product assertion at binary boundary.
577. `[ ]` GO-D-22.4 [MED] — NUL/bound check on `Process` only; mock-driven tests bypass.
578. `[ ]` GO-D-22.5 [LOW] — `aletheia_send_frame` symbol load list aligned. **Clean.**
579. `[FIX]` GO-D-31.1 [HIGH] — ✅ Cluster B closure. Both `CGO_ENABLED=0/1 go build ./aletheia/` clean; `go test -race -count=1 ./aletheia/` ok 7.738s.
580. `[FIX]` GO-D-31.2 [MED] — ✅ Cluster B closure (claim now holds).
581. `[ ]` GO-D-31.3 — `_test.go` build tag discipline aligned with Python `pytest.mark.ffi`. **Clean.**
582. `[ ]` GO-D-31.4 — Stringer outputs `*_string.go` should be excluded from lint (already default).
583. `[ ]` GO-D-32.1 [MED] — `serializeCommand` deterministic via lex-sort; `serializeDataFrame` uses manual key order. Pin cross-binding wire-byte parity expectation in PROTOCOL.md or unify.
584. `[ ]` GO-D-32.2 [LOW] — `Client.extractLastKnownValues` sorts keys; deterministic. **Clean.**
585. `[ ]` GO-D-32.3 [MED] — Mux extraction source-order iteration aligned with Python/C++.
586. `[ ]` GO-D-32.4 [LOW] — `extractCache` deterministic skip-on-full.

---

## C++ System Agent

#### Findings

587. `[ ]` CPP-D-15.1 [FIX] — `FfiBackend::send_frame_binary` throws while `update_frame_bin`/`extract_signals_bin` return `std::unexpected`; uncaught throw escapes `AletheiaClient::send_frame`. Unify on `std::unexpected`.
588. `[ ]` CPP-D-15.2 [FIX] — `Strong<Tag, T>` ergonomics — verbose `PhysicalValue{Rational{1, 10}}`; add `make_*` factories.
589. `[ ]` CPP-D-15.3 [FIX-style] — `Strong<Tag,T>` + `StrongString<Tag>` should share CRTP base or constrained `Strong`.
590. `[ ]` CPP-D-15.4 [DEFER] — `LtlFormula` extends `std::variant`; portability hazard across libstdc++ versions.
591. `[ ]` CPP-D-15.5 [FIX-style] — `send_frame` `Frame` overload; `send_frames` lacks initializer-list overload.
592. `[FIX]` CPP-D-16.1 [FIX] — ✅ Cluster F closure.
593. `[ ]` CPP-D-16.2 [FIX] — Mock fidelity gap: `MockBackend` doesn't override 4 of 7 binary endpoints; inherits JSON-fallback defaults.
594. `[ ]` CPP-D-16.3 [FIX] — Tests cross public/private boundary via `target_include_directories(unit_tests PRIVATE src)`; promote `detail/` to `aletheia/testing/` or wrap behind opt-in.
595. `[ ]` CPP-D-16.4 [FIX-style] — `IBackend::send_frame_binary` 7 params; hoist into `SendFrameParams` struct.
596. `[ ]` CPP-D-17.1 [FIX] — `AletheiaClient` not `final`; same for `Logger`. Document override surface or seal.
597. `[ ]` CPP-D-17.2 [FIX] — `IBackend` no stable ABI; every method change is vtable layout change. Promote OPTIONAL methods behind `IBackendExtensions`.
598. `[ ]` CPP-D-17.3 [FIX] — `LtlFormula` extending `std::variant` hard-codes 14 alternatives; Visitor pattern for binary-compat extension.
599. `[ ]` CPP-D-17.4 [FIX-style] — `IssueCode` closed enum + hand-rolled `parse_issue_code` if-chain (vs `error_code_table` constexpr pattern). Unify.
600. `[ ]` CPP-D-18.1 [FIX] — `Catch2 v3.7.1` pin without rationale comment; nlohmann/json same. yaml-cpp has good rationale.
601. `[ ]` CPP-D-18.2 [FIX] — `OpenXLSX` pinned to master commit (force-push risk); fork to project namespace.
602. `[ ]` CPP-D-18.3 [FIX] — Sanitizer ignorelist silences OpenXLSX UB findings that overlap loader path (CPP-D-21.x).
603. `[ ]` CPP-D-18.4 [FIX-style] — `FetchContent_Declare` unconditional; option `ALETHEIA_LOADERS` to skip Excel/YAML deps.
604. `[ ]` CPP-D-19.1 [FIX] — `dlc_to_bytes` / `bytes_to_dlc` two parallel tables; one canonical `dlc_byte_count_table` array.
605. `[ ]` CPP-D-19.2 [FIX] — `SignalKeyHash` XOR-then-add poor distribution for adjacent CAN IDs.
606. `[ ]` CPP-D-19.3 [FIX-style] — `Rational::operator<=>` `static_assert(sizeof(__int128) >= 16)`; tighten with consteval probe.
607. `[ ]` CPP-D-19.4 [FIX] — `Rational::from_double` 10⁹ scaling; document combined num × den headroom.
608. `[ ]` CPP-D-19.5 [FIX] — `validate_payload` no BRS validation on non-CAN-FD frames; ISO 11898-1 §10.4.2 says BRS only on CAN-FD.
609. `[ ]` CPP-D-20.1 [FIX] — `max_cache_size = 256` hardcoded in `client.hpp`; SSOT across Python `MAX_EXTRACT_CACHE` / Go `maxExtractCache`. Promote to `aletheia/limits.hpp`.
610. `[FIX]` CPP-D-20.2 [FIX] — ✅ Cluster F closure.
611. `[ ]` CPP-D-20.3 [FIX-style] — `parse_signal_value` + `parse_rational` near-identical; extract `parse_rational_strict_or_float`.
612. `[ ]` CPP-D-20.4 [FIX-style] — `parse_issue_code` 22-branch if-chain; migrate to constexpr lookup table.
613. `[ ]` CPP-D-21.1 [FIX] — `unit_tests_cancel.cpp:91,176,181` physical-time sleeps. (See CPP-B-14.4.)
614. `[ ]` CPP-D-21.2 [FIX] — Loaders no symlink check / ZIP-bomb guard / decompression-ratio cap. (See CPP-B-29.1-2.)
615. `[ ]` CPP-D-21.3 [FIX] — Loaders take no `std::stop_token`; slowest path lacks cancellation.
616. `[ ]` CPP-D-21.4 [FIX] — `ErrorKind::Ffi` declared but never constructed in production. (See CPP-B-7.3.)
617. `[ ]` CPP-D-21.5 [FIX] — `parse_bounded` SAX callback throws at depth 64+; recursive descent already 9600 bytes deep — SIGSEGV before throw. Lower bound or use non-recursive parse_sax.
618. `[ ]` CPP-D-21.6 [FIX-style] — `send_frames` sequential per-frame FFI; consider `aletheia_send_frames_batch`.
619. `[FIX]` CPP-D-22.1 [FIX — CRITICAL] — ✅ Cluster D: 4-arg `AletheiaError` ctor with `e.bound_info()` forwarded; cross-binding parity restored. ctest 10/10 clean.
620. `[ ]` CPP-D-22.2 [FIX] — `FfiBackend` ctor passes stack-local `std::string.data()` to `hs_init`; verify GHC memcpy semantics or copy to static storage.
621. `[ ]` CPP-D-22.3 [FIX] — `~FfiBackend() = default` — multiple FfiBackend instances leak dlopen handle + StablePtrs; document once-per-process contract.
622. `[ ]` CPP-D-22.4 [FIX-style] — `rts_mismatch_info` stuck after first read; document.
623. `[ ]` CPP-D-22.5 [FIX] — `FfiBackend::process` builds `std::string{input}.c_str()` 10 MiB copy; document or switch to (ptr, len) at shim.
624. `[ ]` CPP-D-31.1 [FIX] — `Rational::operator<=>` `__int128` constexpr usability on ARM64 < g++ 14 unchecked.
625. `[ ]` CPP-D-31.2 [FIX] — `static_assert(std::endian::native == std::endian::little)` in `client.cpp:35` only; not in any header.
626. `[ ]` CPP-D-31.3 [FIX] — `<format>` requires libstdc++ 13 / libc++ 16; clang 21 + libstdc++ 12 (Ubuntu 22.04) doesn't have it. Document libstdc++ floor.
627. `[ ]` CPP-D-31.4 [FIX-style] — `std::expected` C++23; document libstdc++ floor.
628. `[ ]` CPP-D-31.5 [FIX] — `std::source_location` Linux-only; add `#if !defined(__linux__) #error`.
629. `[ ]` CPP-D-32.1 [FIX-style] — `$<BUILD_INTERFACE:...>` PRIVATE link of yaml-cpp/OpenXLSX into shared lib; verify `-fPIC`.
630. `[ ]` CPP-D-32.2 [FIX-style] — `target_include_directories(unit_tests PRIVATE src)` blanket include; per-test granularity.
631. `[ ]` CPP-D-32.3 [FIX] — `cross_binding_integration_tests` missing `target_include_directories(... PRIVATE src)` unlike sibling test targets.
632. `[ ]` CPP-D-32.4 [FIX] — `install(DIRECTORY include/ ...)` installs `detail/cache_keys.hpp` unprefixed; rename `_private/` or `#error` guard.
633. `[ ]` CPP-D-32.5 [FIX-style] — `ALETHEIA_CLANG_TIDY` opt-in; default ON when tool found. Same for `ALETHEIA_FUZZ` / `ALETHEIA_MUTATION`.

---

## Python System Agent

#### Findings

634. `[ ]` PY-D-23.1 [LOW] — `aletheia.testing` omits async-side `gate_send_frame` re-export.
635. `[ ]` PY-D-23.2 [LOW] — `add_checks(checks)` merge semantics unclear with duplicate names.
636. `[ ]` PY-D-23.3 [LOW] — `validate_dbc()` returns dict; promote typed `errors()`/`warnings()` partitioning.
637. `[ ]` PY-D-23.4 [MED] — `_RationalInput` private but appears in every Signal builder; promote to `RationalInput` + top-level export.
638. `[ ]` PY-D-23.5 [LOW] — `Predicate.__init__`/`Property.__init__` accept formula dict but docstrings say "not public API"; either gate or accept honestly.
639. `[ ]` PY-D-24.1 [HIGH] — **Backend Protocol DI seam still missing** (carry-over from R19 cluster 9 / PY-D-17.1). Largest cross-binding parity gap. Promote `Backend(Protocol)` + thread through `__init__`.
640. `[ ]` PY-D-24.2 [MED] — `asyncio.testing.gate_send_frame` setattr monkey-patch; closes naturally with PY-D-24.1.
641. `[ ]` PY-D-24.3 [LOW] — `RTSState` module-level singleton; closes with PY-D-24.1.
642. `[ ]` PY-D-25.1 [INFO] — `Signal` three-point coupling no test asserts three lists stay in sync. Verify `test_predicate_sync.py` coverage.
643. `[ ]` PY-D-25.2 [LOW] — TypedDict discriminator unions in `_dbc_types.py` no runtime parity test; add Agda-source-truth walk.
644. `[ ]` PY-D-25.3 [LOW] — `Predicate.implies(other)` accepts `Property | Predicate`; widen to `LTLFormula` or document wrap idiom.
645. `[ ]` PY-D-26.1 [MED] — `pyproject.toml requires-python = ">=3.13"` but classifier lists Python 3.12; drop classifier.
646. `[ ]` PY-D-26.2 [LOW] — `[tool.mutmut]` config in pyproject.toml ships in wheel; move to mutmut.toml.
647. `[ ]` PY-D-26.3 [LOW] — `_install_config` lazy import documented; no test fails-shut on top-level import.
648. `[ ]` PY-D-26.4 [LOW] — `pytest-markdown-docs` pinned in `[dev]` but harness lives at repo root.
649. `[FIX]` PY-D-27.1 [HIGH] — **`conftest.py:46,193,195` imports removed `ProcessError`.** Same as PY-A-1.1. ✅ Closed by cluster A.
650. `[ ]` PY-D-27.2 [MED] — `aletheia.limits` constants not re-exported from top-level `aletheia` package; downstream callers must dig.
651. `[ ]` PY-D-27.3 [MED] — `validate_can_id`/`dlc_to_bytes`/`bytes_to_dlc` raise `ValueError` not `ValidationError`. (See PY-B-8.1.)
652. `[FIX]` PY-D-27.4 [MED] — ✅ Cluster C closure.
653. `[ ]` PY-D-27.5 [LOW] — `CANFrameTuple` BRS/ESI semantics not in docstring (only in `send_frame` docstring).
654. `[ ]` PY-D-28.1 [LOW] — `is_closed` returns `True` pre-`__enter__` AND post-`__exit__`; ambiguous.
655. `[ ]` PY-D-28.2 [LOW] — `send_frames` / `send_frames_iter` asymmetric `BatchError.partial_results`; add `iteration_kind`.
656. `[ ]` PY-D-28.3 [MED] — `Signal.less_than(0.1)` writes `{numerator: 3602879..., denominator: 3602879...}` (float64 bits) instead of `{1, 10}`. Use `to_signal_fraction` in Signal builders.
657. `[ ]` PY-D-28.4 [LOW] — Optional-dependency narrow swallow in `__init__.py:114-134` may re-raise `aletheia.can_log` informative error.
658. `[ ]` PY-D-29.1 [MED] — `aletheia.asyncio.send_frames_iter` per-frame await — no batch path. Add `send_frames_bulk`.
659. `[ ]` PY-D-29.2 [LOW] — `run_checks(logfile: str)` only; no `Iterable[CANFrameTuple]` overload.
660. `[ ]` PY-D-29.3 [LOW] — `aletheia.cli mux-query`/`signals` no multi-DBC merge.
661. `[ ]` PY-D-29.4 [LOW] — Excel loader CAN-FD incomplete (no BRS/ESI columns).
662. `[ ]` PY-D-30.1 [LOW] — `_call_send_frame_ffi` ABI-coupling positional args; bind names for clarity.
663. `[ ]` PY-D-30.2 [LOW] — `MAX_FRAME_BYTE_COUNT` defined but `validate_payload_length` doesn't enforce.
664. `[ ]` PY-D-30.3 [MED] — `_DECIMAL_PRECISION_DEN = 10**9` used for both JSON and binary FFI; document or split.
665. `[ ]` PY-D-30.4 [MED] — `_MAX_FORMULA_DEPTH = 100` independent of `MAX_NESTING_DEPTH = 64`; coherence vs deliberate slack.
666. `[ ]` PY-D-30.5 [LOW] — `is_str_dict` O(N) — cold path; informational.
667. `[ ]` PY-D-31.1 [MED] — `python/build/lib/aletheia/__init__.py` stale build artefacts; `git rm --cached python/build/`.
668. `[ ]` PY-D-31.2 [LOW] — `stubs/` directory dev-only; document or ship as `aletheia-stubs/`.
669. `[ ]` PY-D-31.3 [LOW] — `all` extras self-reference no static guard.
670. `[ ]` PY-D-31.4 [LOW] — `_client.py` near 1000-line cap; split candidate. (See PY-A-6.1.)
671. `[ ]` PY-D-31.5 [INFO] — `stubs/can/__init__.pyi:23` `bitrate_switch: bool` correct.

---

# Action plan — cluster split (2026-05-12)

671 raw findings → 47 marked `[FIX]` across Clusters A-G (✅ shipped); 624
remain.  Clusters H-R organize the remaining work, ordered by blast-radius
per `feedback_review_round_dispositions.md`.  Each cluster ships as one
focused commit; gates run fresh at every cluster closure per
`feedback_gate_claim_integrity.md`.

## ✅ Closed (commits)
- **A** `4be9a84` — `conftest.py` ProcessError unblock (PY-A-1.1 / PY-D-27.1)
- **B** `dbd3e60` — Go `CGO_ENABLED=0` build matrix + Backend interface assertions (GO-B-31.1 / GO-A-1.1 / GO-D-22.1 / GO-D-31.1 / GO-B-7.1)
- **C** `c2c6bab` — cross-binding rational discipline (GO-B-24.1 / PY-B-8.2 / CPP cross-binding)
- **D** `9a73a48` — C++ `send_frames` bound_info_ forwarding (CPP-D-22.1)
- **E** `c795141` — docs hygiene: module count, Python 3.13 floor, Last-Updated stamps (DOC-A-1.1-1.7 / 1.11 / 2.1-2.4 / 3.1 / 3.4)
- **F** `036a684` — BRS/ESI mock fidelity Go + C++ + `serialize_send_frame` (GO-B-14.1 / CPP-B-11.1 / CPP-D-16.1 / R20 cluster F)
- **G** `00dc764` — CHANGELOG R19 BREAKING entries + cpp/go README + CANCELLATION.md drift (GO-D-17.1 / DOC-A-1.8-1.10 / 2.7 / 3.5)

## Pending clusters

### Cluster H — Remaining FIX-NOW + universal-rule gaps  *(small, urgent)*
- `GO-B-12.1` — `parseRational` wire-float overflow + denominator-fraction silent truncation
- `AGDA-D-11.2` — `firstDBCOverBound` skips 4 list types
- `AGDA-D-32.4` — `max-value-descriptions-per-file` declared but never enforced

### Cluster I — AGDA BoundKind enforcement audit
- `AGDA-D-32.1/32.2/32.3/32.5` — `IdentifierLength` / `StringLength` / `FrameByteCount` declared but never emitted; lift binding-level rejections into kernel
- `AGDA-D-30.1` — `ffi-exports.snapshot` constructor coverage gap
- FEATURE_MATRIX row update

### Cluster J — Python ValidationError migration
- `PY-A-5.3` / `PY-B-8.1` / `PY-D-27.3` — ~20 `ValueError` sites should raise `ValidationError` per PY-D-20.1 kind-tagged hierarchy
- Touches `_helpers.py`, `loaders/`, factory paths; pylint 10/10

### Cluster K — C++ ErrorKind::Ffi emission
- `CPP-D-21.4` / `CPP-B-7.3` — `ErrorKind::Ffi` declared but never constructed; mirrors Python `FFIError` and Go `ErrFFI`
- Audit dlopen / dlsym / `hs_init` paths

### Cluster L — BRS/ESI doc-fence sweep  *(unblocks gate)*
- Doc-fence harness regression: post-cluster-A unblock surfaced **102 fence failures** because `CANFrameTuple` is now 7-tuple (R19 cluster 18 BRS/ESI) but docs still unpack 5
- Files: `docs/COOKBOOK.md`, `docs/TUTORIAL.md`, `docs/guides/QUICKSTART.md`, `docs/reference/PYTHON_API.md`, `docs/reference/INTERFACES.md` (+ siblings)
- `DOC-B-19.2` and friends

### Cluster M — Logger fast-path guards (Go + C++)
- `GO-A-30.1` — 6 `LogAttrs` sites in `client.go` need `Enabled(ctx, slog.LevelDebug)` outer guard (mirror Python R19 cluster 19 / PY-B-14.1)
- `CPP-A-30.1` — equivalent in C++ Logger callback path
- Bench after

### Cluster N — Excel / YAML loader I/O hardening
- `CPP-B-29.x` — symlink-safe + ZIP-bomb bounds in `cpp/src/excel/`
- `PY-B-26.2` — same in `python/aletheia/loaders/excel.py` / `yaml.py`
- `CPP-D-21.2` — TOCTOU race on path-resolution
- New tests for symlink loops + 1 KiB → 1 GiB decompression bombs

### Cluster O — Go cluster-5 rename completion + naming Cat 3
- `GO-D-15.1` — `NewDbcMessage` / `NewDbcDefinition` / `Backend.FormatDbcBinary` / `WithDbcSheet` / unexported `parseDbc*` / `formatDbcFn`
- `GO-D-15.2` — `DBCRawValueDesc.CANID CANID` stutter → `ID CANID`
- `GO-A-3.x` siblings

### Cluster P — Python Backend(Protocol) DI seam (R19 carry-over)
- `PY-D-24.1` — promote `Backend(Protocol)` + thread through `AletheiaClient.__init__`
- Largest remaining cross-binding parity gap (C++ has `IBackend`, Go has `Backend` interface, Python has nothing)
- Touches `_client.py`, conftest fixtures, public re-exports; FEATURE_MATRIX row

### Cluster Q — Multi-binding Cat 1/4 cleanup  *(sweep)*
- Dead code + stale comments across AGDA-A / GO-A / CPP-A / PY-A (~80 findings)
- DEFER comments lacking concrete revisit signal (`GO-A-4.8` + siblings)
- Cat 4 wording / godoc rendering

### Cluster R — Misc HIGH follow-ups
- `GO-D-19.1` — `Rational.Float64()` in enrichment loses precision; promote `Rational.String()` matching wire form
- `GO-D-20.1` — `Backend` interface JSON-command + binary-FFI mix; document or split `CommandBackend` + `BinaryBackend`
- Residual HIGH items uncovered while working other clusters

### DEFER-end-of-round (final pass)
- AGDA-B-26.x DEFER block re-evaluation (`stepL-satisfied-stable` lemma, Bool fast-path RE-DEFER post R19-CARRY-1)
- Cat 27 stdlib coverage findings
- C++ `Strong<Tag, T>` ergonomics + `LtlFormula` `std::variant` portability
- `AGENTS.md` future-tense paragraph (DOC-A-1.14)
- DEFERRALS.md / re-disposition file updates

---

## Progress log

- 2026-05-12 — Clusters A-G shipped (commits 4be9a84, dbd3e60, c2c6bab, 9a73a48, c795141, 036a684, 00dc764).  47 findings marked `[FIX]`.  Cluster split saved.


---

**End of R20 findings (Step 1 + Step 2). Round opens for clustering + disposition assignment.**
