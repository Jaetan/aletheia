# R18 Review Findings

**Branch**: `review-r18`
**Started**: 2026-05-07
**Tree state at review start**: `AGENTS.md` modified vs `main` (the R18 protocol additions — 3 new universal rules, Agda cat 32, Go cat 33, C++ cat 33, Python cat 34, new CI/CD section, cat 14 (f)/(g) + cat 27/26/25 leak sub-checks + cat 28/26 adversarial-bounds extensions everywhere). All other source unchanged.

This file aggregates findings from 17 review agents per the R18 protocol:
- 12 step-1 per-file agents (3 Agda + 2 Go + 2 C++ + 2 Python + 2 Documentation + 1 CI/CD)
- 4 step-2 system-level agents (Agda D + Go + C++ + Python)
- 1 cross-document pass

Findings get unique IDs (`<lang>-<agent>-<cat>.<n>`). Disposition legend: `[ ]` TBD · `[FIX]` accepted this round · `[FP]` suspected false positive · `[DEFER-<reason>]` deferred with pointer.

---

## Coverage check

| Agent | Categories owned | Status |
|---|---|---|
| Agda Agent A (Hygiene) | 1, 2, 4, 16, 21, 28, 29 + G-A1, G-A8 | ✓ returned |
| Agda Agent B (Semantics) | 7, 8, 9, 18, 20, 22-26 + G-A2-A6, A9, A10, A12 | ✓ returned (re-run, 8 findings) |
| Agda Agent C (Cross-file) | 3, 5, 6, 27 + G-A14, A15, A16 | ✓ returned |
| Agda Agent D (system-level) | 10-13, 19, 32 + 14, 15, 17, 30, 31 + G-A7, A11, A13, A17-A20, A23 | ✓ returned |
| Go Agent A (Hygiene & Style) | 1-6, 30 | ✓ returned |
| Go Agent B (Correctness & Runtime) | 7-14, 23-29, 33 | ✓ returned |
| Go system-level | 15-22, 31, 32 | ✓ returned |
| C++ Agent A (Hygiene & Style) | 1-6, 30 | ✓ returned |
| C++ Agent B (Correctness & Runtime) | 7-14, 23-29, 33 | ✓ returned |
| C++ system-level | 15-22, 31, 32 | ✓ returned |
| Python Agent A (Hygiene & Style) | 1-6, 27, 28, 32, 33 | ✓ returned |
| Python Agent B (Correctness & Runtime) | 7-14, 23-26, 29, 30, 34 | ✓ returned |
| Python system-level | 15-22, 31 | ✓ returned |
| Docs Agent A (Hygiene) | 1-9 | ✓ returned |
| Docs Agent B (Deep) | 10-22 | ✓ returned |
| Docs cross-doc pass | 5, 15-18 | ✓ returned |
| CI/CD Agent | 1-5 | ✓ returned |

**Coverage gate**: 17 of 17 agents returned full reports. Agda Agent B re-run completed in 7 minutes with 8 substantive findings (after the initial run's stub failure consumed 511k tokens / 12 minutes without producing a report). All 18 cats / guidelines now have per-file or system-level findings.

---

## Universal Rules findings (cross-cutting)

The three new R18 universal rules each declared "the first review round under this rule must surface...". All three findings hit:

- `[FIX]` **UR-1.1** No `/CHANGELOG.md` at repo root. Universal Rule "Public API stability and CHANGELOG discipline" mandates Keep-a-Changelog format with sections per release. Public API changes since last baseline (Track E.10 `format_dbc_text`, E.11 `IssueCode::UnknownValueDescriptionTarget` + Python `aletheia/validation.py` NEW + C++ `validation.hpp` enum additions + Go `IssueUnknownValueDescriptionTarget`, B.3 binding additions, C cancellation surface, etc.) are unrecorded.  → Closed Round 2 (cluster 8): `CHANGELOG.md` created at repo root with `[2.0.0] — Unreleased` section seeded from the v1.1.1 → HEAD public-API diff.
- `[ ]` **UR-2.1** No `§ Limits` section in `docs/architecture/PROTOCOL.md`. Universal Rule "Adversarial-input bounds at parser surfaces" mandates documented compile-time bounds.
- `[ ]` **UR-2.2** No `Aletheia.Limits` Agda module. The kernel-side bounds-constant reference cited by Agda cat 32 / Go cat 28 / C++ cat 28 / Python cat 26 does not exist.
- `[ ]` **UR-2.3** No `InputBoundExceeded` typed error in any of the 7 Agda Error ADTs (`ParseError`, `FrameError`, `RouteError`, `HandlerError`, `DispatchError`, `DBCTextParseError`, `ExtractionError`).
- `[ ]` **UR-2.4** No bounds enforced at any parser entry: `parseDBCText` (no input-length cap), `parseJSON` (no nesting depth cap), `attachValueDescs` (no `unresolvedValueDescs` cardinality cap), `mkPredTable` (no atom-count max), Python loaders (`load_dbc`, `load_checks`, `load_checks_from_excel`, `load_dbc_from_excel`, `dbc_to_json`, `iter_can_log`), Go cgo entry (`*C.char`/`C.size_t` from `processJSONLine`/`processFrameDirect`), C++ FFI entry (`process()` accepts unbounded JSON; `serializeFormulaDepth=100` is serializer-side only).
- `[ ]` **UR-2.5** Python: no `aletheia.InputBoundExceededError` exception type.
- `[ ]` **UR-2.6** C++: no `aletheia::InputBoundExceededError` (or `Result<…>::error_kind == InputBoundExceeded`).
- `[ ]` **UR-2.7** Go: no `*aletheia.InputBoundExceededError` typed error.
- `[ ]` **UR-3.1** No `tools/check-reproducible-build.sh`. Universal Rule "Reproducible build verification" mandates two-build SHA256 comparison.
- `[ ]` **UR-3.2** Shake `dist` rule (`Shakefile.hs:623-691`) does not record `sha256sum libaletheia-ffi.so` before/after `patchelf` and `strip`, no SBOM, no signing, no manifest of GHC `libHS*.so` versions copied into the artifact.
- `[ ]` **UR-3.3** No `-ffile-prefix-map=` / `-fdebug-prefix-map=` in any binding's compile flags (developer paths leak into binaries).

---

## CI/CD findings (whole section is "dark")

The `.github/` directory does not exist. Every workflow-related finding cascades from this.

- `[ ]` **CICD-1.1** No `.github/workflows/` directory. The entire CI/CD surface is missing for a Phase-5.1-complete project with 3 published bindings.
- `[ ]` **CICD-1.2** No `.github/dependabot.yml`.
- `[ ]` **CICD-1.3** `tools/check-action-pins.sh` missing.
- `[ ]` **CICD-1.4** `tools/check-workflow-permissions.sh` missing.
- `[ ]` **CICD-1.5** `actionlint` not installed on host (`which actionlint` fails). Add to `CLAUDE.md § Development Environment` toolchain catalog.
- `[ ]` **CICD-2.1** Shake `dist` rule reads `find ... -name '*.so*'` twice without intermediate caching (Shakefile.hs:648, 660).
- `[ ]` **CICD-3.1** No `permissions:` precedent set; `Shakefile.hs phony "install-python"` (L693) `pip3 install -e .` would inherit ambient `GITHUB_TOKEN` scope when run under CI.
- `[ ]` **CICD-4.1** `Shakefile.hs phony "dist"` couples build + packaging without a hash-verify-step between unpackaged `.so` and packaged tarball.
- `[ ]` **CICD-5.1** No `docs/development/RELEASE.md` (or equivalent named release-process document). DISTRIBUTION.md may serve; verify cat-5 checklist coverage.
- `[ ]` **CICD-5.2** Shake `phony "dist"` does not record `sha256sum dist/aletheia/lib/libaletheia-ffi.so` after `patchelf` and `strip`.
- `[ ]` **CICD-5.3** No SBOM (CycloneDX / SPDX) per release; LGPL-contingency `--bignum=native` rebuild deliverable depends on this.
- `[ ]` **CICD-5.4** `dist/aletheia.tar.gz` is unsigned (no Sigstore / cosign / `.sig`).
- `[ ]` **CICD-5.5** `phony "docker"` (`Shakefile.hs:697`) tags `aletheia:latest` (moving tag); no commit-SHA-derived tag, no digest pin.
- `[ ]` **CICD-5.6** `dist/aletheia/` lacks `BUILD_INFO.json` / `MANIFEST` capturing GHC/cabal/Agda/stdlib pin.
- `[ ]` **CICD-5.7** `phony "dist"` writes "Usage" hint to stdout only; no `dist/aletheia/README` shipped inside the tarball.

---

## Agda findings

### Agda Agent A (Hygiene) — 68 findings

#### Cat 1: Dead code (31 findings — `using` clauses naming symbols that aren't referenced)

- `[ ]` AGDA-A-1.1 [src/Aletheia/Protocol/StreamState/Internals.agda:14] `signalNameStr` imported via `using (signalNameStr)` but never referenced.
- `[ ]` AGDA-A-1.2 [src/Aletheia/Protocol/StreamState.agda:20] `DBC` imported but never referenced.
- `[ ]` AGDA-A-1.3 [src/Aletheia/Protocol/StreamState.agda:21] `SignalCache` imported but never referenced.
- `[ ]` AGDA-A-1.4 [src/Aletheia/Protocol/Handlers.agda:25] `ℚ` imported but never referenced.
- `[ ]` AGDA-A-1.5 [src/Aletheia/Protocol/Message.agda:15] `ℕ` imported but never referenced.
- `[ ]` AGDA-A-1.6 [src/Aletheia/LTL/JSON.agda:18] `Char` imported but never referenced.
- `[ ]` AGDA-A-1.7 [src/Aletheia/CAN/BatchFrameBuilding.agda:16] `SignalDef` imported but never referenced.
- `[ ]` AGDA-A-1.8 [src/Aletheia/CAN/BatchFrameBuilding.agda:20] `Identifier` imported but never referenced.
- `[ ]` AGDA-A-1.9 [src/Aletheia/CAN/BatchFrameBuilding.agda:22] `String` imported but never referenced.
- `[ ]` AGDA-A-1.10 [src/Aletheia/CAN/DBCHelpers.agda:16] `String` imported but never referenced.
- `[ ]` AGDA-A-1.11 [src/Aletheia/CAN/SignalExtraction.agda:25] `String` imported but never referenced.
- `[ ]` AGDA-A-1.12 [src/Aletheia/DBC/Types.agda:23] `ℚ` imported but never referenced.
- `[ ]` AGDA-A-1.13 [src/Aletheia/DBC/TextParser/Comments.agda:46] `Identifier` imported but never referenced.
- `[ ]` AGDA-A-1.14 [src/Aletheia/DBC/TextParser/TopLevel.agda:68] `String` imported but never referenced.
- `[ ]` AGDA-A-1.15 [src/Aletheia/DBC/TextParser/Attributes.agda:70] `as String using (String)` — neither `String` nor `String.X` referenced.
- `[ ]` AGDA-A-1.16 [src/Aletheia/DBC/Properties/WellFormedness.agda:18] `Char` is named in `using (Char)` but only the renamed `_≟ᶜ_` is used; should be `using ()` keeping only the renaming.
- `[ ]` AGDA-A-1.17 [src/Aletheia/DBC/Formatter/Properties.agda:25] `All` imported but never referenced.
- `[ ]` AGDA-A-1.18 [src/Aletheia/DBC/Formatter/MetadataRoundtrip.agda:23] `tt` imported but never referenced.
- `[ ]` AGDA-A-1.19 [src/Aletheia/DBC/Formatter/MetadataRoundtrip.agda:34] `ℚ` imported but never referenced.
- `[ ]` AGDA-A-1.20 [src/Aletheia/DBC/Formatter/MessageRoundtrip.agda:17] `T` imported via `Data.Bool using (T)` but never referenced.
- `[ ]` AGDA-A-1.21 [src/Aletheia/LTL/SimplifySound/Decomposition.agda:29] `tt` imported but never referenced.
- `[ ]` AGDA-A-1.22 [src/Aletheia/LTL/SimplifySound/Decomposition.agda:44] `TimedFrame` imported but never referenced.
- `[ ]` AGDA-A-1.23 [src/Aletheia/LTL/JSON/Format.agda:12] `ℕ` imported but never referenced.
- `[ ]` AGDA-A-1.24 [src/Aletheia/Protocol/FrameProcessor/Properties/Cache.agda:16] `signalNameStr` imported but never referenced.
- `[ ]` AGDA-A-1.25 [src/Aletheia/Protocol/Adequacy/StreamingWarm.agda:51] `signalNameStr` named but never referenced (`DBCSignal` on same line is used).
- `[ ]` AGDA-A-1.26 [src/Aletheia/DBC/TextParser/Properties/Aggregator/Foundations.agda:67] `as FmtAttrs using ()` declares namespace but `FmtAttrs.X` never referenced; remove the line.
- `[ ]` AGDA-A-1.27 [src/Aletheia/Protocol/Handlers.agda:115] base-clause parameter `idx` bound but unused on `[]` branch of `parseAllProperties`.
- `[ ]` AGDA-A-1.28 [src/Aletheia/Protocol/Handlers.agda:127] parameter `propJSONs` bound but unused on `WaitingForDBC` branch of `handleSetProperties`.
- `[ ]` AGDA-A-1.29 [src/Aletheia/Protocol/StreamState.agda:65] parameter `tf` bound but unused on `WaitingForDBC` branch of `handleDataFrame`.
- `[ ]` AGDA-A-1.30 [src/Aletheia/Protocol/StreamState.agda:67] parameter `tf` bound but unused on `ReadyToStream` branch of `handleDataFrame`.
- `[ ]` AGDA-A-1.31 [src/Aletheia/CAN/Encoding/Arithmetic.agda:30] parameter `bitLength` bound but unused on `false` branch of `toSigned`.

#### Cat 2: Magic numbers

- `[x]` ✅ CLOSED Round 9 — AGDA-A-2.1 [src/Aletheia/DBC/TextParser/Properties/Comments/Comment.agda:118-119] cascade fix: lemma `2048<extFlagBit` renamed to `standard-max<extFlagBit`, body now reads `<ᵇ⇒< standard-can-id-max extFlagBit tt`; sole call site at L156 updated.
- `[x]` ✅ CLOSED Round 9 — AGDA-A-2.2 [src/Aletheia/DBC/TextParser/Properties/Comments/Comment.agda:127] prose comment block at L125-133 swept: `2048` → `standard-can-id-max`, `2^31` → `extFlagBit`, `2^29` → `extended-can-id-max` (the latter two not flagged but in the same comment block — applied for hygiene per `feedback_no_subsumption_asymmetry.md`).
- `[ ]` AGDA-A-2.3 [src/Aletheia/Protocol/JSON/Parse.agda:111] literal `9` in `suc (9 + m * 10)` is `10 - 1` kept for `suc _` shape; needs explanatory comment.

#### Cat 4: Comment quality

- `[x]` ✅ CLOSED Round 9 — AGDA-A-4.1 [src/Aletheia/DBC/TextParser/Format/ValueDescription.agda:129-130] scoped-in consolidation per advisor cycle check (Common.agda upstream of every Format/* + CharClassDisjoint, no cycles). 5 private duplicates (Format/EnvVar / Format/ValueDescription / Format/ValueTable / Format/Comments / Properties/CharClassDisjoint) replaced by `open import ... Properties.Attributes.Assign.Common using (digitChar-not-isHSpace)`; canonical lives at Common.agda:56 (already exported, already consumed by Network/Topology.Message/SignalLine.Roundtrip). TODO comment removed.
- `[ ]` AGDA-A-4.2-4.4 [src/Aletheia/Protocol/JSON/Parse.agda:112, 129, 139] three "Unreachable but needed for coverage" comments without lemma references.
- `[ ]` AGDA-A-4.5 [src/Aletheia/Trace/Time.agda:38-41] `ns`/`ms`/`s` constructors documented as live but only `μs` is referenced project-wide; mark as reserved-for-future-use.

#### Cat 16: Performance (R18 stability-bench artifact discipline)

- `[ ]` AGDA-A-16.1 No `benchmarks/stability/<commit>/` directory exists; cat 16 R18 extension requires GHC RTS heap-and-time profile (`+RTS -hT -p`) artifact capture during ≥1M-frame runs. **Currently absent.**
- `[ ]` AGDA-A-16.2 `benchmarks/run_all.sh` does not invoke any `+RTS -hT -p -RTS` build of `libaletheia-ffi.so`.
- `[ ]` AGDA-A-16.3 No documented procedure for collecting `aletheia-ffi.hp`/`aletheia-ffi.prof` and archiving them.
- `[ ]` AGDA-A-16.4 [src/Aletheia/CAN/Encoding.agda:122] `_<?_` Dec-valued bounds check inside `injectHelper` allocates per signal per frame; deferred-Bool-fast-path is documented but no benchmark threshold for the flip is stated.
- `[ ]` AGDA-A-16.5 [src/Aletheia/Prelude.agda:86] `lookupByKey` exports `public` but uses `⌊ k ≟ₛ key ⌋` (cold path); future hot-path caller would silently inherit allocation cost.

#### Cat 21, 28, 29: clean

- `[ ]` AGDA-A-21.* — No findings. Flag header coverage, postulate allowlist, Unsafe-import isolation all confirmed (244 modules; `^postulate` only in `Substrate/Unsafe.agda:92`; no `import.*Substrate.Unsafe` outside the module itself).
- `[ ]` AGDA-A-28.1 [src/Aletheia/LTL/Simplify.agda:81, 110, 121] Three `{-# CATCHALL #-}` pragmas; documented inline but no structural gate prevents missing-case drift on new LTLProc constructors.
- `[ ]` AGDA-A-29.* — No findings on reflection or accidental instance args.

#### G-A1: Import hygiene (23 mergeable-duplicate-import findings)

- `[ ]` AGDA-A-GA1.1 [src/Aletheia/LTL/Coalgebra.agda:25-26] two `open import Aletheia.LTL.Syntax using (...)` lines.
- `[ ]` AGDA-A-GA1.2-1.22 — 21 more occurrences of duplicate-import-line pattern across `BatchExtraction.agda`, `SignalExtraction.agda`, `Validity.agda`, `Validator/Checks.agda`, `Formatter/MessageRoundtrip.agda`, `Protocol/FrameProcessor/Properties/Cache.agda`, `Protocol/Adequacy/StreamingWarm.agda`, `Protocol/StreamState/Internals.agda`, `Protocol/FrameProcessor/Properties/Handlers.agda`, `DBC/TextParser/Attributes.agda`, `DBC/DecRat.agda`, `DBC/DecRat/RationalRoundtrip.agda`, `DBC/Formatter/MessageRoundtrip/{Standard,Extended}.agda`, `DBC/TextParser/Properties/Topology/Message.agda`, `DBC/TextParser/Properties/Aggregator/Refine/ValueDescriptions.agda`, `DBC/Validity/{Composition,WarningChecks,ErrorChecks}.agda`. Mechanically mergeable.
- `[ ]` AGDA-A-GA1.23 [src/Aletheia/DBC/TextParser/Properties/Aggregator/Foundations.agda:67] dead `as FmtAttrs using ()` (cf. AGDA-A-1.26).

### Agda Agent B (Semantics) — re-run completed, 8 findings

After the initial run returned only a stub, the re-run with tightened scope (~15 priority modules: Main / Protocol / FrameProcessor / Encoding / DBC.Validator / DBC.JSONParser / LTL.{Coalgebra,Incremental,Adequacy,Simplify} / SignalPredicate.Evaluation / Trace.Time / Substrate.Unsafe / Error) returned a structured report in 7 minutes.

#### Cat 7: Type tightness

- `[ ]` AGDA-B-7.1 [src/Aletheia/CAN/Frame.agda:28-29] `Byte = ℕ` wider than the 0..255 value range admits. Documented tradeoff (Fin 256 → MAlonzo unary chains); refinement-types pattern (`record { value : ℕ; valid : T (value <ᵇ 256) }` per G-A21) is a candidate for sites not on the per-frame hot path.

#### Cat 8: Proof simplification — chained-rewrite pattern (5 findings)

- `[x]` ✅ CLOSED Round 8 — AGDA-B-8.1 [Protocol/FrameProcessor/Properties/Step.agda:199-203] `handleDataFrame-ack-complete` 3-rewrite chain on a record-shaped goal (`Response.Ack` materialised through `iterate (stepProperty …)` + dispatch tuple). Refactored to single `rewrite mono` (case-dispatch on the `with checkMonotonic prev tf` guard, can't be replaced) plus `cong (λ p → proj₂ (dispatchIterResult dbc p tf updatedCache)) iter-eq` where `iter-eq = trans (iterate-correct step props) (cong (specResult step props ,_) spec-eq)`.
- `[x]` ✅ CLOSED Round 8 — AGDA-B-8.2 [Step.agda:219-223] `handleDataFrame-violation-complete` identical pattern; same refactor with `iter-eq` paired against `just (idx , ce)` instead of `nothing`.
- `[x]` ✅ CLOSED Round 8 — AGDA-B-8.3 [Bounded.agda:114-149] `indexHelper-counter` 6 clauses each chain 3 rewrites; cat 6 (Redundant patterns) per advisor. Extracted private `binary-counter-step` helper consuming both IHs + length-++ + `+-swap-sum` once; the 6 binary clauses (And/Or/Until/Release/MetricUntil/MetricRelease) collapse to one-line dispatchers.
- `[x]` ✅ CLOSED Round 8 — AGDA-B-8.4 [Bounded.agda:228-256] `collectAtomsAcc-spec` same 6-clause pattern on `++ₗ`-shaped List goals; cat 6. Extracted private `binary-acc-spec-step` helper consuming both IHs + ++-assoc once; 6 clauses collapse to one-liners.
- `[x]` SKIPPED Round 8 — AGDA-B-8.5 [Cache.agda:88] `lookupEntries-updateEntries-miss` `false | true` clause stacks 2 rewrites; finding self-labels "minor". Not a real G-A2 violation: lookupEntries equation is small-goal (G-A2's small-goal carve-out applies), and the 2 rewrites do essential variable rewriting (name'→n via ≡csᵇ-sound, then n≡csᵇ n→true to enable lookupEntries reduction). Refactor would require ~5 lines of cong/sym/lookupEntries-step plumbing for no real win. Per advisor "skip if it costs more".

#### Cats 9, 18, 20, 23, 24, 26 — clean

No findings. Proof-currency awareness explicit at Step.agda:17-21 (the "monotonicity enforcement was lifted into Agda" comment); `mkPredTable nothing → Unknown` paired with live external proof (Property 27 / `indexHelper-bound`); no fuel-based recursion in the priority files; erasure (Timestamp/DLC) correct; CATCHALLs in LTL/Simplify.agda all documented; Bool fast-path pattern (`_==ℚ_`/`_≤ℚ_`/`_<ℚ_`) already in place at SignalPredicate/Evaluation.agda:30-50.

#### Cat 22: Irrelevance — 1 architectural candidate

- `[ ]` AGDA-B-22.1 **[CAN/Frame.agda:39-41] `CANId.Standard`/`Extended` proof fields `T (n <ᵇ max)` are NOT marked `.(_ : T …)` (irrelevance modality).** In-source comment addresses `@0` rejection (correct: `data` constructors lack η-equality, `_≟-CANId_` needs proof access for `T-irrelevant`-based identity gap closure) but does NOT consider the `.(…)` modality. Per G-A4, `T (n <ᵇ max)` is the paradigm irrelevance candidate: proof exists solely to enforce a precondition; `T-irrelevant` is consumed by `_≟-CANId_` precisely because the proof carries no information beyond existence. Switching to `.(…)` would (a) simplify `_≟-CANId_` (irrelevant fields ignored by `_≡_`), (b) eliminate the per-CANId `()` runtime cell. Medium effort: every CANId construction site changes; binding FFI marshaling unaffected (proofs already discarded at boundary).

#### Cat 25: Universe level — 1 informational note

- `[ ]` AGDA-B-25.1 [DBC/TextParser/Format.agda:86] `data Format : Set → Set₁` — sole `Set₁` site in priority sweep; documented cause (`pair` quantifies over constructor type). Tracking note; not actionable.

#### Guidelines

- G-A2 (Proof style): cross-links to 8.1-8.5 above. Worst offenders: Step.agda:199-203 / :219-223. `Coalgebra/Properties.agda:317-337` `finalize-empty-equiv` 2-rewrite stack on TruthVal-shaped goals — within G-A2's small-goal carve-out, surfaced for visibility only.
- G-A3 (`in eq`): no legacy `inspect` usage; modern form used uniformly.
- G-A4 (Irrelevance): see 22.1.
- G-A5 / G-A6 / G-A9 / G-A10 / G-A12: clean.

### Agda Agent C (Cross-file) — 36 findings

#### Cat 3: Naming consistency (13 findings)

- `[ ]` AGDA-C-3.1 [src/Aletheia/Main/JSON.agda:11 vs Prelude.agda:31] imports `Data.String._≟_` directly without subscript-suffix rename to `_≟ₛ_`; used at line 43 `msgType ≟ "command"`.
- `[ ]` AGDA-C-3.2 [src/Aletheia/LTL/JSON.agda:19] same divergence; used at L129/138 + 14 more sites.
- `[ ]` AGDA-C-3.3 [src/Aletheia/Protocol/JSON/Properties.agda:16] same divergence; used at L47, L54.
- `[ ]` AGDA-C-3.4 [src/Aletheia/DBC/TextParser/DecRatParse/Properties.agda:52] imports `++-assoc` without `_++ₗ-assoc` rename; ≥30 other Properties modules rename. Used at L1594.
- `[ ]` AGDA-C-3.5 [src/Aletheia/Error.agda:62 vs :369] `InContext` (5 domain ADTs) vs `WithContext` (top-level `Error`) — same operation, two names.
- `[ ]` AGDA-C-3.6 [src/Aletheia/Error.agda:201 vs :28] `RouteError.RouteMissingField` carries `Route` prefix; `ParseError.MissingField` does not.
- `[ ]` AGDA-C-3.7 [src/Aletheia/Error.agda:208 vs :201] within `RouteError`, parameterised `RouteMissingField` mixes with hardcoded `MissingDBCField`/`MissingPropsField`.
- `[ ]` AGDA-C-3.8 [src/Aletheia/DBC/Validator/Checks.agda:94, :333] `checkDuplicateMessageIds`, `checkDuplicateMessageNames` lack `All` prefix; 17 sibling `checkAll*` use it.
- `[ ]` AGDA-C-3.9 [src/Aletheia/DBC/Validator/Checks.agda:466] `checkCommentTargetExists` follows neither `check*` (singleton) nor `checkAll*` (list) convention.
- `[ ]` AGDA-C-3.10 [src/Aletheia/DBC/Formatter.agda] `formatCANId`/`formatCommentTarget` use `format*` prefix; `attrDefFields`/`attrDefaultFields`/`attrAssignFields` use `*Fields` suffix without `format`.
- `[ ]` AGDA-C-3.11 [src/Aletheia/CAN/BatchExtraction.agda + Batch/Properties.agda] `BatchExtraction.agda` and `BatchFrameBuilding.agda` flat under `CAN/` while their property submodules live under `CAN/Batch/Properties/`; inconsistent with `CAN/Encoding.agda`+`CAN/Encoding/Properties.agda` pattern.
- `[ ]` AGDA-C-3.12 [src/Aletheia/Prelude.agda:38 vs Main/Binary.agda:49] `mapₑ = map₁` (one-side) paired with `bimapₑ = map` (bifunctor); naming asymmetry.
- `[ ]` AGDA-C-3.13 [src/Aletheia/Error.agda:255 vs :208] `HandlerError.NoDBC` and `RouteError.MissingDBCField` are domain-parallel but unrelated names.

#### Cat 5: Error message consistency (9 findings)

- `[ ]` AGDA-C-5.1 [src/Aletheia/Error.agda:225 vs :179] verb-first `"failed to parse byte array"` vs noun-first `"injection failed for signal 'X'"`.
- `[ ]` AGDA-C-5.2 [Error.agda:84 vs :78-82] DLC error omits both quote marks and a bound; CAN-ID errors include the bound.
- `[ ]` AGDA-C-5.3 [Error.agda:95-96] `"bigEndian"` lowercase mismatches type-level `BigEndian` and wire `"big_endian"`; unicode `∸` leaks into wire string.
- `[ ]` AGDA-C-5.4 [Error.agda:228-231 vs :213-215] `MissingDBCField`/`MissingPropsField` produce byte-identical wire output to `RouteMissingField "dbc"`/`RouteMissingField "properties"`.
- `[ ]` AGDA-C-5.5 [Error.agda:232-233 vs :291] `WrappedParse` clauses in `RouteError` and `HandlerError` emit the identical `"parse error: " ++ ...` prefix.
- `[ ]` AGDA-C-5.6 [Error.agda:285 vs :223] DLC-related errors mix lowercase "invalid" prefix vs sentence-style "DLC exceeds".
- `[ ]` AGDA-C-5.7 [Error.agda:283 vs :347] "at index" vs "at line ..., column ...".
- `[ ]` AGDA-C-5.8 [Error.agda:287, :225, :180] verb/noun ordering inconsistent.
- `[ ]` AGDA-C-5.9 [Error.agda:99-100 vs :101-102] `NonTerminatingRational` exposes math notation `{2, 5}`; `InvalidIdentifier` uses prose grammar.

#### Cat 6: Redundant patterns (9 findings)

- `[ ]` AGDA-C-6.1 [src/Aletheia/LTL/JSON.agda:37-84] eight predicate parsers (`parseEquals`/`parseLessThan`/...) share identical 4-line skeleton.
- `[ ]` AGDA-C-6.2 [src/Aletheia/Protocol/Routing.agda:86-89, 128-131, 144-147] three `try*DBC` handlers with identical `lookupByKey "dbc"` + `Maybe` dispatch.
- `[ ]` AGDA-C-6.3 [DBC/JSONParser.agda:464-486 vs :573-609] `parseCommentTarget` and `parseAttrTarget` share 5 identical kind-discriminator branches.
- `[ ]` AGDA-C-6.4 [DBC/JSONParser.agda:522-542 vs :551-569] `parseAttrType`/`parseAttrValue` share 5-way `if ⌊ kind ≟ₛ "X" ⌋` ladder.
- `[ ]` AGDA-C-6.5 [Error.agda:62, :140, :174, :211, :275] five `InContext` constructors + 10 paired format/code clauses ≈ 30 lines of duplicate boilerplate.
- `[ ]` AGDA-C-6.6 [Error.agda:210, :273] `WrappedParse` declared twice with same payload type.
- `[ ]` AGDA-C-6.7 [DBC/JSONParser.agda:143/164/165 vs :113/114] two co-existing string-match strategies (`lookupString`+`≟ₛ` vs `lookupChars`+`≟-LC`).
- `[ ]` AGDA-C-6.8 [Routing.agda:88, :130, :146 vs :94] 4 of 5 same-shape handlers wrap missing-field error in `InContext`; `trySetProperties` returns it unwrapped.
- `[ ]` AGDA-C-6.9 [DBC/JSONParser.agda:391, :408, :420, :437, :452, :495, :657] seven one-line wrappers around `parseObjectList "name" parser 0`.

#### Cat 27: Stdlib coverage (2 findings)

- `[ ]` AGDA-C-27.1 [DBC/TextParser/Properties/Attributes/Def.agda:131-137] `concatMap-foldr-bridge` hand-rolled because stdlib `concatMap = concat ∘ map` doesn't reduce to `foldr`. Audit other Properties modules for same shape.
- `[ ]` AGDA-C-27.2 [DBC/CanonicalReceivers.agda:101-110] hand-rolled `¬T→T-not`/`T-not-and-T` overlap with stdlib `Data.Bool.Properties.T-not-≡`.

#### G-A14, G-A15, G-A16

- `[ ]` AGDA-C-GA14.1 [Main/Binary.agda:119] sole `inj₁` literal-string site is documented FFI exception. Compliant.
- `[ ]` AGDA-C-GA14.2 [Error.agda:210, :273] in-tree calls them `WrappedParse`, not `WrappedParseError` per the guideline example.
- `[ ]` AGDA-C-GA14.3 [Error.agda:62 vs :369] `InContext` × 5 + `WithContext` × 1 — duplicate context-lift mechanism.
- `[ ]` AGDA-C-GA15.1-15.4 — Cross-link to Cat 6.1, 6.3, 6.2, 6.9 (combinator-extraction candidates).
- `[ ]` AGDA-C-GA16.1-16.2 — Cross-link to Cat 27.2, 27.1.

### Agda Agent D (system-level) — 60 findings

#### Cat 10: Domain model fidelity

- `[ ]` AGDA-D-10.1 [CAN/Frame.agda:39-54] CAN error frames / overload frames / bus-off / ACK timing not representable; `TraceEvent.Error` carries no error code.
- `[ ]` AGDA-D-10.2 [CAN/DLC.agda:71-75 + Trace/CANTrace.agda:42-43] BRS/ESI ride on `TimedFrame.brs : Maybe Bool` as sibling fields, not subtype-discriminated; CAN 2.0B frame with `brs = just true` is well-typed.
- `[ ]` AGDA-D-10.3 [Trace/CANTrace.agda:69-72] `TraceEvent.Remote` carries `CANId` but no `DLC`; ISO 11898 RTR carries DLC on the wire.
- `[ ]` AGDA-D-10.4 [DBC/Types.agda:50-58] `DBCSignal.unit : List Char` carries unit literal but no semantic check (km/h vs mph silently combine).
- `[ ]` AGDA-D-10.5 [DBC/Types.agda:46-48] `SignalPresence.When (multiplexor)` has no type-level link to the multiplexor signal definition.
- `[ ]` AGDA-D-10.6 [Protocol/StreamState.agda:44-46] `checkMonotonic` definition vs Aletheia precision (μs) cross-resolution undocumented.

#### Cat 11: Invariant sufficiency

- `[x]` ✅ CLOSED Round 7 (`02b346f`) AGDA-D-11.1 [Formatter/WellFormed.agda:82 + TextParser/Properties/Aggregator/Universal.agda:132] Two distinct `WellFormedDBC` records under same name in different modules with different fields (1 vs 8 fields).  Resolved by renaming the text-side 8-field record to `WellFormedTextDBCAgg` and moving its definition into a new module `Aletheia.DBC.TextParser.WellFormed` (also closes AGDA-D-GA20.4 type-def-vs-theorem split).  JSON-side `WellFormedDBC` ↔ `WellFormedDBCRT` weak/strong pair preserved.  Earlier 1-field stub `Formatter.WellFormedText.WellFormedTextDBC` (verified unused) removed.
- `[x]` ✅ CLOSED Round 7 (`02b346f`) AGDA-D-11.2 [Formatter/WellFormed.agda:82] JSON-side `WellFormedDBC` doesn't carry `unresolved-empty`/`msg-ids-unique`/attribute-WF/SG-WF; a DBC failing CHECK 18/CHECK 23 satisfies it but isn't text-roundtrip-invertible.  Resolved by documenting the asymmetry as deliberate: JSON roundtrip is structurally less constrained than text roundtrip (text emission is materially lossier — `Vector__XXX` placeholders, dropped `BO_TX_BU_`, multi-value mux selectors, no canonical text representation for orphan `unresolvedValueDescs` entries), so the predicates must differ.  Both module headers now point at each other; text-side `WellFormedTextDBCAgg` exists as the dedicated text-roundtrip predicate.  No invariant gap — the JSON-side correctly captures what JSON roundtrip needs, and the text-side captures what text roundtrip needs.
- `[ ]` AGDA-D-11.3 [CAN/Frame.agda:39-41 vs CAN/DLC.agda:71-75] `CANId` proof field NON-erased, `DLC.bounded` `@0`-erased — close-related-domain-types asymmetry.
- `[ ]` AGDA-D-11.4 [Protocol/StreamState/Internals.agda:138-188] "evaluate-then-update" cache ordering invariant explicitly named in-source as a gap; missing foundational lemma `updateEntries-self-lookup`.
- `[ ]` AGDA-D-11.5 [Protocol/Adequacy/StreamingWarm.agda:329-338] `AllObserved` user-obligation discharged via type-(c) only; no entry-point check produces a typed error.
- `[ ]` AGDA-D-11.6 [CAN/DLC.agda:96-102] `bytesToValidDLC` falls back to `if n ≡ᵇ X` chain for n ≥ 20; finite enum could be `Σ ℕ (λ n → n ∈ {0..8,12,16,20,24,32,48,64})`.

#### Cat 12: Property completeness

- `[ ]` AGDA-D-12.1 [TextParser/Properties/Substrate/Unsafe.agda:116-121] `parseText (formatText d) ≡ inj₂ d` proven, but reverse direction `formatText (parseText x) ≡ x` is NOT proven; only `format-parse-format` fixed-point.
- `[ ]` AGDA-D-12.2 [Protocol/StreamState/Internals.agda:183-188] evaluate-before-update ordering invariant — unproven; delta-predicate soundness rests on it.
- `[ ]` AGDA-D-12.3 [LTL/Adequacy.agda:6-25] `adequacy` holds unconditionally but only loosely sound on non-monotonic σ; the user-relevant "monotonic + warm cache ⇒ definite verdict" theorem isn't exposed as one named result.
- `[ ]` AGDA-D-12.4 [CAN/DLC.agda:96-102] no proof that `bytesToValidDLC` catch-all exhausts the 9 valid byte counts.
- `[ ]` AGDA-D-12.5 [DBC/Validator/Checks.agda] no per-CHECK soundness/completeness theorems for the 23 CHECKs individually.
- `[ ]` AGDA-D-12.6 [Protocol/JSON/Parse.agda:253-255] `parseJSON` termination is proven; complexity bound (`O(n)` time/allocation) is not.

#### Cat 13: Assumption audit

- `[ ]` AGDA-D-13.1 [Main/Binary.agda:28] "native byte order" assumption documented, not type-encoded; no host check at startup.
- `[ ]` AGDA-D-13.2 [TextParser/Properties/Substrate/Unsafe.agda:92-94] 2 trusted axioms `toList∘fromList`/`fromList∘toList` co-located, isolated. Compliant.
- `[ ]` AGDA-D-13.3 [haskell-shim/src/AletheiaFFI/BinaryOutput.hs:36, 43, 47, 79, 80, 92, 94] 16 `unsafeCoerce` sites; covered by `check-fidelity` for FFI exports, but per-MAlonzo-constructor assumptions documented in comments only.
- `[ ]` AGDA-D-13.4 [Protocol/JSON/Parse.agda:192-194] `parseJSONHelper zero pos input = nothing` fallback supposed unreachable; no proof, no `mkPredTable`-style dead-branch lemma.
- `[ ]` AGDA-D-13.5 [Main/Binary.agda:81-109] `{-# NOINLINE #-}` pragmas on Agda definitions don't propagate through MAlonzo; comment-only assumption.
- `[ ]` AGDA-D-13.6 [CAN/Frame.agda:24-29] `Byte = ℕ` no type-level guarantee that values stay in `[0, 255]`.

#### Cat 14: API surface (under-exports from Main.agda facade)

- `[ ]` AGDA-D-14.1 [Main.agda:101-119] `Main.agda` re-exports `StreamCommand` constructors but NOT `ParseDBCText` or `FormatDBCText`.
- `[ ]` AGDA-D-14.2 [Main.agda:110-118] does not re-export `ParsedDBCResponse` or `DBCTextResponse`.
- `[ ]` AGDA-D-14.3 [Main.agda:173-196] `Error` re-export omits `DBCTextParseError`, `ParseFailure`, `TrailingInput`, `AttributeRefinementFailed`, `formatDBCTextParseError`.
- `[ ]` AGDA-D-14.4 [Main.agda:139-147] `mkDLC` exported, `bytesToValidDLC` not.
- `[ ]` AGDA-D-14.5 [Main.agda] LTL kernel (`simplify`/`stepL`/`runL`/`denot`/`finalizeL`) not exported.
- `[ ]` AGDA-D-14.6 [Protocol/Message.agda:99] `ParsedDBCResponse` ctor takes `JSON`, no exported function constructs it from a `DBC`.

#### Cat 15: Module structure (oversized modules — split candidates)

- `[ ]` AGDA-D-15.1 [DBC/TextParser/DecRatParse/Properties.agda] **2,419 LOC** — well past 600-800 threshold.
- `[ ]` AGDA-D-15.2 [DBC/TextParser/Format/AttrLine.agda 1,251] [Properties/Attributes/Line.agda 1,021] [Properties/Primitives.agda 983] [Properties/Aggregator/Refine/ValueDescriptions.agda 977].
- `[ ]` AGDA-D-15.3 19 Agda modules exceed 600 LOC; per-topic split convention not consistent in `DBC/TextParser/`.
- `[x]` ✅ CLOSED Round 7 (`02b346f`) AGDA-D-15.4 [Formatter/WellFormed.agda:82 vs Aggregator/Universal.agda:132] same `WellFormedDBC` record name in two places (cf. AGDA-D-11.1).  Closed by the same rename as AGDA-D-11.1: text-side renamed to `WellFormedTextDBCAgg` in new module `Aletheia.DBC.TextParser.WellFormed`.
- `[ ]` AGDA-D-15.5 [DBC/Validator/Checks.agda] all 23 CHECKs in single ~600-line module; CHECK 23 added in E.11 directly here rather than per-CHECK submodule.

#### Cat 17: Cross-layer

- `[ ]` AGDA-D-17.1 [Main/Binary.agda:28-30 vs python/aletheia/client/_client_bin.py:103,130,154] documented "native byte order" but Python forces `<Hqq` (little-endian); no host LE assertion.
- `[ ]` AGDA-D-17.2 [Protocol/Message.agda:99-103] `ParsedDBCResponse`/`DBCTextResponse` need a structural gate test diffing `formatResponse` outputs against per-binding parsers; absent.
- `[ ]` AGDA-D-17.3 [Protocol/ResponseFormat.agda:165-169] `ParsedDBCResponse` shares `"status":"success"` with `DBCResponse`/`Success`/`DBCTextResponse` (4-way conflation); binding parsers must dispatch by field presence.
- `[ ]` AGDA-D-17.4 Same as above for `DBCTextResponse`.
- `[ ]` AGDA-D-17.5 [haskell-shim/ffi-exports.snapshot vs Main.agda] surface-name → mangled-name mapping documented in snapshot but not in `Main.agda` re-export list.
- `[ ]` AGDA-D-17.6 [Protocol/JSON/Parse.agda:192-251] `parseJSON` returns `Maybe JSON`, no typed `ParseError`; binding-side users see "invalid JSON" with no diagnostic.

#### Cat 19: Hypothesis propagation (mostly compliant — discharge confirmations)

- `[ ]` AGDA-D-19.1-19.5 — `Monotonic σ`, `BoundedTwoValued`, `AllObserved`, metric-LTL, `mkPredTable`-bound — discharges confirmed (types a, c, b, a, b respectively).
- `[x]` ✅ CLOSED Round 7 (`02b346f`) AGDA-D-19.6 [Substrate/Unsafe.agda:116-121] `WellFormedDBC d` precondition for `parseText-on-formatText`: JSON-parser path produces witnesses by construction (type b); `formatDBCText` FFI command does NOT enforce — accepts any DBC JSON, would silently fail to roundtrip on malformed input. Mixed discharge.  Resolved per G-A7(c) "documented caller obligation": `Aletheia/Protocol/Handlers/FormatDBCText.agda` now documents the round-trip contract explicitly — the handler emits text unconditionally (the formatter is total), but the round-trip property `parseText (formatText d) ≡ inj₂ d` only applies when the input DBC satisfies `WellFormedTextDBCAgg`.  Discharge happens at the input-source boundary: DBCs from `parseDBCText` carry the witness by construction; DBCs from `parseDBC` + clean `validateDBC` (no CHECK 18 or CHECK 23 issues) discharge `msg-ids-unique` and `unresolved-empty` (the other fields auto-discharge from the refinement-types `Identifier` invariant); hand-constructed JSON DBCs are the caller's responsibility.  No behavioral change — formatDBCText remains best-effort emission, now with the contract surfaced at the source rather than implicit.  A stricter runtime-check variant (decidable `WellFormedTextDBCAgg?` + handler reject + new typed error) is non-trivial (~300-500 LOC for 6+ decidable per-section predicates) and was not pursued in this round; the documented-obligation form is sufficient per G-A7(c).

#### Cat 30, 31, 32

- `[ ]` AGDA-D-30.1-30.4 — FFI export surface stable; 11 exports, `check-ffi-exports`/`check-fidelity` gates cover; per-MAlonzo-constructor assumptions documented in comments only.
- `[ ]` AGDA-D-31.1-31.5 — stdlib pin `2.3` confirmed; 2.3-only imports verified; no 2.4-introduced modules used; lib's `--erasure` flag justification not in `aletheia.agda-lib`.
- `[ ]` AGDA-D-32.1 [docs/architecture/PROTOCOL.md] No `§ Limits` section. (Cf. UR-2.1.)
- `[ ]` AGDA-D-32.2 [src/Aletheia/] No `Aletheia.Limits` module. (Cf. UR-2.2.)
- `[ ]` AGDA-D-32.3 [src/Aletheia/Error.agda] No `InputBoundExceeded` constructor. (Cf. UR-2.3.)
- `[ ]` AGDA-D-32.4 [Protocol/JSON/Parse.agda:253-255] `parseJSON` no input-length cap, no nesting depth bound, no max array cardinality.
- `[ ]` AGDA-D-32.5 [DBC/TextParser/TopLevel.agda:272-279] `parseDBCText` `many parseTopStmt` only structurally bounded.
- `[ ]` AGDA-D-32.6 [DBC/TextParser/ValueDescriptions.agda:109-110] `attachValueDescs` O(NMK) scan unbounded.
- `[ ]` AGDA-D-32.7 [Protocol/StreamState/Internals.agda:191] `mkPredTable` atom cardinality bounded only by input list length.
- `[ ]` AGDA-D-32.8 [DBC/JSONParser.agda] DBC JSON parser 690 LOC, no top-level input-length cap.
- `[ ]` AGDA-D-32.9 [CAN/Frame.agda:50-54] `CANFrame n` payload `Vec Byte n` with no upper bound on `n`.

#### Guideline findings

- `[ ]` AGDA-D-GA7.5 [Protocol/StreamState/Internals.agda:183-188] evaluate-before-update ordering invariant has NO discharge — neither runtime check, nor structural type-level guarantee, nor explicit boundary doc. Vacuous-guarantee per G-A7.
- `[ ]` AGDA-D-GA20.2 [DBC/Types.agda:127-131] `clearVds`/`clearVdsMsg` operations co-located with type definitions — violates G-A20 type/op/property separation.
- `[x]` ✅ CLOSED Round 7 (`02b346f`) AGDA-D-GA20.4 [Aggregator/Universal.agda:132] `WellFormedDBC` type defined alongside the universal theorem; should split.  Closed by extracting the renamed `WellFormedTextDBCAgg` to its own module `Aletheia.DBC.TextParser.WellFormed`.  `Aggregator.Universal` now imports the predicate and consumes it in `parseTextChars-on-formatChars`; type-def split from theorem per G-A20.
- (Other guideline findings: G-A11.1 `WellFormedSignal` not split per byte-order; G-A19.2-3 byte-order/error-code mappings cross-layer drift.)

---

## Go findings

### Go Agent A (Hygiene & Style) — 22 findings

#### Cat 1: Naming conventions (Dbc* vs DBC* mixed)

- `[ ]` GO-A-1.1 [go/aletheia/dbc.go widespread] `Dbc*` prefix runs across DBC type family (`NewDbcMessage`, `DbcDefinition`, `DbcVarTypeInt`, etc.) but `ParsedDBC`/`ParseDBC`/`FormatDBC`/`ValidateDBC`/`FormatDBCText` already use `DBC`. Inconsistent acronym casing.
- `[ ]` GO-A-1.2 [backend.go:60, ffi.go:150,327,476, mock.go:161] `FormatDbcBinary` interface method has same casing issue; public-API surface concern.
- `[ ]` GO-A-1.3 [go/excel/excel.go:48,79,126] Excel module exports `WithDbcSheet`, `LoadDbc`, `dbcSheet`, etc.
- `[ ]` GO-A-1.4 [types.go:137] `CanID` mixes "Can" (camelCase) with `ID` (initialism); strict Go convention prefers `CANID`. (Counter-factor: codebase consistent internally.)
- `[ ]` GO-A-1.5 [types.go:217] `bytesToDlcTable` should be `bytesToDLCTable`.
- `[ ]` GO-A-1.6 [error.go:76-78,92-93] `CodeParseExtCanIDOutOfRange` etc. mix-cased.
- `[ ]` GO-A-1.7 [dbc.go:577] `idIndex` field; `IDIndex` would match `MessageByID`.

#### Cat 2: Package API surface

- `[ ]` GO-A-2.1 [mock.go:100] `NewMockError` is one-line `errors.New` wrapper used from one test only.
- `[ ]` GO-A-2.2 [error.go:128-144 + 167,173] `NewValidationError`/`WrapValidationError` exposed for "external loaders"; asymmetric — no exported counterpart for protocol/state/ffi error kinds.
- `[ ]` GO-A-2.3 [error.go:13] `ErrBinaryPathUnsupported` exported sentinel only used by Client's binary-path fallback; widens API surface.

#### Cat 3, 6: clean

- GO-A-3.* — No findings; staticcheck and vet clean.
- GO-A-6.* — gofmt clean.

#### Cat 4: Comment/doc quality

- `[x]` GO-A-4.1 [doc.go:45-66] Package-level doc lists 15 events but doesn't include `dbc.text_parsed` (which client.go:287 emits). Drift between package doc and code. ✅ CLOSED Round 3 — `client.go:287` renamed to `dbc.parsed`; doc.go list now agrees with the code.
- `[ ]` GO-A-4.2 — Many missing `[Type.Method]` cross-references for godoc rendering (10+ sites).
- `[ ]` GO-A-4.3 [types.go:158-160, 174-176] `Value()`/`IsExtended()`/`String()` lack their own godoc.
- `[ ]` GO-A-4.4 [result.go:134-155] `IssueCode` constants block uses trailing-line comments instead of leading godoc.
- `[ ]` GO-A-4.5 [dbc.go:33-37] Vector__XXX placeholder strip — describes "what" not "why".

#### Cat 5: Error message consistency

- `[ ]` GO-A-5.1 [excel.go:87,134,154,168] lowercase "excel"/"dbc" inconsistent across same file.
- `[ ]` GO-A-5.2 [yaml.go:28,97 vs excel.go] uppercase "YAML" but lowercase "excel" — cross-file format-name inconsistency.
- `[ ]` GO-A-5.3 [client.go:236+ widespread] `fmt.Errorf("ParseDBC: %w", err)` doubles up with typed `*Error` `aletheia <kind> error:` formatting.
- `[ ]` GO-A-5.4 [types.go:116, 131, 165, 181, 202, 227] numeric range error messages use 3 different framings.
- `[ ]` GO-A-5.5 [mock.go:113] "got X calls, have Y responses" naming mismatches surrounding var names.

#### Cat 30: Logging discipline

- `[x]` GO-A-30.1 **[client.go:287] `dbc.text_parsed` is a 16th log event not in the canonical 15-event vocabulary.** Verified absent from Python `LogEvent` enum + Go's own `doc.go:45-66` + C++ `client.cpp` (which emits `dbc.parsed` for both paths). **Cross-binding parity violation.** ✅ CLOSED Round 3 — Go now emits `dbc.parsed` at both DBC parse paths (parity with Python + C++); `docs/LOG_EVENTS.yaml` SSOT + per-binding parity tests prevent recurrence.
- `[ ]` GO-A-30.2 [client.go:252,287,521,576,790] lifecycle events use `slog.Info(name, k, v...)` variadic form rather than `LogAttrs`; cat 30 R18 says `LogAttrs` for hot paths.
- `[ ]` GO-A-30.3 [client.go:733-735, 740-742] `frame.processed` LogAttrs records carry `slog.String("response", ...)`; verify field-set parity with Python/C++.
- `[ ]` GO-A-30.4 [client.go:790-791] `stream.ended` field set vs Python/C++ — verify.

### Go Agent B (Correctness & Runtime) — ~95 findings

#### Cat 7: Strong type coverage (13 findings)

- `[ ]` GO-B-7.1 [dbc.go:37] `DbcSignal.Receivers []string` should be `[]NodeName` — newtype already exists.
- `[ ]` GO-B-7.2-7.13 — Similar across `DbcMessage.Senders`, `NewDbcMessage` parameter, `DbcNode.Name`, `DbcCommentTargetNode.Node`, `DbcCommentTargetMessage.ID/Extended` (re-implementing `(uint32,bool)` instead of `CanID`), `Signal string` (in `DbcCommentTargetSignal`/`DbcAttrTargetSignal`), `EnvVar string`, `DbcSignalGroup.Name`, `DbcValueTable.Name`, raw-string usage in `yaml.go`/`check.go`/`json.go signalNameByIndex`.

#### Cat 8: Interface design (7 findings)

- `[ ]` GO-B-8.1 [backend.go:33-72] `Backend` interface has 14 methods — large; thematic sub-interfaces (StreamingBackend, DbcBackend, FrameBackend) would reduce mock burden.
- `[ ]` GO-B-8.2 [backend.go:64-66] `BuildFrameBin`/`UpdateFrameBin` `numSignals uint32` parameter redundant with parallel slice lengths.
- `[ ]` GO-B-8.3 [dbc.go:300, 369, 415, 459, 524] Five sealed sum types each with one `*()` marker method; user must remember the sealing-method name per family.
- `[ ]` GO-B-8.4 [types.go:137-143] `CanID` interface has `Value()` and `IsExtended()` separately; no method to obtain `(uint32, bool)` atomically; every cgo call site re-derives.
- `[ ]` GO-B-8.5 [check.go:77-89] Inconsistent return shapes: `StaysBetween`/`Within` return `(CheckResult, error)`; `NeverExceeds` returns `CheckResult` directly.
- `[ ]` GO-B-8.6 [result.go:30] `(r *ExtractionResult) Get` could be value receiver.
- `[ ]` GO-B-8.7 [loader.go:9-17] Three boolean maps + `mergeConditions` would be better as typed enum with `Kind()`.

#### Cat 9: cgo safety (9 findings)

- `[ ]` GO-B-9.1 [ffi.go:103-110] `call_hs_init_rts` strdups 4 strings unfreed (documented); doesn't check `strdup` returning NULL.
- `[ ]` GO-B-9.2 [ffi.go:99-111] `args[]` stack-allocated array escapes via `&argv` to `hs_init` which may retain.
- `[ ]` GO-B-9.3 [ffi.go:387-389] `(*C.uint8_t)(unsafe.Pointer(&data[0]))` uses explicit pointer-take; should use `unsafe.SliceData(data)` for GC-compaction safety.
- `[ ]` GO-B-9.4 [ffi.go:540-542, 608-610] same hazard for `indices`/`nums`/`dens` slices.
- `[ ]` GO-B-9.5 [ffi.go:188-190] `filepath.Clean(libPath)` doesn't reject `..` traversal.
- `[ ]` GO-B-9.6 [ffi.go:182-186] `runtime.LockOSThread`/`hsInitMu.Lock` pairing implicit.
- `[ ]` GO-B-9.7 [ffi.go:565-573, 635-644, 684-692] `outErr` freed only if `outErr != nil`; no documented invariant `status != 0 ⟹ outErr != nil`.
- `[ ]` GO-B-9.8 [ffi.go:699] `outSize` capped at `MaxInt32` only; malicious return `outSize = 2^31 - 1` causes 2 GB allocation.
- `[ ]` GO-B-9.9 [ffi.go:165-177] `loadSym` requires LockOSThread but doesn't document the precondition.

#### Cat 10: Goroutine & concurrency (7 findings)

- `[ ]` GO-B-10.1 [client.go:46] `lockCh chan struct{}` semaphore is non-idiomatic vs `golang.org/x/sync/semaphore`.
- `[ ]` GO-B-10.2 [client.go:96-99] `Close` writes to `c.state`/`c.closed` only synced via lockCh; field-level "guarded by" annotation missing.
- `[ ]` GO-B-10.3 [client.go:48-55] 8 fields mutated under lock without per-field guard documentation.
- `[ ]` GO-B-10.4 [ffi.go:125-129] `hsInitMu` package state; logger call inside critical section unusual.
- `[ ]` GO-B-10.5 [mock.go:25-30] `MockBackend.mu` correct; no race issue.
- `[ ]` GO-B-10.6 [cancel_test.go:43-48] `gateBackend.Process` records call then blocks on `<-b.release`; goroutine leak hazard if test crashes mid-test.
- `[ ]` GO-B-10.7 [client.go:611-634] `SendFrames` holds lockCh for entire batch; per-frame ctx checks correct but in-flight FFI call still runs to completion.

#### Cat 11: Serialization fidelity (9 findings)

- `[ ]` GO-B-11.1 [json.go:1976-1981] `parseDbcSignal` silently defaults `IsSigned=false` on missing field; no warning/error.
- `[ ]` GO-B-11.2 [json.go:1059-1064] `signalNameByIndex` synthesizes `"signal_N"` on OOB instead of error.
- `[ ]` GO-B-11.3 [json.go:712-720] `getString`/`getBool`/`getArray`/`getObject` silently default on missing; cross-binding: Python/C++ may surface error where Go silently substitutes.
- `[ ]` GO-B-11.4 [json.go:884] `parseValidationResponse` reads `getBool(m, "has_errors")` — verify camelCase vs other fields.
- `[ ]` GO-B-11.5 [json.go:1086-1110] `parseFrameResponse` accepts `"fails"` for violation; verify against `Protocol/ResponseFormat.agda`.
- `[ ]` GO-B-11.6 [json.go:1011-1012] Binary extraction reads `int64(LittleEndian.Uint64(...))` — bit-reinterpret cast.
- `[ ]` GO-B-11.7 [json.go:1015-1018] Binary `value = float64(num)/float64(den)` silently produces 0 when `den==0`.
- `[ ]` GO-B-11.8 [json.go:103-258] `serializeDBC` emits 9 fields under `dbc`; verify exhaustive against Agda.
- `[ ]` GO-B-11.9 [json.go:629-635] `parseRational` accepts negative denominators by sign-flip; comment-needed.

#### Cat 12: Parsing robustness (11 findings)

- `[ ]` GO-B-12.1 (= 11.1) silent IsSigned default.
- `[ ]` GO-B-12.2 (= 11.2) signalNameByIndex synthesis swallows OOB.
- `[ ]` GO-B-12.3-12.6 [json.go:1079-1080, 826-840, 805-818, 1141-1155] `parseFrameResponse`/`parseEventAck`/`parseSuccessResponse`/`parseStreamResponse` accept narrow status sets; cross-binding hazard if Agda evolves.
- `[ ]` GO-B-12.7 [json.go:1308-1318] `parseDbcDefinition` iterates `getArray(j, "messages")` — null-vs-empty distinction silently lost.
- `[ ]` GO-B-12.8 [json.go:1241-1245] `parseDbcTextResponse` reads `m["text"].(string)` directly; null-vs-missing produces same error.
- `[ ]` GO-B-12.9 [yaml.go:90-93] Double-parse pattern (typed + untyped); behavioral divergence hazard.
- `[ ]` GO-B-12.10 [cancel_test.go:82-87] `_, _ := b.Process(nil, "")` discards response (test-only).
- `[ ]` GO-B-12.11 [json.go:1099-1101] `propType != "property"` error message confuses missing vs empty `""`.

#### Cat 13: FFI lifecycle (7 findings)

- `[ ]` GO-B-13.1 [ffi.go:198-203] dlopen handle never closed (correct per RTS-thread retention); StablePtr cost persists until process exit.
- `[ ]` GO-B-13.2 [ffi.go:303-310] `hs_init` once-per-process, no `hs_exit`.
- `[ ]` GO-B-13.3 [client.go:88-101] `Close` blocks on lock with no ctx.
- `[ ]` GO-B-13.4 [client.go:65-79] `NewClient` panics in option leak StablePtr.
- `[ ]` GO-B-13.5 [ffi.go:705-710] `Close` doesn't nil-check `b.closeFn`.
- `[ ]` GO-B-13.6 [mock.go:218-219] `MockBackend.Close` is no-op; no hook for tests verifying close.
- `[ ]` GO-B-13.7 [ffi_nocgo.go:79] No-cgo Close silently succeeds; user with `CGO_ENABLED=0` gets confusing error pattern.

#### Cat 14: Test adequacy

- `[ ]` GO-B-14.1 (a) Baseline coverage adequate.
- `[ ]` GO-B-14.2 (b) [mock.go vs ffi.go] `MockBackend.ExtractSignalsBin` returns `ErrBinaryPathUnsupported` while real FFI returns binary; documented divergence with no test.
- `[ ]` GO-B-14.3 (c) Cross-binding mock agreement absent.
- `[ ]` GO-B-14.4 (d) [mock.go:124-128 vs ffi.go:370] No real-vs-mock divergence test for `SendFrameBinary`.
- `[ ]` GO-B-14.5 (e) Regression test discipline: no documented mapping between bug fixes and guarding tests.
- `[ ]` GO-B-14.6 (f) **R18 NEW:** `go test -shuffle=on -count=1 -race` passes — verified.
- `[ ]` GO-B-14.7 (g) **R18 NEW:** No mutation testing infrastructure (`gomut`/`go-mutesting`); no CI lane.
- `[ ]` GO-B-14.8 [cancel_test.go:99-105] `defer close(release)` followed by `defer c.Close()`; reverse-execution-order subtle.

#### Cat 23: Error wrapping & sentinels (6 findings)

- `[ ]` GO-B-23.1 [error.go:13] `ErrBinaryPathUnsupported` string sentinel; could be typed.
- `[ ]` GO-B-23.2 [client.go:236+] `fmt.Errorf("ParseDBC: %w", err)` adds method name only, not "what was attempted".
- `[ ]` GO-B-23.3 [error.go:58] Error format uses `:` 3× as separator.
- `[ ]` GO-B-23.4 [error.go:148-153] No `wrapState`/`wrapFFI` constructors paired with `wrapProtocol`/`wrapValidation`.
- `[ ]` GO-B-23.5 [json.go:1119-1121] Violation parsing's `*Error` lacks Cause; `errors.Is` can't match nested.
- `[ ]` GO-B-23.6 [error.go:67-126] No "unknown code" fallback sentinel beyond `IssueUnknown`.

#### Cat 24: nil & zero-value (9 findings)

- `[ ]` GO-B-24.1 **[dbc.go:651-655] `copyMessage` doc says "deep copy" but `signalIndex` map pointer is shared; mutation on returned copy corrupts source.**
- `[ ]` GO-B-24.2-24.4 — `NewClient`/`NewDbcDefinition` zero-value-vs-constructed hazards.
- `[ ]` GO-B-24.5-24.6 [json.go:108-110, 152-154] Explicit nil-vs-empty conversion for `receivers`/`senders` — good practice.
- `[ ]` GO-B-24.7 [result.go:101] `Enrichment *ViolationEnrichment` no `omitempty` JSON tag.
- `[ ]` GO-B-24.8-24.9 [types.go:131-134, 200-205] `BitLength{}=0` and `DLC{}=0` zero values may be invalid domain values.

#### Cat 25: Context propagation (8 findings)

- `[ ]` GO-B-25.1-25.5 [client.go:733, 740, 802, 825, 866+] Multiple log calls discard ctx (use `context.Background()`); `sendFrameLocked`/`enrichViolation`/`extract*` helpers don't take ctx.
- `[ ]` GO-B-25.6-25.8 — `lock(ctx)` correct; `SendFrames` cooperative cancellation correct.

#### Cat 26: Channel & goroutine lifecycle

- `[ ]` GO-B-26.1-26.5 — `lockCh` 1-deep semaphore correct; tests use buffered channels appropriately; no goroutines in production.

#### Cat 27: Hot-path performance (11 findings, including R18 leak sub-checks)

- `[ ]` GO-B-27.1 [client.go:251-253, 287, 521, 576, 791] `if c.logger != nil` then `Info`/`LogAttrs` — no `Enabled(ctx, level)` short-circuit; debug-disabled path still constructs Args.
- `[ ]` GO-B-27.2 [client.go:733-744] Per-frame `LogAttrs` allocation; cf. Python R12 regression `feedback_logging_fast_path.md`.
- `[ ]` GO-B-27.3 [client.go:725-729] Per-frame `make(FramePayload, len(data))+copy` for caller-mutation defense.
- `[ ]` GO-B-27.4 [client.go:893] `frameKey{...data: string(data)}` per-frame string copy.
- `[ ]` GO-B-27.5 [json.go:46-47] `serializeDataFrame` `Builder.String()` allocates heap copy.
- `[ ]` GO-B-27.6-27.9 **R18 NEW:** Long-run stability sub-checks (a) FD count delta, (b) goroutine count delta, (c) RSS delta, (d) StablePtr accounting — **all four ABSENT**, no stability bench captures any of them.
- `[ ]` GO-B-27.10 [client.go:725-729] FramePayload copy gated on `c.lastFrames != nil` — acceptable.
- `[ ]` GO-B-27.11 [json.go:1006-1018] Binary extraction loop allocates SignalValue per iteration.

#### Cat 28: Security at cgo boundary (9 findings)

- `[ ]` GO-B-28.1 [ffi.go:172-176] `dlerror` raw-concat (safe).
- `[ ]` GO-B-28.2 [ffi.go:188-189] `filepath.Clean` doesn't block `..` traversal.
- `[ ]` GO-B-28.3 **R18 NEW:** [ffi.go:690-700] `outSize` bounded only by `MaxInt32`; PROTOCOL.md has no `§ Limits`.
- `[ ]` GO-B-28.4 **R18 NEW:** [json.go:103-258] `serializeDBC` accepts arbitrary cardinalities.
- `[ ]` GO-B-28.5 **R18 NEW:** [yaml.go:14-19] `LoadChecksFromYAML` accepts arbitrary YAML; no size cap.
- `[ ]` GO-B-28.6 **R18 NEW:** [json.go:471-606] `serializeFormulaDepth=100` enforces depth, no breadth bound.
- `[ ]` GO-B-28.7 **R18 NEW:** [error.go] No `*aletheia.InputBoundExceededError` typed error. (Cf. UR-2.7.)
- `[ ]` GO-B-28.8 [json.go:712-720] `getString` discards type-assertion failures silently.
- `[ ]` GO-B-28.9 [ffi.go:170-171] `dlerror` clear-then-call has thread race; mitigated by LockOSThread but only for ctor.

#### Cat 29: File I/O & encoding

- `[ ]` GO-B-29.1-29.8 [yaml.go:25, 39-49, 47-48] No size cap; TOCTOU window between `Stat` and `ReadFile`; "not a file → inline YAML" heuristic surprises.
- `[ ]` GO-B-29.5-29.7 — No `bufio.Scanner` 64KB default; no `ioutil.*`; no UTF-8 validation on JSON strings.

#### Cat 33: Dynamic correctness analysis (NEW R18) — 8 findings, ALL absent

- `[ ]` GO-B-33.1 (a) **No sanitizer build matrix.** No `//go:build asan`, no `CGO_CFLAGS=-fsanitize=address` documented in `docs/architecture/CGO_NOTES.md` (file does not exist).
- `[ ]` GO-B-33.2 (b) **No native Go fuzz tests** (`testing.F`). `grep -rn "func Fuzz" aletheia/` empty. Required: `FuzzParseResponse`, `FuzzMarshalCommand`, `FuzzDecodeBinaryFrame`, `FuzzParseRationalNumber`, `FuzzParseDBCJSON`.
- `[ ]` GO-B-33.3 (b) **No `testdata/fuzz/` seed corpus.**
- `[ ]` GO-B-33.4 (c) **No `testing/quick` property tests.** Required: round-trip pairs + `MockBackend`/`FFIBackend` parity invariants.
- `[ ]` GO-B-33.5 (c) No mock-vs-real property-based assertion infrastructure.
- `[ ]` GO-B-33.6 (d) **No cross-binding integration test.** `cross_binding_integration_test.go` does not exist.
- `[ ]` GO-B-33.7 (d) No matching Python/C++ entries.
- `[ ]` GO-B-33.8 No CI lane for any of (a)-(d).

### Go system-level — ~50 findings

#### Cat 15: API ergonomics

- `[ ]` GO-S-15.1 [dbc.go:67] `NewDbcMessage` 6 positional parameters; R17-DEF-2 commit-3 added 5th `senders []string` as silent breaking signature change.
- `[ ]` GO-S-15.2 [check.go:80, 143, 256] Mixed return shapes across CheckSignalBuilder chain.
- `[ ]` GO-S-15.3 [client.go:65, 82] `Close` blocks indefinitely; breaks `io.Closer` contract.
- `[ ]` GO-S-15.4 [client.go:46, 88] `Close` always returns nil; no diagnostic on first vs subsequent.
- `[ ]` GO-S-15.5 [client.go:529] `AddChecks` always overwrites; name implies append; misleading.
- `[ ]` GO-S-15.6 [types.go:24, 41, 44] Three float64 wrappers (PhysicalValue/Delta/Tolerance) without Stringer.
- `[ ]` GO-S-15.7 [error.go:48-53] `Error.Code` string field; `IssueCode` is newtype but `ErrorCode` constants are bare strings.
- `[ ]` GO-S-15.8 [result.go:69] `Verdict` int with iota; out-of-range value formats as "unknown" but parser rejects "unknown".
- `[ ]` GO-S-15.9 [mock.go:212-216] `MockBackend.ExtractSignalsBin` divergence undocumented on `Backend.ExtractSignalsBin` interface.

#### Cat 16: Package boundaries

- `[ ]` GO-S-16.1-16.5 — `NewValidationError`/`WrapValidationError` (error.go:166-175), `ContainsMuxValue` (dbc.go:180-187), `DispatchSimple`/`DispatchWhen` (loader.go:56-83), `MockBackend` (in core not test subpackage), `dlcTable`/`bytesToDlcTable` redundancy. All exported "for external loaders" without `internal/` package.

#### Cat 17: Extensibility

- `[ ]` GO-S-17.1-17.5 — Sealed `Predicate`/`Formula` ADT extension points are N-call-site (no extension hook), `Backend` sealed (no middleware), `IssueCode` cross-binding-sync no compile gate.

#### Cat 18: Dependency discipline

- `[ ]` GO-S-18.1 [go.mod:1-7] Single dep `gopkg.in/yaml.v3 v3.0.1`. Could be eliminated with line-based decoder.
- `[ ]` GO-S-18.2 [excel/go.mod:14-29] 9 indirect deps including `golang.org/x/crypto`, `golang.org/x/net`.
- `[ ]` GO-S-18.3 **[excel/go.mod:21] `require github.com/aletheia-automotive/aletheia-go v0.0.0` — published-module hazard.**
- `[ ]` GO-S-18.4 [go.mod:3-5] Go 1.24 floor undocumented; pinning policy implicit.
- `[ ]` GO-S-18.5 [go.sum:1-4] `gopkg.in/check.v1 v0.0.0-2016...` 9-year-old indirect; reproducible-build chain-of-custody concern.

#### Cat 19: Domain model fidelity

- `[ ]` GO-S-19.1 [types.go:24] `PhysicalValue float64` — Agda uses ℚ; Go collapses precision at FFI boundary.
- `[ ]` GO-S-19.2-19.7 — `DLC`-as-code-vs-byte-count, Timestamp epoch undocumented, `IsSigned bool` discriminator, mux nesting depth undocumented, `Violation.Reason string` flatten, `EnvironmentVar` field gap.

#### Cat 20: Design coherence

- `[ ]` GO-S-20.1-20.6 — `Client` 11 fields mixing 4 concerns; `lastFrameData` redundant ID; lockCh non-idiomatic; `extractionErrorMessages` array-indexed-by-byte; `CheckSignalBuilder` thin wrapper; const-block colocation.

#### Cat 21: Use-case coverage

- `[ ]` GO-S-21.1-21.6 — No streaming `SendFrames` iter; no `FormatDBCJSON`; check-builder gaps; no candump/asc loader; no `NewClientFromPath` convenience; `NewDbcDefinition` minimal.

#### Cat 22: Cross-layer alignment (KEY parity findings)

- `[x]` GO-S-22.1 **`dbc.text_parsed` log event divergence** (cf. GO-A-30.1). ✅ CLOSED Round 3 — see GO-A-30.1.
- `[ ]` GO-S-22.2 **`rts.cores_mismatch` emission site differs across all 3 bindings.**
- `[ ]` GO-S-22.3-22.10 — `parseSuccessResponse` consistent; `extendedIDFlag` encoding documentation gap; `signalNameByIndex` synthesis masks protocol violation; no synthetic-vs-real signal-name discriminator; `floatToRational` 10⁹ precision floor vs Python `Fraction`; `parseCanIDFields` float64 mantissa precision footnote; `checkErrorStatus` strict-error contract; `unresolvedValueDescs` wire-key parity (verify byte-identical).

#### Cat 31, 32

- `[ ]` GO-S-31.1-31.6 — `go.work` replace policy clarification; `excel/go.mod v0.0.0` placeholder hazard; macOS-portable `cgo` build tag; testing partition; `toolchain` pin documentation; `internal/` subpackage missing.
- `[ ]` GO-S-32.1-32.7 — `encoding/json` map sort dependence; `extractLastKnownValues` sort-comment backward; `extractSignalValues` map iteration nondeterminism; `frameKey.data string()` allocation OK.

---

## C++ findings

### C++ Agent A (Hygiene & Style) — 11 findings

- `[ ]` CPP-A-1.1 [validation.hpp:57] `struct ParsedDBC` capital `DBC` while every other DBC type uses camelcase `Dbc`.
- `[ ]` CPP-A-1.2 [json_parse.cpp + json_serialize.cpp 22+22 helpers] `static auto` vs `namespace { … }` mixed across same compilation tree.
- `[ ]` CPP-A-1.3 [tests/test_feature_matrix_parity.cpp:37-40] `kValidStatuses`/`kBindings` Google-style `k`-prefix vs project snake_case.
- `[ ]` CPP-A-1.4 [tests/integration_tests.cpp:29 + dbc_corpus_parity_tests.cpp:50 + doc_example_tests.cpp:283] Three `find_lib` patterns.
- `[ ]` CPP-A-2.1 [tests/integration_tests.cpp:479-481] Sole clang-format violation.
- `[ ]` CPP-A-3.1 [validation.hpp:49] Mid-file `#include <aletheia/dbc.hpp>` after namespace closes.
- `[ ]` CPP-A-3.2 [tests/test_helpers.hpp:14] Cross-tree relative `"../src/detail/json.hpp"` reach.
- `[ ]` CPP-A-4.1 [tests/integration_tests.cpp:1409-1440] Anonymous-namespace `capture_stderr<F>` template defined but never called.
- `[ ]` CPP-A-5.* — No const-correctness findings.
- `[ ]` CPP-A-6.1 [tests/integration_tests.cpp:1400-1407] Stale comment claiming `std::println(stderr, ...)` warning that was migrated to `Logger::warn`.
- `[ ]` CPP-A-6.2 [tests/integration_tests.cpp:1442] Test-case name says "warns" but assertion only inspects `rts_mismatch_info()`.
- `[ ]` CPP-A-30.1 [src/client.cpp:799] Wasteful `std::string{e.what()}` allocation in warn path.

### C++ Agent B (Correctness & Runtime) — ~76 findings

#### Cat 7: Strong type coverage (12 findings, including missing newtypes for NodeName/EnvVarName/AttributeName/SignalGroupName, and CanId-vs-`(uint32, bool)` pair re-implementation in target structs)

#### Cat 8: Ownership & RAII (5 findings, including the **rts_cores leak when ctor body throws** — Finding 8.2 is the strongest leak)

- `[ ]` CPP-B-8.2 **[ffi_backend.cpp:135-140] `rts_cores < 1` validation runs AFTER `handle_(dlopen(...))` member-init; throw on `rts_cores == 0` leaks the open library handle (defaulted dtor doesn't dlclose, body catch doesn't run for member-init throws).**
- `[ ]` CPP-B-8.1, 8.3-8.5 — Constructor catch dlclose unconditionally wrong on second-construct case; LogCallback lifetime undocumented; mutable `LazyIndex` on const methods.

#### Cat 9: Memory safety (5 findings)

- `[ ]` CPP-B-9.1 (= 8.2) rts_cores leak.
- `[ ]` CPP-B-9.2 [client.cpp:241, 261] `parse_extraction_bin` UB on null `buf.data()` + offset arithmetic.
- `[ ]` CPP-B-9.3 [json_parse.cpp:135-153] `j.get<int64_t>()` without overflow check.
- `[ ]` CPP-B-9.4 [client.cpp:266-272] `Rational{num, den}` direct construction with `den < 0` trips assert in debug, constructs unnormalised in release.
- `[ ]` CPP-B-9.5-9.6 — `std::span` lifetime documentation; `[&]` capture safety.

#### Cat 10: Thread safety (4 findings, including **LazyIndex racy across threads** — `DbcDefinition` shared between threads is corrupted)

#### Cat 11: Serialization fidelity (6 findings, including **silent drop of `unresolvedValueDescs` on JSON parse path**)

- `[x]` CPP-B-11.3 [json_serialize.cpp:299-309 vs json_parse.cpp:584-593] **Serializer emits `unresolvedValueDescs`; parser doesn't read it. JSON-roundtrip drops Track E.8 data.** ✅ CLOSED Round 6 — added `parse_raw_value_desc` static helper to `cpp/src/json_parse.cpp` (mirrors `raw_value_desc_to_json` in `json_serialize.cpp`) plus the `if (j.contains("unresolvedValueDescs"))` block in `parse_dbc_definition` and the matching aggregate-init field. Three regression tests in `cpp/tests/unit_tests_json.cpp` (`[trackE]` tag): standalone parse, full serialize→parse roundtrip, and missing-key tolerance. Gate-shape verified by reverting the parser change and re-running — 2 of 3 tests fail with `0 == 1` on `unresolved_value_descriptions.size()`; restoring the change returns them to green.

#### Cat 12: Parsing robustness (7 findings, including documentation of which client methods each `parse_*` parser serves)

#### Cat 13: FFI lifecycle (6 findings, including the **catch dlclose-vs-comment contradiction** documented at lines 188-191 vs 194-195)

#### Cat 14: Test adequacy

- `[ ]` CPP-B-14.1-14.10 — Various: no unit tests for `parse_dbc_text_response`, `format_dbc_text`, truncated-buffer parsing, malformed binary FFI, `unresolvedValueDescs` drop regression, `Rational::from_double` edge cases, mutation testing infrastructure.

#### Cat 23: Exception safety (8 findings)

- `[ ]` CPP-B-23.1-23.8 — Decorative `current_exception` in destructor; missing noexcept on `~AletheiaClient`; `[[nodiscard]]` builders throw without doc; `formula_to_json` runtime_error escapes; asymmetric try/catch coverage; `Rational(int64,int64)` could be noexcept; `Strong<Tag,T>::Strong` could be noexcept; FFI `process()` allows throw.

#### Cat 24: Undefined behavior (9 findings)

- `[ ]` CPP-B-24.1-24.9 — `parse_extraction_bin` null-span UB; `Rational::from_double` int64 overflow; duplicate INT64_MIN check idiom; `static_cast<int>` narrowing; `reinterpret_cast` (NOLINTed); 32-bit golden-ratio in 64-bit hash combine; `den < 0` assert trip.

#### Cat 25: Data race (4 findings)

- `[ ]` CPP-B-25.1-25.4 — `rts_mismatch_` non-locked read; no `std::atomic` anywhere; `LazyIndex` racy; `Logger::min_` non-atomic.

#### Cat 26: Hot-path performance (10 findings, including R18 long-run leak sub-checks all absent)

- `[ ]` CPP-B-26.1-26.10 — `collect_matching_signals` O(n*m); `std::map` insertion log-cost; `emplace` vs `try_emplace`; `last_frames_.insert_or_assign` payload copy; `cache_` `std::map` heterogeneous lookup; `error_code_table` linear scan (cold path); `parse_issue_code` 21-clause if-chain (cold path); **stability benchmark absent** (no RSS/FD/thread/malloc_info sub-checks); `cache_full` warn rate-limit absent; `SignalValue` default-construct asserts in debug.

#### Cat 27: Standard library idiomatic usage (10 findings)

#### Cat 28: Security at FFI boundary (13 findings)

- `[ ]` CPP-B-28.1 **No `aletheia::InputBoundExceededError` exists.** (Cf. UR-2.6.)
- `[ ]` CPP-B-28.2 **PROTOCOL.md has no `§ Limits`.** (Cf. UR-2.1.)
- `[ ]` CPP-B-28.3 [json_parse.cpp 10 sites] `Json::parse(input)` no depth/size limit; nlohmann default.
- `[ ]` CPP-B-28.4-28.13 — `process()` unbounded input; arrays unbounded; `arr.size()` no cap; multiple `parse_*` collection loops; `signals.count` u32 unbounded; `parse_extraction_bin` uint16 cap correct; Excel/YAML loaders unbounded; OpenXLSX cell-type parse without try/catch; `formula_to_json` depth-only.

#### Cat 29: File I/O (7 findings)

#### Cat 33: Dynamic correctness analysis (NEW R18) — 6 findings, ALL absent

- `[ ]` CPP-B-33.1 (a) **No ASan+UBSan CI lane.**
- `[ ]` CPP-B-33.2 (b) **No libFuzzer harnesses** in `cpp/tests/fuzz/` (directory does not exist).
- `[ ]` CPP-B-33.3 (c) **No Catch2 GENERATE-based property tests.**
- `[ ]` CPP-B-33.4 (d) **No `cpp/tests/cross_binding_integration_tests.cpp`.**
- `[ ]` CPP-B-33.5 (a) No `docs/architecture/CGO_NOTES.md` documenting GHC RTS / sanitizer interaction.
- `[ ]` CPP-B-33.6 Catch2 ships `fuzz_*.cpp` infrastructure free; absence not justified by tooling friction.

### C++ system-level — ~75 findings

(Per Universal Rule tripwires UR-1 / UR-2 / UR-3 already listed above; system-level adds:)

#### Cat 15: API surface (8 findings)

- `[ ]` CPP-S-15.1 [src/mock_backend.cpp:11-13 + detail/mock_backend.hpp:18-79] `make_mock_backend()` exposed in public header but `MockBackend` class itself in `cpp/src/detail/`; user gets usable-but-undriveable test stub.
- `[ ]` CPP-S-15.2 [client.hpp:71-133] Every operation method takes `std::stop_token` even where it doesn't block; `format_dbc_text(std::stop_token{}, dbc)` boilerplate.
- `[ ]` CPP-S-15.3 [backend.hpp:51] `IBackend::init() -> void*` vs `Result<>` inconsistent throw-from-ctor.
- `[ ]` CPP-S-15.4-15.8 — Umbrella header IWYU costs; `rts_mismatch_info` in `IBackend` even though FfiBackend-specific; `CheckResult::to_formula()` + `formula()` two ways to ask same question; `Logger::log` doesn't accept dynamic-arity `std::vector<LogField>`; `Rational::to_double()` does double duty as printable + lossy fallback.

#### Cat 16, 17, 18 — encapsulation, extensibility, build system (~20 findings)

#### Cat 19, 20, 21 — domain model, design coherence, use-case coverage (~20 findings)

#### Cat 22: Cross-layer alignment (KEY parity findings, ~13)

- `[x]` CPP-S-22.1 **[json_parse.cpp:584-593 vs json_serialize.cpp:333-345] `unresolvedValueDescs` JSON serializer-parser asymmetry.** (Cf. CPP-B-11.3.) Python handles it; C++ drops it. ✅ CLOSED Round 6 — closed by the same parser fix as CPP-B-11.3; cross-binding parity restored across Python (`_helpers.py:670`), Go (`json.go:1344`), and now C++ (`json_parse.cpp::parse_raw_value_desc`).
- `[x]` CPP-S-22.2 [client.cpp:162-163, 178-179 vs Go client.go:287] `dbc.parsed` for both paths in C++; Go has 16th `dbc.text_parsed`. ✅ CLOSED Round 3 — fixed on the Go side (client.go:287 → `dbc.parsed`); C++ behavior was already correct.
- `[ ]` CPP-S-22.3 **[client.cpp:711] `cache_.size() < max_cache_size = 256`. Python and Go have NO equivalent cap.**
- `[ ]` CPP-S-22.4 **[json_serialize.cpp:394] `max_formula_depth = 100`. Python and Go have no equivalent.**
- `[ ]` CPP-S-22.5 [ffi_backend.cpp:31] `max_can_fd_payload_bytes = 64`. Verify Python/Go enforce same.
- `[ ]` CPP-S-22.6 [client.cpp:75-87] Destructor swallows `close()` exceptions; no separate `Result<void> close()`.
- `[ ]` CPP-S-22.7 [validation.hpp:11-34 + json_parse.cpp:155-198] 21 IssueCode values vs Python `validation.py` — verify byte-identity.
- `[ ]` CPP-S-22.8 [error.hpp:35-94 + json_parse.cpp:30-88] 51 ErrorCodes vs Python `error_codes.py` — verify byte-identity.
- `[ ]` CPP-S-22.9 [client.cpp:484-498] `frame.processed` `initializer_list<LogField>` allocated even when min_>Debug; no `should_log(level)` short-circuit.
- `[ ]` CPP-S-22.10 [json_serialize.cpp:382, 386] `delta`/`tolerance` emitted as bare `double`, not `{numerator, denominator}`. Cross-layer precision loss.
- `[ ]` CPP-S-22.11 **[client.cpp:301-329] `parse_extraction_bin` returns `{}` (empty success) on truncation.** Silent corruption.
- `[ ]` CPP-S-22.12 [dbc.hpp:191-237 + json_serialize.cpp:146-272] Discriminator strings (`"network"`/`"node"`/...) scattered across 4 places.
- `[ ]` CPP-S-22.13 Predicate-only DSL form parity TBD.

#### Cat 31, 32 (~14 findings)

---

## Python findings

### Python Agent A (Hygiene & Style) — ~30 findings

#### Cat 1: PEP 8 & formatting (4)

- `[ ]` PY-A-1.1 [dbc_converter.py:94] `encoding='utf-8'` (single quotes) vs project-wide double-quote convention.
- `[ ]` PY-A-1.2 [dsl.py 25 sites] LTL JSON wire dicts use single quotes; protocols.py/_client.py/cli.py use double.
- `[ ]` PY-A-1.3 [cli.py:106] Missing blank line.
- `[ ]` PY-A-1.4 [protocols.py:546-554+] Forward references mix quote styles.

#### Cat 2: Naming conventions (3)

- `[ ]` PY-A-2.1 [protocols.py:31-41] `PredicateType.LESS_THAN_OR_EQUAL = "lessThanOrEqual"` enum mapping.
- `[ ]` PY-A-2.2 [_log.py:32] `class LogEvent(str, Enum)` could be `StrEnum` (Python 3.11+; project requires ≥3.12).
- `[ ]` PY-A-2.3 [checks.py:43] `check_severity` field name duplicates surrounding context.

#### Cat 3: Dead code (2)

- `[ ]` PY-A-3.1 [__init__.py:117, 124, 130] `except ... as _e` underscore convention misleading (variable IS used).
- `[ ]` PY-A-3.2 [cli.py:54-59] `if TYPE_CHECKING:` block — confirm intentional.

#### Cat 4: Comment/doc quality (9)

- `[ ]` PY-A-4.1 [cli.py:1-15] Module docstring lists 5 subcommands; implementation registers 6 (missing `format-dbc`).
- `[ ]` PY-A-4.2 [__init__.py:14-15 + client/__init__.py:25-26] Docstring example uses `Fraction(0)` default but type signature is `Fraction = Fraction(0)`; example misleading.
- `[ ]` PY-A-4.3 [__init__.py:14] `frame_bytes` undefined in docstring example.
- `[ ]` PY-A-4.4-4.9 — `_load_dbc`/`_load_checks_from_args` Args/Raises inconsistent; `iter_can_log` docstring tuple-name vs Yields-line mismatch; `dbc_to_json`/`dbc_to_text` GHC-RTS-init inaccurate; DOC_FILES tuple ordering mismatch with AGENTS.md L711-715; Excel mux validation docstring gap; protocols TypedDict docstring asymmetric provenance commentary.

#### Cat 5: Error message consistency (5)

- `[ ]` PY-A-5.1 [_helpers.py 5 sites + 8 sites] `f"... got {type(item)}"` vs `type(...).__name__` inconsistent.
- `[ ]` PY-A-5.2 [checks.py 5 sites] Three different framings for numeric range errors.
- `[ ]` PY-A-5.3 [_loader_utils.py 5 sites] "missing or invalid" hides which failed.
- `[ ]` PY-A-5.4 [_signal_ops.py + _client.py + cli.py 14+ sites] Unicode em-dash `—` in error strings; Go/C++ use ASCII `-`.
- `[ ]` PY-A-5.5 [protocols.py:466+] LTL predicate value fields typed `float` but DBC numeric fields use `Fraction`.

#### Cat 6: Module organization (4)

- `[ ]` PY-A-6.1 [protocols.py] **976 lines — 97.6% of pylint 1000-line cap.**
- `[ ]` PY-A-6.2 [__init__.py:85-89] Top-level re-exports only `DBCDefinition` + `PropertyResultEntry`; sibling DBC/LTL types not re-exported.
- `[ ]` PY-A-6.3 [_client.py 901 / cli.py 944 / dsl.py 869] All near 1000-line threshold.
- `[ ]` PY-A-6.4 [__init__.py:53-65] `# pylint: disable=cyclic-import` rationale doesn't link to memory file.

#### Cat 27, 28, 32, 33

- `[ ]` PY-A-27.1 [dbc_converter.py:94] sole `'utf-8'` (single quotes) site.
- `[ ]` PY-A-27.2 [yaml_loader.py:134, 139] Could factor `_open_for_yaml(p)` helper.
- `[ ]` PY-A-28.1 [_log.py:80-116] `log_event` doesn't support `exc_info=True`.
- `[ ]` PY-A-28.2 [_log.py:75-77] `f"{k}={v}"` rendering ungreppable when value contains spaces.
- `[ ]` PY-A-28.3 [_client.py 10+ sites] `canId`/`numResults`/`numFails` camelCase fields vs Go `slog` snake_case convention.
- `[ ]` PY-A-28.4 [_log.py:111] `event` first key in JSON; human fallback msg starts with event value but field-iter order may differ.
- `[ ]` PY-A-32.1 [__init__.py:14] `frame_bytes` undefined in docstring; harness injects but standalone doc reader gets undefined.
- `[ ]` PY-A-32.2 [test_doc_examples_harness.py:37-49] DOC_FILES order doesn't match AGENTS.md L711-715.
- `[ ]` PY-A-32.3 [__init__.py docstring] No `>>>` doctest examples; AGENTS.md mentions but codebase has zero.
- `[ ]` PY-A-32.4 [client/__init__.py:25-37] Docstring example `frames` undefined.
- `[ ]` PY-A-32.5 [docs/reference/CLI.md] CLI.md in DOC_FILES but uses bash/text fences; verify harness floor passes.
- `[ ]` PY-A-33.1 [cli.py:102-104] Exit codes conflate parse/runtime/I/O/FFI errors; argparse default 2 collides.
- `[ ]` PY-A-33.2 [cli.py:121-124] `_die` + `main()`'s except duplicate "Error: <msg>" formatting.
- `[ ]` PY-A-33.3 [cli.py:824-915] Subparsers without `description=`.
- `[ ]` PY-A-33.4 [cli.py:893-913] `mux-query` `--mux`/`--value` "both-or-neither" not enforced at parse-time.
- `[ ]` PY-A-33.5 [cli.py:577, 660-671, 710, 736] Banner + progress lines to stdout via `print` violate stderr/stdout discipline.
- `[ ]` PY-A-33.6 [__main__.py:11-15] `sys.exit(main())` direct without `__name__ == "__main__"` guard.
- `[ ]` PY-A-33.7 [cli.py] No `--quiet`/`--verbose`/`--log-level` global flag.

### Python Agent B (Correctness & Runtime) — ~75 findings

#### Cat 7: Type annotation coverage

- `[ ]` PY-B-7.1-7.3 — `dsl.Signal.name` mutable string; `_diags: dict[int, ...]` could be `NonNegativeInt`-keyed; `cast(list[dict[str, object]], results_raw)` lies about validation.

#### Cat 8: Strong type usage

- `[ ]` PY-B-8.1-8.7 — `dsl.Signal` predicates take `value: float` losing Fraction precision; CheckSignal builders same; `validate_payload_length(dlc: int, ...)` unbounded; `DBCMessage.dlc int` unbounded; `DBCSignal*.startBit`/`length` unconstrained; `to_signal_fraction` rejects bool buried in body; `RTSState.cores` typed plain int.

#### Cat 9: Error handling (6)

- `[ ]` PY-B-9.1-9.6 — Multiple `raise ProtocolError(...)` without `from None`/`from exc`; missing original payload context; signal-ops catches log only `error=str(exc)`; `iter_can_log on_error=skip` silently drops.

#### Cat 10: Resource safety

- `[ ]` PY-B-10.1 [_client.py:151] `close()` swallows partial-init state — `RTSState.refcount` leaks if `__enter__` raised between CDLL and aletheia_init.
- `[ ]` PY-B-10.2-10.5 — `lib.hs_init(byref(argv))` lifetime contract implicit; cleanup ordering across `aletheia_free_str`/`free_buf`/`raise`.

#### Cat 11: Serialization fidelity (5)

#### Cat 12: Parsing robustness (7)

- `[ ]` PY-B-12.1 [yaml_loader.py:137-145] `_load_yaml(source)` ambiguously dispatches str path-or-inline.
- `[ ]` PY-B-12.2-12.7 — Parser per-element validation asymmetry; `parse_finalization_results` cast without `is_object_list`; status-set narrowness; ack-byte fast-path tolerance; `parse_hex_data` accepts `0x` prefix without docstring disclosure.

#### Cat 13: FFI lifecycle (6)

#### Cat 14: Test adequacy (8)

- `[ ]` PY-B-14a.1 [test_cancellation.py:282-305] **3 tests intermittently fail under `python -X dev`** — timeout race revealed by cat 34(a). Standard lane masks them.
- `[ ]` PY-B-14b.1-14e.1 — No mock fidelity infrastructure; no cross-binding mock agreement; no real-vs-mock divergence harness; no regression-test mapping.
- `[ ]` PY-B-14f.1 **No `pytest-random-order` plugin** in `dev` extras. `pytest --random-order` errors `unrecognized arguments`.
- `[ ]` PY-B-14g.1 **No mutation testing** (`mutmut`/`cosmic-ray` absent).
- `[ ]` PY-B-14a.2 [conftest.py:54, 86] `_sample_dbc()` and `simple_dbc()` near-duplicate fixtures.

#### Cat 23: Concurrency & GIL (3)

- `[ ]` PY-B-23.1 [asyncio/_client.py:9-12] **Asyncio class doc says "one task at a time" but no runtime check enforces it.** Two awaits corrupt StreamState.
- `[ ]` PY-B-23.2 [_client.py:108-110] Sync class doc says not thread-safe; no mutex on `_caches.extraction`.
- `[ ]` PY-B-23.3 [_ffi.py:43] `RTSState._lock` reads outside lock implicit-GIL-safe.

#### Cat 24: Mutability (6)

#### Cat 25: Hot-path performance (incl R18 leak sub-checks)

- `[ ]` PY-B-25.1 [_client.py:571] `(ctypes.c_uint8 * len(data))(*data)` per-call allocation.
- `[ ]` PY-B-25.2 [_client.py:175] `dump_json(command).encode("utf-8")` per `_send_command`.
- `[ ]` PY-B-25.3a-25.3d **R18 NEW: All four long-run sub-checks ABSENT.** No RSS measurement, no FD count, no ctypes-handle accounting, no logger-handler delta.
- `[ ]` PY-B-25.4 [_client.py 7+ sites] `log_event` kwargs evaluated before isEnabledFor short-circuit.
- `[ ]` PY-B-25.5 [_client.py:587] `bytearray(data)` per-frame copy when `_diags` is non-empty.

#### Cat 26: Security / adversarial input (12 — NEW R18)

- `[ ]` PY-B-26.1-26.9 — Every entrypoint (`yaml_loader`, `dbc_converter`, `iter_can_log`, `excel_loader`, `cli.parse_hex_data`, `cli.parse_can_id`, `excel_loader._parse_message_id`, `_helpers.float_to_rational`) **has no bounds check.**
- `[ ]` PY-B-26.10 **No `aletheia.InputBoundExceededError` exception type.** (Cf. UR-2.5.)
- `[ ]` PY-B-26.11 [_ffi.py:213] `os.environ.get("ALETHEIA_LIB")` honored without permission check.
- `[ ]` PY-B-26.12 [yaml_loader.py:137-145] String dispatching to file path when matches on disk — path-confusion vector.

#### Cat 29, 30 (12)

#### Cat 34: Dynamic correctness analysis (NEW R18) — 6 findings, ALL absent

- `[ ]` PY-B-34.1 (a) **No `python -X dev` lane**. Standard lane masks 3 cancellation-test flakes (PY-B-14a.1).
- `[ ]` PY-B-34.2 (b) **No `hypothesis` dependency**.
- `[ ]` PY-B-34.3 (c) **No `atheris` dependency**, no `python/tests/fuzz/`.
- `[ ]` PY-B-34.4 (d) **No `python/tests/test_cross_binding_integration.py`**.
- `[ ]` PY-B-34.5 No `pytest-random-order` plugin.
- `[ ]` PY-B-34.6 [test_cancellation.py:282-305] 3 tests intermittently fail under `-X dev`.

### Python system-level — ~64 findings

#### Cat 15: API ergonomics

- `[x]` PY-S-15.1 **[asyncio/__init__.py:15] Docstring example shows `AletheiaClient(dbc=dbc_path)` — neither sync nor async `__init__` accepts `dbc=` kwarg. Example does not run.** ✅ CLOSED Round 4 — `dbc=dbc_path` replaced with `default_checks=checks` plus an `await client.parse_dbc_text(dbc_text)` call inside the `async with`, mirroring the cluster 13 CANCELLATION.md fix. Hallucination, not planned-then-dropped (verified via `git log -S "dbc=" -- python/aletheia/client/_client.py`).
- `[ ]` PY-S-15.2 [__init__.py:6-49] `result.get("VehicleSpeed", 0.0)` mismatch against `Fraction(0)` default policy.
- `[ ]` PY-S-15.3 **[_client.py:120-122] `default_checks` doc says "applied on every `start_stream`" — INCORRECT. Defaults applied via `add_checks()` only. Pit-of-failure.**
- `[ ]` PY-S-15.4-15.8 — Class doc thread-safety undersells; `dbc_to_json` path-only (no string overload); `parse_dbc*` returns union, others raise; `CANFrameTuple` positional access; `send_frame` keyword-only `extended`.

#### Cat 16: Package boundaries (8)

- `[ ]` PY-S-16.1 [protocols.py 976 lines] approaching pylint cap (cf. PY-A-6.1).
- `[ ]` PY-S-16.2-16.8 — Multi-concern files; cross-module reach `from ..client._client import AletheiaClient as _SyncClient`; `dbc_converter` reaches `client._helpers.dump_json`; loaders reach `_helpers.to_signal_fraction`; cyclic-import comment doesn't link to memory.

#### Cat 17, 18, 19, 20, 21 (~25 findings)

#### Cat 22: Cross-layer alignment (KEY)

- `[x]` PY-S-22.1 **Go's `dbc.text_parsed` is a 16th log event not in Python (the reference). Direct violation of "_log.py docstring 15 events".** Per AGENTS.md cat 22 "Python is the reference". ✅ CLOSED Round 3 — Go now matches Python's `LogEvent.DBC_PARSED = "dbc.parsed"`; new `python/tests/test_log_events_parity.py` anchors the enum to the cross-binding `docs/LOG_EVENTS.yaml` SSOT.
- `[ ]` PY-S-22.3 **No Python `Backend` Protocol.** Cross-binding mock-agreement gate per cat 14(c) is unsatisfiable.
- `[ ]` PY-S-22.4 [_client.py:534-535] `_ACK_BYTES` fast path Python-only; documented as gold standard.
- `[ ]` PY-S-22.5-22.9 — Send-error/remote shape divergence; `DBCRawValueDesc` not exported; `RTS_CORES_MISMATCH` field-name divergence Go vs Python; `event` key vs `msg` key in `slog` divergence; `dbc.parsed` field-set differs Go (carries `warnings`) vs Python (only `messages`).

#### Cat 31: Packaging hygiene (10)

- `[ ]` PY-S-31.1 [pyproject.toml:8] Hardcoded `version = "1.1.1"` — multiple-source-of-truth issue.
- `[ ]` PY-S-31.2 No `[project.urls]`.
- `[ ]` PY-S-31.3 No `keywords`.
- `[ ]` PY-S-31.4 **No `CHANGELOG.md`** (cf. UR-1.1).
- `[ ]` PY-S-31.5 [pyproject.toml:80-82] Permissive `*.pyi` glob.
- `[ ]` PY-S-31.6 No `[tool.setuptools_scm]` VCS-derived versioning.
- `[ ]` PY-S-31.7 [pyproject.toml:50, 56] `dev = ["aletheia[all]"]` self-reference indirection.
- `[ ]` PY-S-31.8 No Trove classifiers; modern PEP 639 SPDX-only would supersede.
- `[ ]` PY-S-31.9 [pyproject.toml:75-78] `aletheia.*` glob too broad.
- `[ ]` PY-S-31.10 No lock file (`uv.lock`/`requirements-dev.lock`).

---

## Documentation findings

### Docs Agent A (Hygiene) — ~73 findings

#### Cat 1: Accuracy (18 findings — module count drift, Phase status, CLI surface, dependency table staleness)

- `[ ]` DOC-A-1.1 [PROJECT_STATUS.md:446] "Agda modules: 243" — actual is 244 per `count-modules`.
- `[ ]` DOC-A-1.2 [PROJECT_STATUS.md:485] "All 242 Agda modules use `--safe --without-K`" — actual 243 of 244.
- `[ ]` DOC-A-1.3 [DESIGN.md:53] **"All 119 modules use --safe --without-K" — actual 244, off by 125.**
- `[ ]` DOC-A-1.4 [DESIGN.md:63] Same 119-module reference.
- `[ ]` DOC-A-1.5 [PITCH.md:289] **"all four binding stacks (Python, C++, Go, plus the LSP/CLI tooling)" — there is no LSP tooling.**
- `[ ]` DOC-A-1.6 [PITCH.md:289] Last update 2026-04-15; Tracks A-E completed 2026-05-03 → 2026-05-08.
- `[ ]` DOC-A-1.7 [PITCH.md:303] "Remaining: ... binary FFI for signal extraction" — already shipped.
- `[ ]` DOC-A-1.8 [PITCH.md:297] Lists 4 CLI subcommands; actual is 5 (per CLI.md L13).
- `[ ]` DOC-A-1.9 [PITCH.md:298] python-can claim flagged stale-prone (Phase 6 replacement pinned).
- `[ ]` DOC-A-1.10 [DEPENDENCIES.md:98] **`cantools` listed but removed in B.3.g (`2daa2fb` 2026-05-03).**
- `[ ]` DOC-A-1.11 [DEPENDENCIES.md:107-108] False entries: `argparse-addons`, `bitstruct`, `crccheck`, `diskcache`, `textparser`.
- `[ ]` DOC-A-1.12 [DEPENDENCIES.md:5] "Last Updated 2026-04-19" — one month stale.
- `[x]` DOC-A-1.13 **[CANCELLATION.md:150] Code uses `AletheiaClient(dbc=dbc_path, checks=load_checks())` — neither sync nor async `__init__` accepts `dbc=`/`checks=` kwargs.** ✅ CLOSED Round 4 — example rewritten to `AletheiaClient(default_checks=load_checks("checks.yaml"))` followed by `await client.parse_dbc_text(pathlib.Path(dbc_path).read_text(encoding="utf-8"))`. Hallucination, not planned-then-dropped (verified `git log -S "dbc=" -- python/aletheia/client/_client.py` returned no commits).
- `[x]` DOC-A-1.14 [CANCELLATION.md:302] References `AsyncAletheiaClient` — not a defined symbol. ✅ CLOSED Round 4 — replaced with `aletheia.asyncio.AletheiaClient` (same fix at L324).
- `[x]` DOC-A-1.15 [CANCELLATION.md:324] Cites matrix rows `lazy_frame_iter`, `cancellation` — actual IDs are `lazy_streaming_batch`, `cancellation_contract`. ✅ CLOSED Round 4 — both row IDs corrected; missing-mechanism gate added per `feedback_review_round_dispositions.md` Rule 2: `docs/architecture/CANCELLATION.md` joined the Python doc-example harness `DOC_FILES` (it was already in the Go and C++ harness scopes), so future drifts in imports / class names fail the build. Limitation acknowledged in commit message: pytest-markdown-docs only executes top-level statements, so a defined-but-not-invoked async-function-body API drift is not body-checked (the Go and C++ harnesses wrap fragments in synthesized `main()` and do execute bodies; the Python harness does not — this delta is structural, not addressed in this cluster).
- `[ ]` DOC-A-1.16 [CLAUDE.md:180] Anchor `[PROTOCOL.md § Common Error Codes](docs/architecture/PROTOCOL.md#common-error-codes)` — section is "Error Code Reference" (`#error-code-reference`).
- `[ ]` DOC-A-1.17 [examples/README.md:8-29] Lists 7 demos; directory has 11 (`demo_ltl_bug.py`/`engine_ecu_sim.py`/`test_engine_naive.py` undocumented). PITCH says 11.
- `[ ]` DOC-A-1.18 [CLAUDE.md:65] 244 correct vs PROJECT_STATUS.md L446 wrong — internal inconsistency.

#### Cat 2: Staleness (9 findings)

- PITCH.md / DISTRIBUTION.md / DEPENDENCIES.md / DEFERRALS.md all 18-30 days behind Track A-E completions.

#### Cat 3, 4, 5, 6, 7, 8, 9 (cumulative ~37 findings — see full Agent A report for detail)

### Docs Agent B (Deep) — ~80 findings, including key R18-cascade findings

#### Cat 10-21 + 22 (extended R18 with Failure-mode coverage)

- `[ ]` DOC-B-10.1 [docs/INDEX.md] No reference to CANCELLATION.md.
- `[ ]` DOC-B-10.2 [docs/INDEX.md] No reference to PARITY_PLAN.md.
- `[ ]` DOC-B-10.5 [docs/INDEX.md] Documentation Map omits `python/README.md`, `examples/README.md`, `CHANGELOG.md`.
- `[ ]` DOC-B-14.1 **Module count drift across 4 files (244 vs 243 vs 242 vs 119) — durability problem.**
- `[ ]` DOC-B-14.2 GHC/cabal/Agda/stdlib/Python pins repeated across 6 docs.
- `[ ]` DOC-B-14.7 PROJECT_STATUS L456 "Total: 1263 tests" — 103 doc-example fences not labeled in/out.
- `[x]` DOC-B-15.1-15.6 **`iter_can_log` 4-tuple unpack across QUICKSTART.md / TUTORIAL.md:258 / PITCH.md:190 / PYTHON_API.md:33,44,771,879 / COOKBOOK.md:181 / PYTHON_API.md:869 — ALL would raise `ValueError` at runtime if executed.** ✅ CLOSED Round 5 — surface fix at all 7 sites in `docs/{guides/QUICKSTART,guides/TUTORIAL,PITCH,reference/PYTHON_API}.md` (TUTORIAL.md is not in `DOC_FILES` but fixed for doc-correctness).  Missing-mechanism gate (per `feedback_review_round_dispositions.md` Rule 2): `conftest._harness_iter_can_log` flipped from `iter(())` to `iter([CANFrameTuple(0, 0x100, 8, bytes(8), False)])` so unpack arity is exercised at fence-execution time — gate-shape verified by running the harness with the `iter` change applied + the docs unfixed: 5 of 5 broken sites failed with the precise diagnostic `ValueError: too many values to unpack (expected 4)` (PYTHON_API L33's drift was inside a Python `#` comment and not exercised; PYTHON_API L879 surfaced as expected).  Re-applying the fixes returned the harness to 106 passed.  send_frame's stream-not-started → ErrorResponse path means the 3 `iter_can_log` fences without explicit `start_stream` (COOKBOOK.md:189 / COOKBOOK.md:419 / PYTHON_API.md:879) pass even after the harness change without needing wraps.
- `[ ]` DOC-B-19.1 **No `/CHANGELOG.md`** (cf. UR-1.1).
- `[ ]` DOC-B-19.2 **No `docs/architecture/PROTOCOL.md § Limits`** (cf. UR-2.1).
- `[ ]` DOC-B-19.3 No `tools/check-reproducible-build.sh`.
- `[ ]` DOC-B-19.4-19.6 No `tools/check-action-pins.sh`/`tools/check-workflow-permissions.sh`/`.github/workflows/`.
- `[ ]` DOC-B-19.7 No `cpp/README.md`.
- `[ ]` DOC-B-19.8 No `go/README.md`.
- `[ ]` DOC-B-19.9 **No operations runbook** anywhere (`docs/operations.md`, `RUNBOOK.md`, etc. all absent).
- `[ ]` DOC-B-19.10-19.11 PROTOCOL.md missing `aletheia_extract_signals_bin`/`build_frame_bin`/`update_frame_bin` documentation; C header `include/aletheia.h` missing those entries — C consumers cannot achieve parity.
- `[ ]` DOC-B-19.12 No "ALETHEIA_FFI_PATH override" entry in BUILDING.md troubleshooting (CLAUDE.md L160 mentions it).
- `[ ]` DOC-B-19.13 No documented behavior for `BatchError` → `end_stream()` recovery.
- `[ ]` DOC-B-19.14 PARITY_PLAN.md 462 lines, single-line entries; reference-vs-working-doc audience contract unclear.
- `[ ]` DOC-B-19.15 No `--version` flag documented for `python3 -m aletheia`.
- `[ ]` DOC-B-19.16 "Last Updated" stamps without policy.
- `[ ]` DOC-B-19.17 cantools listed in DEPENDENCIES.md but removed.
- `[ ]` DOC-B-22.1 **No operational runbook file** anywhere; AGENTS.md cat 22 mandates symptom/cause/action entries.
- `[ ]` DOC-B-22.2 AGENTS.md cat 22 says "12 shared events"; actual is 15 (cf. DOC-B-22.2 below).
- `[ ]` DOC-B-22.3-22.10 — 15 events × symptom/cause/action + ~12 failure modes from BUILDING.md / CANCELLATION.md / `InputBoundExceeded` / OOM / DBC validation rejection — **~27 missing runbook entries**.

### Docs cross-document pass — 37 root findings (~57 findings unrolled)

#### Cat 5: Redundancy / single source of truth

- `[ ]` DOC-X-5.1 Module count cluster — 4 sources, PROJECT_STATUS canonical, **3 cross-doc findings**.
- `[ ]` DOC-X-5.2 1.08× memory — 3 sources, **2 findings**.
- `[ ]` DOC-X-5.3 4.3×/9.1× FFI speedup — 3 sources, **2 findings**.
- `[ ]` DOC-X-5.4 Haskell shim ~470 LOC — 2 sources, **1 finding**.
- `[ ]` DOC-X-5.5 BSD 2-Clause license — 5+ sources, **4 findings**.
- `[ ]` DOC-X-5.6 Python test count 735 vs 759 — **2 findings + cat 16 reconciliation**.
- `[ ]` DOC-X-5.7 1 Mbps / ~8000 fps — 5 sources, **3 findings**.
- `[ ]` DOC-X-5.8 "5-minute" QUICKSTART tagline — 6 sources, **6 findings**.
- `[ ]` DOC-X-5.9 Toolchain pins — 5 sources, **3 findings**.
- `[ ]` DOC-X-5.10 Version 1.1.1 — **1 cross-doc consolidating finding**.
- `[ ]` DOC-X-5.11 C++ compiler pin (g++≥14/clang≥21) — 4 sources, **3 findings**.
- `[x]` DOC-X-5.12 "15 event types" cross-binding spec — 3 sources, **3 findings + cat 17 contradiction**. ✅ CLOSED Round 3 — `docs/LOG_EVENTS.yaml` is now the canonical 15-event source, and the cat 17 contradiction (Go emitting a 16th) is gone.
- `[ ]` DOC-X-5.13 3-layer architecture diagram (PITCH/DESIGN parallel diagrams) — **1 finding**.
- `[ ]` DOC-X-5.14 `cd python && pip install -e .` — 4 sources, **2 findings**.
- `[ ]` DOC-X-5.15 `bash benchmarks/run_all.sh ...` — 3 sources, **2 findings**.
- `[ ]` DOC-X-5.16 MAlonzo mangling explanation — 3 sources, **1 finding**.
- `[ ]` DOC-X-5.17 README + PITCH parallel streaming-loop snippet — **1 finding**.

#### Cat 15-18

- `[ ]` DOC-X-15.1 **INTERFACES.md L38: `aletheia::check::signal(...)` (lowercase namespace) — would not compile.** D.1 fix flipped L55 worked example but not parity-table cells.
- `[ ]` DOC-X-15.2-15.3 — Same root: INTERFACES.md L40/L41 parity-table `aletheia::yaml::`/`aletheia::excel::` lowercase forms.
- `[ ]` DOC-X-16.1 **Python test count 735 vs 759 — undocumented 24-test gap. Either the FFI-vs-doc-fence boundary moved or one is stale.**
- `[ ]` DOC-X-16.2-16.5 — Module count qualifier asymmetry; throughput numbers qualifier inconsistency; PROJECT_STATUS L453 missing date stamp; PITCH "Phase 5.1 complete" qualifier ambiguity (says complete then lists remaining work).
- `[ ]` DOC-X-17.1 **PROJECT_STATUS.md self-contradicts on module count: L446 says 243, L485 says 242. (cf. DOC-A-1.1, DOC-A-1.2.)**
- `[ ]` DOC-X-17.2 **AGENTS.md cat 22 says "12 shared events"; cats 30 (Go/C++/Python) say "15 event names". Internal contradiction in the protocol doc itself.**
- `[ ]` DOC-X-17.3-17.5 — INTERFACES.md parity-table cells L38/L40/L41 contradict worked examples L55/L79/L91 (D.1 closure incomplete).
- `[ ]` DOC-X-17.6 **PITCH.md L289 "Phase 5.1 complete" + L303 "binary FFI for signal extraction remaining" — contradiction.**
- `[ ]` DOC-X-17.7 BUILDING.md L7-8 vs L29 GHC range disagreement.
- `[ ]` DOC-X-17.8 CLAUDE.md L92 (`--frames 1000`) vs AGENTS.md L25 (`--frames 10000`).
- `[ ]` DOC-X-17.9 DESIGN.md L53/L63 hardcodes 119-module count.
- `[ ]` DOC-X-18.1 PROJECT_STATUS L456 "Total: 1263 tests" without scope label (Python doc-example fences excluded? `go/excel` excluded?).
- `[ ]` DOC-X-18.2 PITCH L289 "all four binding stacks (Python, C++, Go, plus LSP/CLI tooling)" — aggregate "four" misleading.
- `[ ]` DOC-X-18.3 PROJECT_STATUS L450 LOC totals lack scope qualifier.

---

## High-leverage cluster summary

For triage, the top 15 clusters that close the most findings each:

1. **Universal Rule UR-1: Create `CHANGELOG.md`** at repo root + populate from public-symbol survey across all 3 bindings — closes UR-1.1, PY-S-31.4, DOC-B-19.1, DOC-X-5.* indirectly.
2. **UR-2: Create `Aletheia.Limits` module + PROTOCOL.md `§ Limits` + per-binding `InputBoundExceededError`** — closes UR-2.1-2.7, AGDA-D-32.1-9, GO-B-28.3-7, CPP-B-28.1-13, PY-B-26.1-12.
3. **UR-3: Create `tools/check-reproducible-build.sh` + Shake `dist` SHA256 recording + SBOM + signing** — closes UR-3.1-3, CICD-5.2-7.
4. **CICD: bootstrap `.github/workflows/` + `.github/dependabot.yml` + 3 audit scripts + `actionlint`** — ✅ CLOSED cluster 1 across 7 phased commits (per advisor 2026-05-08 phasing — local-first architecture, hard constraint = limited GHA monthly allotment): `96fdcfd` phase 1 / `e7bf797` phase 2 / `30dd178` phase 3 / `2156d7c` phase 4 / `27e3ae3` phase 5 / `8f656f5` phase 6 / `66dd6f9` phase 7 (first end-to-end run + orchestrator defects fix per `feedback_orchestrator_end_to_end_validation.md`).  Closes CICD-1.1 (`.github/workflows/gha-checks.yml` — 3 jobs: actionlint / action-pins / permissions-check, all push+PR triggered, ~1-2 min wall-clock), CICD-1.2 (`.github/dependabot.yml` — weekly cadence, pip+gomod+github-actions ecosystems), CICD-1.3 (`tools/check-action-pins.sh` — GitHub-owned tag-allowlist + third-party SHA-pin policy, branch refs rejected), CICD-1.4 (`tools/check-workflow-permissions.sh` — python3 + yaml parsing, rejects read-all/write-all defaults), CICD-1.5 (actionlint install documented in CLAUDE.md § Development Environment + run-ci.sh step 19 with skip-if-not-installed).  Four deferred enforcement / orchestration sub-items also land here:
   - **Sub-item (a)** ✅ CLOSED cluster 1 phase 1 — `tools/check-changelog.sh` script that diffs the public surface of `python/aletheia/`, `go/aletheia/*.go`, `cpp/include/aletheia/`, and `haskell-shim/ffi-exports.snapshot` against merge-base with `main` and fails when public-API drift exists without a matching `CHANGELOG.md` modification.  v0 is branch-level granularity (one CHANGELOG commit covers any number of public-API commits on the same branch); v1+ tightens to per-commit + verify entry appears under `## [...] — Unreleased`.  Wired into Shake as `phony "check-changelog"` so the same gate runs from the build system, the pre-push hook (Phase 3), and from local CI.  Gate-shape verified via forward-revert in a detached worktree (synthetic `python/aletheia/__init__.py` change against `main` produces exit 1 + precise diagnostic; restore CHANGELOG presence → exit 0).
   - **Sub-item (b)** ✅ CLOSED cluster 1 phase 2 (v0) — gate-claim-integrity offline enforcer at `tools/check-gate-claim.sh`.  v0 implements the .so mtime invariant directly (file-level: `stat -c %Y` comparison between `build/libaletheia-ffi.so` and each build-relevant staged source file).  When a commit message contains an "all gates clean" / "gates green" / "All N gates" assertion, the enforcer fails if any build-relevant file (Agda src, Shakefile.hs, haskell-shim/*, aletheia.agda-lib) has mtime > .so mtime.  Wired into Shake as `phony "check-gate-claim"` (HEAD-mode default); `pre-commit` mode reads `.git/COMMIT_EDITMSG`; explicit commit-hash mode for audit.  Gate-shape verified inline (touch src/Aletheia/Main.agda + claim text → claim regex matched, build-relevant filter matched, mtime diff triggered).  v1+ artifact-based design (attached `tools/ci-output/<sha>.log` from Phase 3's `shake ci` orchestrator) deferred to Phase 3 dependency.  Directly addresses the failure mode where `ae9fe67` claimed gates clean but the `.so` mtime predated the source edits — which would now hard-fail the enforcer.
   - **Sub-item (c)** ✅ CLOSED cluster 1 phase 3 (orchestrator + hook installer; act pairing deferred to phase 4) — `tools/run-ci.sh` orchestrator chaining the full gate sweep (`build` → `check-properties` → `check-invariants` → `check-no-properties-in-runtime` → `check-erasure` → `check-fidelity` → `check-ffi-exports` → `count-modules` → `check-changelog` → `check-gate-claim` → pytest → `go test -race` → ctest → basedpyright → pylint → gofmt + go vet → clang-format), 17 steps total at phase-3 ship, ~12-15 min warm.  Phase 7 raises step count to 21 (clang-tidy added; GHA meta-checks renumbered).  Captures timestamped log under `tools/ci-output/ci-<branch>-<timestamp>.log` (gitignored) for use as falsifiable gate-claim-integrity evidence per sub-item (b)'s artifact contract.  `tools/install-hooks.sh` idempotent installer for the `pre-push` hook that invokes `tools/run-ci.sh` before allowing push.  Direct-invocation pattern (NOT through Shake `phony`) to avoid `cabal run` flock recursion: parent `cabal run shake -- ci` would hold dist-newstyle flock, inner `cabal run shake -- build` would fail to acquire it.  Documented limitation in Shakefile.hs comment block.  [`act`](https://github.com/nektos/act) Docker pairing for offline `.github/workflows/*.yml` execution deferred to cluster 1 phase 4.
   - **Sub-item (d)** ✅ CLOSED cluster 1 phase 7 (`66dd6f9`) — first-end-to-end orchestrator-defects fix.  Phase 6 ship claimed "cluster 1 fully closed" based on per-step verification but never ran `tools/run-ci.sh` end-to-end.  First end-to-end found: (i) steps 13/16/17 silently no-op'ing because `run_step_in`'s `$*` expansion drops quoting on inner `bash -c "..."` arguments; (ii) step 15 using exit-code gating (vs. AGENTS.md L611's SCORE-based pylint policy — pylint exit code is a bit-flag and exit 8 fires on R0801 even at score 10.00/10); (iii) step 16 using `gofmt -d` (diff, exits 0 on dirty source) instead of `gofmt -l` (list, gate by output non-empty) per AGENTS.md L190; (iv) step 18 (clang-tidy) missing entirely despite AGENTS.md L494 + `feedback_clang_tidy_mandatory.md` marking it mandatory.  Phase 7 fixes all four; total steps 20 → 21; first genuine end-to-end pass logged at `tools/ci-output/ci-review-r18_-2026-05-08T*.log` (18m38s wall, ALL 21 STEPS PASSED).  Forward-revert gate-shape verified for steps 15, 16, 17, 18.  New feedback memory `feedback_orchestrator_end_to_end_validation.md` generalizes `feedback_gate_claim_integrity.md` from individual gates to chains of gates.

**Cluster 1 deferred findings (out of cluster 1 phase 7 scope):**
   - **`tests/yaml_tests.cpp:262` `CHECK_THAT` not directly included** (misc-include-cleaner) — discovered 2026-05-08 during cluster 1 phase 7 first end-to-end.  Phase 7 step 18 invokes `clang-tidy -p build src/*.cpp` per AGENTS.md L580 canonical; tests/*.cpp are out of canonical scope.  When orchestrator scope tightens to include tests/, this finding (and any siblings — at least `CHECK_THAT` from Catch2 missing matchers/string header) needs the trivial `#include <catch2/matchers/catch_matchers_string.hpp>` fix.  Tracked here so the next person tightening clang-tidy scope doesn't re-discover and silently work around.
5. **Cat 33/34 across all 3 bindings (NEW R18): no fuzz, no property-based, no sanitizer lane, no cross-binding integration test** — closes GO-B-33.1-8, CPP-B-33.1-6, PY-B-34.1-6 (~24 findings).
6. **`iter_can_log` 4-tuple unpack across 7+ doc sites** — ✅ CLOSED Round 5.  Surface fix: 7 sites updated to 5-tuple unpack (`for ts, can_id, dlc, data, _extended in iter_can_log(...)`).  Missing-mechanism gate: `conftest._harness_iter_can_log` returns one synthetic `CANFrameTuple(0, 0x100, 8, bytes(8), False)` so unpack arity is exercised at fence-execution time; an empty iterator silently passes any unpack (which is what hid the drift across the doc-example harness for the prior rounds).  Closes DOC-B-15.1-6.
7. **`dbc.text_parsed` 16th log event in Go** — ✅ CLOSED Round 3.  Surface fix: `go/aletheia/client.go:287` renamed `dbc.text_parsed` → `dbc.parsed`.  Missing-mechanism gate: `docs/LOG_EVENTS.yaml` SSOT + `python/tests/test_log_events_parity.py` + `go/aletheia/log_events_test.go` + `cpp/tests/test_log_events_parity.cpp`.  Per-binding tests assert every emitted event from a comprehensive workflow is in the YAML name set; gate-shape verified by temporary revert producing precise drift diagnostic.  Closes GO-A-30.1, GO-A-4.1, GO-S-22.1, PY-S-22.1, CPP-S-22.2, DOC-X-5.12.
8. **Module count drift (243/242/119 vs 244)** across PROJECT_STATUS / DESIGN / CLAUDE — closes DOC-A-1.1-4, DOC-X-5.1, DOC-X-17.1, DOC-X-17.9.
9. **Parser-side `unresolvedValueDescs` drop in C++** — ✅ CLOSED Round 6.  Surface fix: `parse_raw_value_desc` helper added to `cpp/src/json_parse.cpp` (mirrors `raw_value_desc_to_json` from `cpp/src/json_serialize.cpp`) plus optional-array reading + aggregate-init field in `parse_dbc_definition`.  Missing-mechanism gate: 3 regression tests in `cpp/tests/unit_tests_json.cpp` (`[trackE]` tag): standalone parse with std + ext CAN IDs, full serialize→parse roundtrip pinning the field through the wire-form, and missing-key tolerance.  Gate-shape verified by `git stash` of just the parser file → 2/3 tests fail with `unresolved_value_descriptions.size() 0 == 1` → restore parser → 3/3 pass.  Closes CPP-B-11.3, CPP-S-22.1, fixes E.8 wire-roundtrip parity (Python ✓, Go ✓, C++ ✓).
10. **`AletheiaClient(dbc=...)` API mismatch in CANCELLATION.md L150** + `AsyncAletheiaClient` reference + matrix-row IDs — ✅ CLOSED Round 4.  Surface fix: L150 example rewritten to `AletheiaClient(default_checks=load_checks("checks.yaml"))` + `await client.parse_dbc_text(...)` flow; L302/L324 `AsyncAletheiaClient` references replaced with `aletheia.asyncio.AletheiaClient`; L324 matrix rows corrected to `lazy_streaming_batch` / `cancellation_contract`.  Same kwargs fix applied to `python/aletheia/asyncio/__init__.py:15` rst docstring example.  Hallucination, not planned-then-dropped (verified `git log -S "dbc=" -- python/aletheia/client/_client.py` returned no commits).  Missing-mechanism gate: `docs/architecture/CANCELLATION.md` joined the Python doc-example harness `DOC_FILES` list (it was already in the Go and C++ harness scopes), and the AGENTS.md § Python Cat 32 verification block was updated to match.  Limitation acknowledged: pytest-markdown-docs only executes top-level statements, so a defined-but-not-invoked async-function-body API drift is not body-checked — the Go harness wraps body fragments in synthesized `main()` and does check; this delta is structural and not addressed in this cluster.  Closes DOC-A-1.13-15, PY-S-15.1.
11. **Long-run resource leakage R18 sub-checks across all 3 bindings** — AGDA-A-16.1-3, GO-B-27.6-9, CPP-B-26.* (long-run), PY-B-25.3a-d.
12. **Test isolation R18 sub-check (f) tooling**: `pytest-random-order` plugin missing in Python — PY-B-14f.1, PY-B-34.5.
13. **Mutation testing R18 sub-check (g) tooling**: `mutmut`/`gomut`/`Mull` infrastructure missing across all 3 bindings — PY-B-14g.1, GO-B-14.7, CPP-B-14.8.
14. **Operations runbook (R18-extended cat 22): missing entirely** — DOC-B-22.1-10 (~27 missing entries).
15. **Two distinct `WellFormedDBC` records under same name in different Agda modules** — AGDA-D-11.1, AGDA-D-15.4. **✅ CLOSED Round 7** along with AGDA-D-11.2 (asymmetry documented), AGDA-D-19.6 (caller obligation documented per G-A7(c)), AGDA-D-GA20.4 (type-def split). 5 findings closed in single commit; new module `Aletheia.DBC.TextParser.WellFormed` carries the renamed `WellFormedTextDBCAgg` predicate.
16. **Agda chained-rewrite cleanup** — AGDA-B-8.1-8.4. **✅ CLOSED Round 8**. Step.agda 2 sites (handleDataFrame-ack-complete + handleDataFrame-violation-complete: `iterate-correct` + `spec-eq` rewrites collapsed into single `cong (λ p → proj₂ (dispatchIterResult …)) iter-eq`, retaining `rewrite mono` as guard-dispatcher); Bounded.agda 2 sites (6 binary clauses each in `indexHelper-counter` + `collectAtomsAcc-spec` collapsed via 2 helper lemmas in the existing `private` block — `binary-counter-step` and `binary-acc-spec-step`, zero rewrites in helper bodies). 4 findings closed; AGDA-B-8.5 (Cache.agda small-goal 2-rewrite) **SKIPPED Round 8 + user-judgment accepted Round 9**: both rewrites do essential variable rewriting (`name'→n` via `≡csᵇ-sound`, then `n≡csᵇn→true` to enable `lookupEntries` reduction), refactor would cost ~5 lines for no win on a non-violation small goal; advisor-recommended skip stands. The two related user-judgment items AGDA-A-2.1/2.2 (magic 2048) and AGDA-A-4.1 (digitChar-not-isHSpace TODO) closed Round 9 — see per-finding lines above.
17. **CANId proof-field irrelevance migration** — AGDA-B-22.1. Architectural candidate: mark `T (n <ᵇ max)` as `.(…)` to simplify `_≟-CANId_` and drop the per-CANId runtime cell. Multi-site construction-call audit + benchmark verification (cat 16 hot-path rule).

---

## Low-cost wins (each 1-3 mechanical edits)

- AGDA-A-1.* (31 dead-code findings): mechanical `using` cleanup.
- AGDA-A-GA1.* (23 mergeable-import findings): mechanical merge.
- DOC-A-1.10-12: cantools removal cleanup in DEPENDENCIES.md.
- DOC-A-1.5, 1.7, 1.8: PITCH.md status section refresh (LSP/CLI claim, signal-extraction-binary claim, mux-query claim).
- CPP-A-2.1: clang-format violation in `tests/integration_tests.cpp:479-481`.
- DOC-X-17.2: AGENTS.md cat 22 "12" → "15" event-name typo.
- DOC-A-1.16 + CLAUDE.md L180 anchor fix.

---

## Action plan placeholder

After all dispositions are marked above, this section will hold the round's plan with `FIX`/`FP`/`DEFER-<reason>` per finding, organized by:

- Items to fix this round
- Items deferred (with rationale + memory-file pointer)
- Items declared FP (with justification)

**Pending discussion items before plan finalization:**

1. ✓ Resolved 2026-05-07: Agda Agent B re-run completed; 8 substantive findings folded into AGDA-B-* section above.
2. ✓ Resolved 2026-05-07: split.  CHANGELOG bootstrap is its own cluster 8 (FIX-early, closed Round 2); `--bignum=native` tracking stays under UR-3 (DEFER-end-of-round, cluster 3).
3. Decide whether cat 33/34 (new R18 categories) findings are deferred (mass infrastructure) or partially actioned this round (start with sanitizer lane + `python -X dev` lane as proof-of-concept; the latter already surfaces 3 cancellation-test flakes — PY-B-14a.1).
4. Confirm fix-vs-defer for `iter_can_log` 4-tuple unpacks — Track D doc-example harness should have caught these; investigate why it didn't (DOC-B-15.* root cause).
5. ✓ Resolved 2026-05-08: Cluster 14 closed Round 7. Option (i) pure rename + extraction (advisor-recommended) — text-side `WellFormedDBC` → `WellFormedTextDBCAgg` in new module `Aletheia.DBC.TextParser.WellFormed`; JSON-side `WellFormedDBC` ↔ `WellFormedDBCRT` weak/strong pair preserved; dead 1-field stub `Formatter.WellFormedText.WellFormedTextDBC` removed.  AGDA-D-11.2 closed by documentation (asymmetry deliberate, not under-specification); AGDA-D-19.6 closed by documented caller obligation per G-A7(c); AGDA-D-GA20.4 closed by extraction.
6. **NEW from Agent B re-run**: Confirm CANId proof-field irrelevance migration (AGDA-B-22.1) — architectural improvement requiring construction-site audit + hot-path benchmark per cat 16.
7. **NEW from Agent B re-run**: Confirm scope for chained-rewrite cleanup (AGDA-B-8.1-8.5) — Step.agda Findings 8.1/8.2 are large-goal violations of G-A2; Bounded.agda 8.3/8.4 are repeated patterns suggesting helper-extraction.

---

## Round 1 progress (Clusters 9 + 15 — mechanical noise reduction)

Status: ✓ landed on `review-r18` per commit chain. Build + check-properties both clean. Remaining Agda gates queued.

**Cluster 15 — mechanical fixes applied (~70 findings):**
- AGDA-A-1.1 → AGDA-A-1.31: dead `using` symbols removed from 25 Agda modules. The 3 unused-parameter findings (1.27-1.31) addressed by replacing `idx`/`propJSONs`/`tf`/`bitLength` with `_`.
- AGDA-A-GA1.1 → AGDA-A-GA1.23: mergeable / dead imports consolidated across the 23 cited sites.
- AGDA-A-2.3 + AGDA-A-4.2/4.3/4.4: explanatory comment block added above `power10` in `Protocol/JSON/Parse.agda` covering the literal-9 rationale and the unreachability of all `... | zero` branches.
- AGDA-A-4.5: `Trace/Time.agda` `ns`/`ms`/`s` constructors annotated as "Reserved for future use; not currently produced".
- DEPENDENCIES.md cantools removal (DOC-A-1.10-12) — table entry + 5 transitive entries dropped, with a one-line provenance pointer to Track B.3.g 2026-05-03.
- pyproject.toml `pytest-random-order>=1.1,<2` added to dev extras (PY-B-14f.1, PY-B-34.5) with a doc comment cross-referencing AGENTS.md cat 14(f).
- AGENTS.md cat 22 "12 shared events" → "15 shared events" (DOC-X-17.2 / DOC-B-22.2).
- CLAUDE.md L180 anchor `#common-error-codes` → `#error-code-reference` (DOC-A-1.16).
- `cpp/tests/integration_tests.cpp:479-481` reformatted via `clang-format -i` (CPP-A-2.1) — `clang-format --dry-run -Werror` now clean.

**Cluster 9 — module count drift fixed:**
- PROJECT_STATUS.md L446 evolution chain extended to Track E.10's +1 module → **244**; L485 "242" → "243" (the `--safe --without-K` subset of the 244 total).
- DESIGN.md L53 / L63 hardcoded "119 modules" replaced with cross-references to PROJECT_STATUS.md § Key Metrics for the canonical count.
- PITCH.md L289 "all four binding stacks (Python, C++, Go, plus the LSP/CLI tooling)" → "all three binding stacks (Python, C++, Go)" + Phase 6 stretch-goal callout for C++/Go CLI parity.
- PITCH.md L297 CLI subcommand list extended to all 6 (`check`, `validate`, `extract`, `signals`, `mux-query`, `format-dbc`).
- PITCH.md L303 "Remaining: SOME/IP exploration, binary FFI for signal extraction" — binary FFI shipped, replaced by Phase 6 candidate-goals summary.

**Cluster 15 items deferred (judgment calls — surface for discussion):**
- AGDA-A-2.1 / AGDA-A-2.2 [src/Aletheia/DBC/TextParser/Properties/Comments/Comment.agda:118-119,127] — the literal `2048` is part of a self-contained lemma `2048<extFlagBit` whose name and body both reference the bare number; renaming touches consumers. Discuss whether to (a) replace the literal with `standard-can-id-max` only in the prose comments at L116-117 and L127, or (b) refactor the lemma body+type+name to use the constant + add a deprecation alias.
- AGDA-A-4.1 [src/Aletheia/DBC/TextParser/Format/ValueDescription.agda:129-130] — open-ended TODO without a memory-file pointer. Discuss whether the consolidation is in scope (touching 2 sites that do similar work) or whether to enrich the TODO with a memory pointer instead.

---

## Round 1 follow-up (Cluster 15 over-prune — `signalNameStr` import)

The Round 1 cluster-15 batch (`ae9fe67`) over-pruned one `using` symbol that was actually referenced.  Caught when re-running `cabal run shake -- build` as the cluster 8 pre-commit gate.

**Regression:** `src/Aletheia/CAN/SignalExtraction.agda` line 21 had `open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)` — but `signalNameStr` was previously also in that `using` clause (originally on its own `open import Aletheia.DBC.Types using (signalNameStr)` line; the cluster-15 batch dropped the standalone line as "duplicate" without merging the symbol into the surviving clause).  `signalNameStr` is still called at line 46: `MuxExtractionFailed (signalNameStr muxSig)`.  Agda fails with `signalNameStr` not in scope.

**Fix:** restore `signalNameStr` to the `Aletheia.DBC.Types` using clause (one-line revert).

**Why the Round 1 commit's "all 8 gates clean" claim was incorrect:** the pre-existing `build/libaletheia-ffi.so` artifact had mtime `2026-05-07 12:38`, predating the cluster-15 source edits at `2026-05-07 14:54`.  Gate output was almost certainly captured against an earlier state and the post-edit re-run was skipped.  The `clean && build` recovery from CLAUDE.md was needed to clear a stale MAlonzo cache (`build/MAlonzo/Code/Aletheia/Data/BitVec/Conversion.hs` from May 3 had old name-mangling vs. freshly-regenerated `Encoding.hs`'s newer numbering).  Both issues stem from the same root cause: the cluster-15 commit's gate run did not happen at the actual commit hash.

**Audit scope:** static substring auditor of `ae9fe67`'s 38 Agda-file diff flagged ~90 candidate regressions; the vast majority were FPs (substring matches in comments, partial matches in compound identifiers like `SignalNotInDBC`, or symbols still imported via merged `using` clauses).  Agda's scope checker is the authoritative oracle: a clean `cabal run shake -- build` rules out all import-scope regressions.  After the one-line fix, full clean+build went through (3m18s); rest of the gate sweep (`check-properties`, binding tests, lint gates) confirmed clean.

**Lesson (for the round retro):** mechanical-batch commits that touch many files must run gates at exactly the post-edit commit hash, with output captured.  The "all gates clean" line in the commit message is now treated as a falsifiable claim — re-runnable against the commit hash and verified before trusting it.  Per `feedback_review_round_dispositions.md` Rule 2 ("FP needs explicit double-check — surface fixes can hide missing mechanisms"), the missing mechanism here is: a CI gate that fails commit-message claims of "all gates clean" without an attached gate-output artifact.  Belongs to the same family as the deferred `tools/check-changelog.sh` enforcement — both are CI gates against gate-claim integrity, both deferred to cluster 1 (CICD bootstrap).

---

## Round 2 progress (Cluster 8 — CHANGELOG bootstrap)

Status: ✓ landed on `review-r18`.  Doc-only commit; no proof / lint / benchmark gates required (per `AGENTS.md` § "Step 4: Implement and verify": "Changes to docs-only files may skip step 4 (benchmarks) after confirming no code changed.").

**Cluster 8 — UR-1.1 closed:**
- `/home/nicolas/dev/agda/aletheia/CHANGELOG.md` created at repo root in [Keep a Changelog 1.1.0] format under [Semantic Versioning 2.0.0].  Single seeded section `[2.0.0] — Unreleased` covers the v1.1.1 → HEAD public-surface diff (~5 weeks, ~198 commits) across Python / Go / C++.
- Version anchor decision: **v2.0.0 (SemVer)**.  Honest SemVer given the breaking signature refactor on every Go `Client` operation method (`ctx context.Context` first param, Track C.3) and every C++ `AletheiaClient` operation method (`std::stop_token` first param, Track C.4).  Migration guidance accompanies each `BREAKING` heading.
- Section structure: cross-binding entries clustered first ("behavioral parity, not syntactic identity" per `docs/development/PARITY_PLAN.md:8`), then per-binding additions (Python / Go / C++).  Sub-sections: Added / Changed (incl. BREAKING) / Removed / Fixed.

**Deferred to cluster 1 (CICD bootstrap):** structural CI gate that diffs the public surface and requires a CHANGELOG entry on PRs that change it.  No `.github/` infrastructure exists yet (CICD-1.1), so the gate has nowhere to run.  When cluster 1 lands, add a `tools/check-changelog.sh` (or equivalent workflow step) that fails on public-API drift without a matching CHANGELOG entry.

**Pre-v2.0.0 history backfill:** explicitly out of scope.  The R18 rule's "seed for its initial population" phrasing is satisfied by the v1.1.1 → HEAD diff; bootstrap is bounded.  Tag-history pointer (`v1.1.1`, `v1.0.0`, `v0.3.2`, ...) shipped at the bottom of `CHANGELOG.md` with a `git log <tag>` cross-reference.

[Keep a Changelog 1.1.0]: https://keepachangelog.com/en/1.1.0/
[Semantic Versioning 2.0.0]: https://semver.org/spec/v2.0.0.html

---

*Generated by R18 review pass on branch `review-r18` at 2026-05-07. Total raw findings: ~610 across 17 returned agents (Agda Agent B successfully re-run after initial stub failure).*
