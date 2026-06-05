# AGENTS.md -- Code Review Protocol

This file defines the review protocol for the Aletheia project. Every review round must follow these rules exactly.

## Universal Rules (All Languages)

**A finding is a finding.** Every diagnostic surfaced by a tool run or manual review is an action item. The only correct response to a finding is to investigate it. Do not classify findings before investigating them. Any label that could justify inaction -- temporal ("pre-existing"), authorial ("not from our changes"), systemic ("build system artifact", "tooling issue", "compiler warning"), or scoping ("out of scope", "separate concern") -- is a dismissal mechanism disguised as a category. A finding has no origin, no age, no owner, and no source system. It is a thing that is wrong, and it gets fixed.

**What counts as a finding.** A finding is any of: (a) a diagnostic emitted by a tool (compiler, linter, formatter, type checker, test framework); (b) a violation of a named category or guideline in this document; (c) a discrepancy between claimed behavior (docs, comments, tests) and actual behavior; (d) code that would surprise a reasonable reviewer familiar with this codebase. When in doubt, raise it.

**Every finding must be fixed.** There are no exceptions. Nits, test gaps, polish, documentation, architecture, design -- everything. "Investigate" means: understand what is producing the diagnostic, determine whether the project can eliminate it, and either fix it or surface it to the user with an explanation. Concluding that a finding is not actionable without investigation is never acceptable.

**Reviews cover specification, design, and architecture, not just implementation.** A review is re-reading all the code and checking if every detail makes sense and is built correctly. Question the specification itself: are the features right? Do they make sense? Are assumptions correct? Should something be reworked? Reviews are the only opportunity to reconsider these choices. Nothing is "disproportionate" for a review round. Cascading type-level changes, API redesigns, module restructuring, and specification corrections are all valid review outcomes.

**No category may be skipped.** Every category listed below must be checked in every review round, against every file in scope. Large files are not an excuse to skim -- recommending a split is itself a valid finding.

**Both local and end-to-end issues are in scope.** Review each file individually AND consider cross-module interactions, data flow, and layer boundaries.

**The only valid dismissal is "suspected false positive".** Suspected false positives must be identified with explicit justification, but no finding may be discarded from the plan without the user's permission. Present all findings -- including those believed to be false positives -- and let the user decide. User deferral is the only non-fix outcome and must be recorded in the round plan and in a durable memory file so future rounds know the state.

**Backward compatibility is never a reason to avoid a change.** When writing or reviewing code, never let "this would break backward compatibility" prevent making the right design choice. Compatibility shims, deprecated aliases, old field names kept alongside new ones, and preserved-but-wrong interfaces are all forms of technical debt. Design the cleanest interface for the current need.

**Discouraged is not deprecated.** When a feature is labeled "discouraged for use case X", "not recommended on CAN", or similar usage norm, that is a direction for users — not a removal plan. Relocate + annotate instead of deleting. Deletion requires an explicit removal signal from the user ("remove this", "we don't need this"). R13's `Predicate.next()` / `Property.next()` was the worked example — kept, relocated under a "Discouraged in CAN analysis" banner, not deleted.

**Benchmark before committing runtime-affecting changes.** Any change to runtime code in any language (Agda core, Haskell shim, Python client, C++ client, Go client) requires `bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput` before commit and a recorded comparison against the most recent baseline. Correctness gates (pytest, ctest, go test, basedpyright, pylint, clang-tidy) do NOT catch allocation-overhead regressions. R12's Python `log_event` wrapper regressed Stream LTL by −16.1% while passing every correctness gate — fixed in `1e40b4d`. Agda cat 16, Python cat 25, Go cat 27, and C++ cat 26 each cross-reference this rule; this is its canonical home.

**In-source deferral notes.** When a review finding is deferred with user approval, the rationale — scope, hazard, recovery path — must be written as a comment block at the relevant code site, not only in the round plan or memory. Reviewers hit the code first; a deferred-item memory file alone will not stop a future round from re-raising the same refactor. The canonical worked example is the comment block above `mkPredTable` in `src/Aletheia/Protocol/StreamState/Internals.agda` documenting why the `ℕ` index is not lifted to `Fin n`.

**Cross-binding feature parity is mechanical, not manual.** `docs/FEATURE_MATRIX.yaml` is the authoritative declaration of every user-facing capability and its per-binding status (`implemented` / `not_applicable` / `planned`). Three structural gate tests — `python/tests/test_feature_matrix_parity.py`, `go/aletheia/feature_matrix_test.go`, `cpp/tests/test_feature_matrix_parity.cpp` — parse the YAML, validate the schema, and for every `implemented` row verify the stated entry resolves on its binding (Python via `importlib` + recursive `getattr`, Go via `go/ast` source parsing, C++ via header + whole-word symbol match). They run inside each binding's default test battery, so a silent removal or rename of a public symbol fails the build the same way a broken test does. When adding, removing, or renaming a user-facing capability, updating the YAML is part of the change, not a follow-up. See `docs/development/PARITY_PLAN.md` for the roadmap and the locked design decisions that bound the matrix's scope.

**No unilateral commit-scope splits.** A stated commit goal is immutable unless the user explicitly OKs descoping. Before every `git commit` of substantial work, run a 2-question pre-commit gate:

1. **Hard rule** — does this commit ship the originally-stated goal in full?
2. **Pre-commit gate** — if no, did I get explicit user approval to descope or split into part-A-now / part-B-next-session?

If either answer is no, do NOT commit. Surface the question — *"I'm at X.  Pushing through to ship the full goal looks like ~Y more turns. Do you want me to push through, or stop and we resume next session?"* — and wait for the answer. The cost of one user turn is bounded; the cost of an unwanted split is rework + trust erosion.

**Structural recognition** — the pattern is "midway through substantial work, agent feels time pressure, rationalizes a save-point, commits short of stated goal." Specifically reject: sunk-cost rationale ("would be a waste to throw away"), false dichotomy ("the alternative is leaving the tree broken" — `git stash` + `.session-state.md` exist), clean-boundary rationale ("splitting here is natural"), session-budget self-assessment ("remaining work too large for available turns" — that judgment is the user's, not the agent's). Trigger words that should fire the gate: any time the agent's internal reasoning about a commit-in-flight uses "checkpoint," "infrastructure," "scaffolding," "preparation," "split," "defer," "next session," or "follow-up," that is the cue to STOP and ask. Two recorded failures, both flagged by user, both fixed same session: `c884e69`/`7a44c87` (parseDecRat subsumption asymmetry, 2026-04-25) and `6f418c4` (B.3.d 3d.3 split into 3d.3a/3d.3b, 2026-04-26 — 3d.3b shipped on top of `6f418c4` to close 3d.3 fully in the same session, alongside this AGENTS.md rule + new memory `feedback_pre_commit_scope_check.md`). See `feedback_pre_commit_scope_check.md` for the canonical statement of this rule.

**Adversarial-input bounds at parser surfaces.** Every parser at a trust boundary — DBC text in Agda, JSON at the FFI boundary in all three bindings, the binary frame decoder, attribute-set / value-table inputs, YAML check loaders, Excel loaders — must enforce explicit upper bounds: max nesting depth, max list cardinality (signals/messages/attributes/value-descriptions per file), max identifier length, max single-string length, max total input length. Bounds are documented in `docs/architecture/PROTOCOL.md` § Limits and are constants known at compile time. Rejection over the bound is a typed error (`InputBoundExceeded` with the offending field and the limit it crossed), never a crash, never an OOM, never a stalled stream. A parser that accepts a 200 MB pathological DBC and exhausts heap is a finding regardless of `--safe`/`-race`/test-suite passes — termination is not the same as bounded resource consumption, and a verified-terminating parser fed a hand-crafted input with 10⁷ signals will still produce a 10⁷-element list that exhausts heap downstream. Cross-binding policy: bounds are checked in the Agda kernel first (definitive), and each binding's wire-shape parser additionally rejects oversize inputs at the FFI entry to short-circuit before marshaling. The first review round under this rule must surface every parser entry point that has no bound check and propose either a tightening or a documented exception in PROTOCOL.md § Limits. The Agda manifestation is cat 32 (Parser resource bounds); the binding manifestations are extensions to Go cat 28, C++ cat 28, and Python cat 26.

**Reproducible build verification.** `cabal run shake -- build` must produce a bit-identical `libaletheia-ffi.so` across two clean builds on the same toolchain pin (same GHC, cabal, Agda, stdlib version). The CI pipeline records `sha256sum libaletheia-ffi.so` per build and a regression gate compares the second build of a given commit against the first; drift indicates a build-time non-determinism (timestamp embedding via `__DATE__`/`__TIME__`, build-path leakage into binaries, cabal-store ordering variance, Shake target ordering, GHC `-fllvm` cache pollution) that must be tracked down, not accepted as flake. The same gate applies to the Python wheel (`pip wheel --no-deps`), the C++ library archive, and the Go module cache after `go mod download` — extend per-target as those entrypoints become release artifacts. Worked example: the LGPL-contingency `--bignum=native` rebuild deliverable's "before/after `.so` hash + benchmark snapshot" depends on this rule — without bit-identical builds, the before/after comparison cannot distinguish a real change from build noise. The first review round under this rule must surface every release artifact that lacks a documented hash-stability check and propose adding one.

**Public API stability and CHANGELOG discipline.** Every renamed, removed, or signature-changed public symbol in `python/aletheia/` (anything not prefixed `_`), `go/aletheia/` (any exported name), or `cpp/include/aletheia/` (anything in the published header tree) is accompanied by a `CHANGELOG.md` entry stating the version, the change, and migration guidance. A removed-public-symbol commit without a CHANGELOG entry is a finding. CHANGELOG location: `CHANGELOG.md` at repo root, sectioned per release per Keep-a-Changelog conventions (`Added`/`Changed`/`Deprecated`/`Removed`/`Fixed`). Internal renames within `_`-prefixed Python modules, `internal/` Go subpackages, or `cpp/src/detail/` are exempt — those are not part of the published API surface. Cross-binding parity (`docs/FEATURE_MATRIX.yaml` rows) is also under this rule: when a matrix-row entry resolves to a different symbol after a binding-side rename, the rename triggers a CHANGELOG requirement and the parity test surfaces the missed entry. Distinct from "discouraged is not deprecated" — that rule covers usage norms (a feature stays available but is annotated against use); this rule covers the actual removal/rename surface. The first review round under this rule must surface the absence of `CHANGELOG.md` itself as a finding and the public-symbol survey as the seed for its initial population.

## Review Procedure

Reviews run in two phases: per-file analysis (local concerns within each file) followed by system-level analysis (cross-file comparison and whole-program reasoning). Every category has exactly one owning agent. The agent prompt must list assigned categories and guidelines by number/name.

### Step 0: Carry-over review (before step 1)

Before launching any agents, the driver reads:
1. **Prior-rounds archive at `.archive/reviews/r*/`** — `findings/*.yaml` with `disposition` in `{DEFER, FIX-PARTIAL, NO-FIX}` are automatic carry-over candidates. Round metadata at `.archive/reviews/r<N>/round.yaml`. Use `tools/review_db.py --report graduation` to surface categories that have gone N rounds with zero real findings (graduation candidates per the **Graduation** rule below); use `tools/review_db.py --report critical-high-trend` to verify the "0 critical stays 0 critical" invariant has not regressed.
2. The most recent round's working findings file in `~/.claude/plans/` (round-scope working state; superseded by archive YAML after merge).
3. `MEMORY.md` → any `project_*_deferred*` or `project_system_review_deferred*` entries.
4. In-source deferral comment blocks (see Universal Rules).

Every deferred finding from prior rounds is automatically a carry-over candidate for this round. If the conditions that justified deferral still hold, re-defer explicitly in this round's plan; if they no longer hold, the finding is live again and must be fixed. A deferred finding silently dropped across rounds is a procedure violation.

**Graduation (load-bearing rule for keeping the agent fleet bounded):** A review category that has gone **2 rounds with zero real findings** (FIX / FIX-PARTIAL / NO-FIX closures imply a real issue was caught; FP and FP-VERIFIED do not count) is a **graduation candidate**. A category graduates from the agent fleet only when:
1. A **mechanical gate** exists that catches the category's semantic surface (the gate is the new enforcement; agent reasoning is no longer required).
2. The graduation is recorded in `memory/feedback_graduated_categories.md` with the gate's name.

Once graduated, the category is no longer reviewed at Step 1 / Step 2 — the gate runs continuously, and a re-raise in a review is a regression of the graduation. Step 3's coverage check skips graduated categories per the list in `memory/feedback_graduated_categories.md`. The per-language agent tables below may still list a graduated category in their range (e.g. "1-6"); the graduated-set table in memory takes precedence. `tools/review_db.py --report graduation` surfaces candidates; merging a category into the graduated set is a deliberate documented step, not an automatic consequence of the report.

Cat 1 (Dead code) is the worked example: graduated R22 when a strict pre-push dead-import gate was wired (commit `403555b`); R22's residual A-1.1 work was historical cleanup wearing review clothes. Post-R23 the gate is the scope-aware `.agdai` IWYU reader (`tools/iwyu_reader.py` + `tools/iwyu_narrow.py`, run_ci steps 9-10); the recompile/regex tools it replaced are retired. Either way, the new-code regression class is caught at push time, not at review time.

### Step 1: Per-file review (agents A, B, C in parallel)

Each agent reads files individually and checks local concerns. These categories can be fully evaluated by examining one file at a time.

**Delta-based scope for Step-1 agents A and B (token-efficiency rule).** Per-file agents A (hygiene) and B (correctness) review **only the files touched since the previous round's merge commit** (`git diff <prev_merge>...HEAD --name-only -- '*.<ext>'`). Per-round file scope drops from O(263 modules) to O(30–80 touched files). Whole-program coverage on these agents is recovered by the next periodic full sweep, scheduled out of band; for a typical follow-up round, delta scope is enough.

**Whole-program scope (must NOT delta) — Agent C and Step-2 system-level Agent D.** Edits in touched files can introduce drift against untouched ones (a renamed function in `M` regresses naming consistency in `N` that imports it; an error message added to `M` may collide with one in `N`). Cross-file comparison categories (Agda cat 3, 5, 6, 27) and every Step-2 category stay whole-program. If the round driver elects to skip whole-program agents to save tokens, that decision is recorded in the round.yaml `notes` field as an explicit scope decision, not a silent omission.

**Agda per-file agents:**

| Agent | Categories | Guidelines |
|-------|-----------|------------|
| A: Hygiene | 1 Dead code, 2 Magic numbers, 4 Comments, 16 Performance, 21 Safety flag audit, 28 Pragma abuse audit, 29 Instance & reflection discipline | G-A1 Import hygiene (→1), G-A8 Flag hygiene (→21) |
| B: Semantics | 7 Type tightness, 8 Proof simplification, 9 Proof soundness, 18 Dead-branch provability, 20 Termination metric hygiene, 22 Irrelevance, 23 Erasure `@0`, 24 Pattern coverage & clause order, 25 Universe level hygiene, 26 Equality discipline | G-A2 Proof style (→8,9,20), G-A9 Where-block provability (→9), G-A5 Termination metric choice (→20), G-A6 Dead branches (→18), G-A3 `in eq` idiom (→8), G-A4 Irrelevance (→22), G-A10 Bounded types (→7,22), G-A12 Decidable check combinators (→8,26) |
| C: Cross-file comparison | 3 Naming, 5 Error messages, 6 Redundant patterns, 27 Stdlib coverage & lemma deduplication | G-A14 Error types (→5), G-A15 Combinator-first (→6), G-A16 Stdlib-first (→27) |

Agent C reads multiple files to compare the same attribute across modules (naming patterns, error string format, duplicated logic). It does not need A or B's results and runs in parallel with them.

**Go per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene & Style | 1-6, 30 | Style, naming, dead code, docs, errors, formatting, slog discipline |
| B: Correctness & Runtime | 7-14, 23-29, 33 | Types, safety, serialization, parsing, FFI, tests, error wrapping, nil discipline, context, channel lifecycle, hot-path perf, cgo security, file I/O, dynamic-correctness analysis (sanitizers/fuzz/property/cross-binding) |

**C++ per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene & Style | 1-6, 30 | Style, naming, dead code, docs, errors, formatting, logging discipline |
| B: Correctness & Runtime | 7-14, 23-29, 33 | Types, safety, serialization, parsing, FFI, tests, exception safety, UB hazards, data races, hot-path perf, stdlib idioms, security, file I/O, dynamic-correctness analysis (sanitizers/fuzz/property/cross-binding) |

**Python per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene & Style | 1-6, 27, 28, 32, 33 | Style, naming, dead code, docs, errors, module organization, file I/O & encoding, logging discipline, doctest validity, CLI quality |
| B: Correctness & Runtime | 7-14, 23-26, 29-30, 34 | Types, safety, serialization, parsing, FFI, tests, concurrency, mutability, hot-path perf, security, exception chaining, determinism, dynamic-correctness analysis (sanitizers/fuzz/property/cross-binding) |

**CI/CD agent (single agent — section is small enough that splitting hurts coherence):**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: CI/CD | 1-5 | Workflow YAML hygiene, cache discipline, permission scoping, build/test isolation, artifact and release surface |

The CI/CD agent runs in parallel with the per-file language agents at step 1. Reviews `.github/workflows/`, `.github/actions/`, `tools/release/`, `dependabot.yml`, and the Shake `dist`/`install`/`release` rules. Hard gate: `actionlint` clean. Findings under cat 1 also surface to the per-language agents when a workflow change implies a source-side change (e.g., a workflow that runs `pytest tests/` against a removed test file is both a CI/CD finding and a Python finding).

**Documentation per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene | 1-9 | Accuracy, staleness, consistency, completeness, redundancy, commands, links, audience, precision |
| B: Deep | 10-22 | Structure, examples, rationale, onboarding, durability, testability, qualifiers, internal consistency, scope labels, missing content, numerical correctness, cross-language parity, operational runbook |

### Step 2: System-level review (agent D, after step 1 completes)

Agent D takes a whole-program view. These categories cannot be evaluated per-file — they require understanding the dependency graph, type flow across module boundaries, or the system's overall design. Agent D launches after step 1 so it can reference per-file findings for context.

**Agda system-level agent:**

| Scope | Categories | Guidelines |
|-------|-----------|------------|
| Specification | 10 Domain model, 11 Invariants, 12 Property completeness, 13 Assumption audit, 19 Hypothesis propagation, 32 Parser resource bounds | G-A11 Validity predicates (→10, 11), G-A13 Generalization (→10), G-A17 Typed error handling (→11), G-A18 State machine encoding (→11), G-A7 Proof hypothesis discharge (→19) |
| Architecture | 14 API surface, 15 Module structure, 17 Cross-layer, 30 MAlonzo export surface stability, 31 Stdlib version pinning & API compatibility | G-A19 Binary FFI wire format (→17, 30), G-A20 Module separation (→15), G-A23 Audit all wire boundaries (→14, 17) |

Agent D must concretely:
- **10 Domain model**: Read all domain type modules (CAN/, DBC/, LTL/, Trace/) and assess whether the type system faithfully models the real-world domain. Identify protocol features, edge cases, or real-world behaviors the model cannot represent.
- **11 Invariants**: Trace type-level constraints across module boundaries. If module X assumes a property, does module Y guarantee it? Are there runtime checks that could be compile-time? Are types over- or under-constrained?
- **12 Properties**: List all proven properties and assess whether they are the ones that matter for safety. Identify important unproven properties and gaps between what proofs guarantee and what users believe.
- **13 Assumptions**: Identify implicit preconditions, unchecked coercions, and model simplifications that could silently produce wrong results. Check agreement with CAN 2.0B, ISO 11898, CAN-FD, DBC format. Verify MAlonzo compilation faithfulness.
- **14 API surface**: Build the import graph and check for over-exported names (internal helpers visible to consumers), under-exported names (useful functions hidden), and unnecessary re-export chains.
- **15 Module structure**: Analyze the dependency graph for direction violations, circular dependencies, modules mixing concerns, and modules that are too large. Check that Types/Operations/Properties are separated.
- **17 Cross-layer**: Verify the Agda → Haskell → binding boundary: FFI type alignment, marshalling assumptions, and behavioral parity across Python/C++/Go bindings.
- **19 Hypothesis propagation**: For every theorem that takes a precondition (e.g. `Monotonic σ`, `TwoValued table`, `AllBelow b φ`), trace the hypothesis from its introduction down to the production pipeline. Verify that each hypothesis is either (a) enforced at the relevant entry point by a runtime check, (b) embedded as a type-level constraint that cannot be violated, or (c) explicitly documented as an uncheckable caller obligation at the boundary. A theorem whose hypothesis is never discharged by the running code is a vacuous guarantee and a finding.

**Go system-level agent:**

| Scope | Categories | Notes |
|-------|-----------|-------|
| Architecture | 15-18, 31, 32 | Ergonomics, boundaries, extensibility, dependency discipline, build tag/module hygiene, determinism |
| Specification | 19-22 | Domain model fidelity, design coherence, use-case coverage, cross-layer alignment |

**C++ system-level agent:**

| Scope | Categories | Notes |
|-------|-----------|-------|
| Architecture | 15-18, 31, 32 | Ergonomics, boundaries, extensibility, dependency discipline, ABI & compiler portability, CMake hygiene |
| Specification | 19-22 | Domain model fidelity, design coherence, use-case coverage, cross-layer alignment |

**Python system-level agent:**

| Scope | Categories | Notes |
|-------|-----------|-------|
| Architecture | 15-18, 31 | Ergonomics, boundaries, extensibility, dependency discipline, packaging hygiene |
| Specification | 19-22 | Domain model fidelity, design coherence, use-case coverage, cross-layer alignment |

**Documentation:** The cross-document pass (below) serves as the system-level review.

### Per-category reporting (mandatory, all agents in steps 1 and 2)

Each agent emits findings as one `## Category N: Name` section per category that has at least one finding, plus a single consolidated `## Coverage` section at the end listing every assigned category as `N covered` or `N skipped: <reason>`. Empty `## Category N: No findings.` blocks are no longer required (and are a token-efficiency violation if produced); silence on a category is interpreted as `covered, no findings` and is verified against the `## Coverage` table.

```
## Category N: Name
Finding N.1: [file:line] description
Finding N.2: [file:line] description

## Guideline: Name (→ Category N)
Finding G.1: [file:line] description

## Coverage
- 1 covered
- 2 covered
- 3 covered
- 4 covered (graduated; see memory/feedback_graduated_categories.md)
- ...
```

A `## Coverage` section that omits an assigned category is a procedure violation. A category listed as `skipped` must carry a reason (typically `graduated`, with a pointer to the graduated-set registry).

### Step 3: Coverage reconciliation and planning

Enter plan mode. Before collating findings:

1. **Coverage check**: verify that all categories received a report from exactly one agent (skipping graduated categories — those covered by mechanical gates, see Step 0). List any gaps. If a non-graduated category was missed, the round is incomplete — reassign and re-run before proceeding.
2. **Collate**: merge all findings into a single numbered plan. Present suspected false positives with justification; the user decides what to dismiss.
3. **No deferrals**: findings are fixed in the current round. "Future work" and "out of scope" are not valid dispositions. The only exception is when the user explicitly defers a finding after reviewing it.
4. **Explicit disposition per finding**: every entry in the collated plan must carry one of `FIX`, `FIX-PARTIAL`, `DEFER`, `NO-FIX`, `FP`, `FP-VERIFIED`, `DROP` before step 4 starts. Definitions are in `.archive/reviews/schema.yaml`. A plan containing unlabeled findings cannot proceed to step 4.
5. **Findings emitted as structured YAML at round close**: every closed finding gets exactly one file at `.archive/reviews/r<N>/findings/<id>.yaml` (schema enforced by `tools/review_db.py`). The round-scope working file `~/.claude/plans/review-r<N>-findings.md` is the human-readable draft; the per-finding YAMLs are the durable record. Round metadata at `.archive/reviews/r<N>/round.yaml` records `raw_findings_count`, `closed_findings_count`, agent fleet, merge SHA. The working `.md` can be archived to the round directory at merge if desired (it is not load-bearing once the YAMLs are written).

### Step 4: Implement and verify

Implement all approved fixes, then run the verification suite **in this canonical order** — later gates depend on earlier ones being clean:

1. **Agda**: `cabal run shake -- build` (Main.agda runtime closure → `libaletheia-ffi.so`; chains `check-stdlib-version` only — does NOT chain the proof-side gates), THEN the proof-side and invariant gates: `cabal run shake -- check-properties` (Properties / *Roundtrip / *WF + universal aggregator + Substrate.Unsafe walk — the actual proof-correctness gate, not reached by `build`), `check-invariants` (postulate / Unsafe-name allowlist), `check-no-properties-in-runtime` (architectural invariant), `check-erasure` (`@0` FFI marshaling assumption), `check-fidelity` (MAlonzo constructor-drift smoke test), `check-ffi-exports` (FFI export-name snapshot diff). For doc-only edits, `build` alone suffices since no proof can have drifted.
2. **Language-specific unit tests**: `python -m pytest`, `go test ./aletheia/ -race`, `ctest --test-dir cpp/build`.
3. **Lint gates**: `basedpyright`, `pylint`, `go vet`, `gofmt -l`, `clang-format --dry-run -Werror`, `clang-tidy -p build`.
4. **Cross-language benchmarks** (mandatory for runtime-affecting changes — see Universal Rules): `bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput`, compared against the most recent baseline. Two thresholds: (a) **steady-state noise floor ~2–4%** — the typical run-to-run jitter on a quiet host; (b) **±10% inter-run variance gate** — beyond this, a delta MUST be investigated, not dismissed as variance (the R12 protocol that caught the −16.1% `log_event` regression). The aspirational gate is no regression > 3% lane-by-lane after accounting for the noise floor; in practice anything inside ±10% reads as run-to-run jitter and anything outside requires root-causing. **When reporting bench runs**, always show four columns per lane: raw current mean, baseline mean, delta %, AND current stddev — the stddev is the only thing that lets the reader judge whether a delta is signal or noise (drop baseline σ first if width forces compression, never both). Before trusting a C++-only regression, verify `cpp/build/CMakeCache.txt` has `CMAKE_BUILD_TYPE:STRING=Release` — a Debug-pinned cache silently produces −20%+ (R15). The runner and binary now both refuse Debug trees, and each bench JSON records `system.build_type`; if a stored baseline predates R15 it has no `build_type` field, so double-check before comparing.

Changes to docs-only files may skip step 4 (benchmarks) after confirming no code changed.

### Cross-document pass (mandatory, documentation reviews only)

Documentation categories 5, 15, 16, 17, and 18 cannot be checked per-file — they require comparing what multiple files say about the same topic. After the per-file review agents finish, launch a dedicated cross-document agent that: (a) identifies every fact stated in more than one file, (b) flags each duplicate as a category 5 finding — agreement between copies does not make duplication acceptable, and (c) for each duplicate, identifies which file is the canonical source and which copies should become cross-references. A fact that appears in N files produces N-1 findings. This pass is separate from and in addition to the per-file rounds.

---

## Per-language categories and guidelines

Per-language category lists and guidelines have been split into per-file modules to reduce token cost of agent invocations. An agent assigned to a language reads only that language's file (plus this `AGENTS.md` for Universal Rules and the Review Procedure).

| Language | File | Categories |
|----------|------|------------|
| Agda     | [`AGENTS/agda.md`](AGENTS/agda.md)     | 32 |
| Go       | [`AGENTS/go.md`](AGENTS/go.md)         | 33 |
| C++      | [`AGENTS/cpp.md`](AGENTS/cpp.md)       | 33 |
| Python   | [`AGENTS/python.md`](AGENTS/python.md) | 34 |
| CI/CD    | [`AGENTS/cicd.md`](AGENTS/cicd.md)     | 5  |
| Documentation | [`AGENTS/docs.md`](AGENTS/docs.md) | 22 |

When citing a finding category in commit messages, round plans, or in-source markers, use the canonical reference form `<LANG> cat <N>` (e.g. `Agda cat 16`, `Python cat 26`) or the finding-id shorthand `<LANG>-<AGENT>-<CAT>.<NUM>` (e.g. `AGDA-A-1.1`). The full text of each category definition lives in the file above.
