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

## Review Procedure

Reviews run in two phases: per-file analysis (local concerns within each file) followed by system-level analysis (cross-file comparison and whole-program reasoning). Every category has exactly one owning agent. The agent prompt must list assigned categories and guidelines by number/name.

### Step 0: Carry-over review (before step 1)

Before launching any agents, the driver reads:
1. The most recent round's plan file in `~/.claude/plans/`.
2. `MEMORY.md` → any `project_*_deferred*` or `project_system_review_deferred*` entries.
3. In-source deferral comment blocks (see Universal Rules).

Every deferred finding from prior rounds is automatically a carry-over candidate for this round. If the conditions that justified deferral still hold, re-defer explicitly in this round's plan; if they no longer hold, the finding is live again and must be fixed. A deferred finding silently dropped across rounds is a procedure violation.

### Step 1: Per-file review (agents A, B, C in parallel)

Each agent reads files individually and checks local concerns. These categories can be fully evaluated by examining one file at a time.

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
| B: Correctness & Runtime | 7-14, 23-29 | Types, safety, serialization, parsing, FFI, tests, error wrapping, nil discipline, context, channel lifecycle, hot-path perf, cgo security, file I/O |

**C++ per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene & Style | 1-6, 30 | Style, naming, dead code, docs, errors, formatting, logging discipline |
| B: Correctness & Runtime | 7-14, 23-29 | Types, safety, serialization, parsing, FFI, tests, exception safety, UB hazards, data races, hot-path perf, stdlib idioms, security, file I/O |

**Python per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene & Style | 1-6, 27, 28, 32 | Style, naming, dead code, docs, errors, module organization, file I/O & encoding, logging discipline, doctest validity |
| B: Correctness & Runtime | 7-14, 23-26, 29-30 | Types, safety, serialization, parsing, FFI, tests, concurrency, mutability, hot-path perf, security, exception chaining, determinism |

**Documentation per-file agents:**

| Agent | Categories | Notes |
|-------|-----------|-------|
| A: Hygiene | 1-9 | Accuracy, staleness, consistency, completeness, redundancy, commands, links, audience, precision |
| B: Deep | 10-21 | Structure, examples, rationale, onboarding, durability, testability, qualifiers, internal consistency, scope labels, missing content, numerical correctness, cross-language parity |

### Step 2: System-level review (agent D, after step 1 completes)

Agent D takes a whole-program view. These categories cannot be evaluated per-file — they require understanding the dependency graph, type flow across module boundaries, or the system's overall design. Agent D launches after step 1 so it can reference per-file findings for context.

**Agda system-level agent:**

| Scope | Categories | Guidelines |
|-------|-----------|------------|
| Specification | 10 Domain model, 11 Invariants, 12 Property completeness, 13 Assumption audit, 19 Hypothesis propagation | G-A11 Validity predicates (→10, 11), G-A13 Generalization (→10), G-A17 Typed error handling (→11), G-A18 State machine encoding (→11), G-A7 Proof hypothesis discharge (→19) |
| Architecture | 14 API surface, 15 Module structure, 17 Cross-layer, 30 MAlonzo export surface stability, 31 Stdlib version pinning & API compatibility | G-A19 Binary FFI wire format (→17, 30), G-A20 Module separation (→15) |

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

Each agent must produce a section for every assigned category, even when no findings exist. Format:

```
## Category N: Name
Finding N.1: [file:line] description
Finding N.2: [file:line] description

## Category M: Name
No findings.
```

A missing section is a procedure violation. "No findings" after examination is a valid result; silence is not.

Each agent must also report on its assigned guidelines using the same format:

```
## Guideline: Name (→ Category N)
Finding G.1: [file:line] description
```

### Step 3: Coverage reconciliation and planning

Enter plan mode. Before collating findings:

1. **Coverage check**: verify that all categories received a report from exactly one agent. List any gaps. If a category was missed, the round is incomplete — reassign and re-run before proceeding.
2. **Collate**: merge all findings into a single numbered plan. Present suspected false positives with justification; the user decides what to dismiss.
3. **No deferrals**: findings are fixed in the current round. "Future work" and "out of scope" are not valid dispositions. The only exception is when the user explicitly defers a finding after reviewing it.
4. **Explicit disposition per finding**: every entry in the collated plan must carry one of three labels before step 4 starts: `FIX` (will be implemented this round), `FP` (suspected false positive — user confirmed), or `DEFER-<reason>` (user-approved deferral with pointer to in-source comment and/or memory file). A plan containing unlabeled findings cannot proceed to step 4.

### Step 4: Implement and verify

Implement all approved fixes, then run the verification suite **in this canonical order** — later gates depend on earlier ones being clean:

1. **Agda**: `cabal run shake -- build` (includes `check-invariants`, `check-no-properties-in-runtime`, `check-erasure`).
2. **Language-specific unit tests**: `python -m pytest`, `go test ./aletheia/ -race`, `ctest --test-dir cpp/build`.
3. **Lint gates**: `basedpyright`, `pylint`, `go vet`, `gofmt -l`, `clang-format --dry-run -Werror`, `clang-tidy -p build`.
4. **Cross-language benchmarks** (mandatory for runtime-affecting changes — see Universal Rules): `bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput`, compared against the most recent baseline. Two thresholds: (a) **steady-state noise floor ~2–4%** — the typical run-to-run jitter on a quiet host; (b) **±10% inter-run variance gate** — beyond this, a delta MUST be investigated, not dismissed as variance (the R12 protocol that caught the −16.1% `log_event` regression). The aspirational gate is no regression > 3% lane-by-lane after accounting for the noise floor; in practice anything inside ±10% reads as run-to-run jitter and anything outside requires root-causing. **When reporting bench runs**, always show four columns per lane: raw current mean, baseline mean, delta %, AND current stddev — the stddev is the only thing that lets the reader judge whether a delta is signal or noise (drop baseline σ first if width forces compression, never both). Before trusting a C++-only regression, verify `cpp/build/CMakeCache.txt` has `CMAKE_BUILD_TYPE:STRING=Release` — a Debug-pinned cache silently produces −20%+ (R15). The runner and binary now both refuse Debug trees, and each bench JSON records `system.build_type`; if a stored baseline predates R15 it has no `build_type` field, so double-check before comparing.

Changes to docs-only files may skip step 4 (benchmarks) after confirming no code changed.

### Cross-document pass (mandatory, documentation reviews only)

Documentation categories 5, 15, 16, 17, and 18 cannot be checked per-file — they require comparing what multiple files say about the same topic. After the per-file review agents finish, launch a dedicated cross-document agent that: (a) identifies every fact stated in more than one file, (b) flags each duplicate as a category 5 finding — agreement between copies does not make duplication acceptable, and (c) for each duplicate, identifies which file is the canonical source and which copies should become cross-references. A fact that appears in N files produces N-1 findings. This pass is separate from and in addition to the per-file rounds.

---

## Agda (31 categories)

Scope: ALL Agda modules -- production code and proofs alike. Never skip a file because it is large or proof-heavy.

### Hygiene/Style (9)

1. **Dead code** -- unused imports, unreferenced definitions, unused where-block variables, dead exports
2. **Magic numbers** -- hardcoded numeric literals that should be named constants
3. **Naming consistency** -- inconsistent naming patterns across modules
4. **Comment quality** -- stale comments that no longer match the code, misleading descriptions
5. **Error message consistency** -- inconsistent error/reason strings across modules
6. **Redundant patterns** -- repeated logic or case-analysis boilerplate that could share helpers or use combinators
27. **Stdlib coverage & lemma deduplication** -- hand-rolled lemmas that duplicate stdlib exports (commonly missed: `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.List.Properties`, `Data.Vec.Properties`); direction-symmetric lemma pairs (`foo-left`/`foo-right` where one is the composition of the other with a symmetry axiom); proof code copy-pasted between Properties submodules that should factor into a shared helper. A hand-written lemma that duplicates a stdlib export is a finding. This category is the home for the "Stdlib before rolling your own" guideline.
28. **Pragma abuse audit** -- cat 21 covers `OPTIONS` pragmas; this covers all other pragmas that bypass soundness checks. Production modules must not contain `{-# TERMINATING #-}`, `{-# NON_TERMINATING #-}`, `{-# NO_POSITIVITY_CHECK #-}`, `{-# INJECTIVE #-}`, `{-# NON_COVERING #-}`, `{-# REWRITE #-}`, or `{-# POLARITY #-}` — they bypass the termination/positivity/coverage checkers that `--safe` relies on. `{-# COMPILE #-}` and `{-# BUILTIN #-}` are valid but assert a Haskell/primitive bridge the review must verify for faithfulness.
29. **Instance & reflection discipline** -- instance arguments (`{{_ : Foo}}`) and reflection (`unquoteDecl`, `macro`) cause type-checking slowdowns and fragility: instance search can loop or resolve ambiguously; reflection macros generate invisible code. The project uses no reflection. Instance arguments appear only where stdlib operations mandate them (e.g., `.{{_ : NonZero q}}` on `_÷_` for ℚ; `.{{_ : NonZero n}}` on `_mod_`/`_%_` for ℕ) — these sites carry a `DEFER-stdlib-mandate` note at the top of the affected module (currently `CAN/Encoding/Properties/Arithmetic/Rational.agda`, `CAN/Endianness.agda`, `Data/BitVec/Conversion.agda`), and every call site supplies the witness explicitly so instance resolution stays trivial. Any other accidental introduction of instance-argument or reflection use is a finding. Further justified exceptions follow the standard deferral path (Universal Rules → "The only valid dismissal"): proposed in the round plan, labeled `DEFER-<reason>` after user approval, and recorded in-source.

### Types & Proofs (10)

7. **Type tightness** -- local type choice within a definition or module: `List` where `Vec n` fits, `String` where an enum fits, raw `ℕ` where a validated newtype fits, exploit dependent types for invariant enforcement. **Scope**: finds cases where the type used is strictly wider than the values it can hold within one file's control. Inter-module contract strength is cat 11, not this category
8. **Proof simplification** -- shorter proofs via stdlib lemmas, eliminating unnecessary case splits, combinator usage; consistent use of modern `with ... in eq` over legacy `inspect` idiom
9. **Proof soundness** -- proofs about the code that actually runs (not stale paths), correct proof strategy (cong/subst/trans vs rewrite chains), memory-safe patterns; **proof-to-implementation currency** — when core functions are refactored, dependent proofs must be updated, not mediated through equivalence with the old path; a proof that holds about a code path no longer taken is a finding
18. **Dead-branch provability** -- defensive fallbacks (`nothing → default`, catch-alls for constructors that cannot occur, "safety" Maybe returns) that are not reached by the calling pipeline. Either prove the branch is unreachable via a bound/hypothesis theorem (see `mkPredTable` + `indexHelper-bound`), or tighten the types so the branch cannot be constructed. A bare defensive fallback with no proof of unreachability and no comment pointing to one is a finding
20. **Termination metric hygiene** -- ranking: structural > length > fuel > well-founded; prefer the leftmost that works. Finding triggers: (a) the function uses a weaker metric than the next-leftmost option would have handled, with no justification, OR (b) the chosen metric is correct but not justified (fuel size has no comment identifying an upper bound on recursion depth; well-founded was used but structural/length could have). A well-justified length-based metric is fine and not a finding
22. **Irrelevance annotation `.(…)` discipline** -- load-bearing proof fields that are used only in type-checking (FFI boundary proofs, bounded-constructor witnesses, preconditions) should be marked `.(p : P)` to kill downstream `subst`/`transport` obligations. Irrelevant fields are ignored by `_≡_`, which simplifies call sites dramatically. The project currently uses relevant proofs everywhere; this category exists to surface candidates for irrelevance, not to mandate a blanket change. This category is the home for the "Irrelevance" guideline.
23. **Erasure `@0` discipline** -- runtime-erased arguments (`(@0 x : T)`) disappear at MAlonzo compile time. They must be genuinely unused at runtime; a load-bearing field mistakenly erased is a latent crash when MAlonzo projects a stub. Conversely, purely phantom fields (type-level tags, unit dimensions) kept runtime-relevant waste heap. `Timestamp (@0 u : TimeUnit)` is the worked example — any similar phantom parameter should follow suit.
24. **Pattern coverage & clause order** -- Agda's coverage checker is sound but clause-order-sensitive. Overlapping clauses that fire before the intended one silently hide bugs. `{-# CATCHALL #-}` pragmas masking missing cases. Implicit absurd patterns (`()`) vs explicit `⊥-elim` (prefer the latter when the impossibility is load-bearing for a reader). Redundant clauses that pass coverage but waste code. When a new data constructor is added (e.g., Path G's `FinalVerdict.Unsure`), every existing match on that type must be audited — any `CATCHALL` on it now hides a silent default.
25. **Universe level hygiene** -- `Set` vs `Set₁` vs `Setω`. Accidental universe polymorphism inflates type-checking time; levels leak through records (a field at `Set ℓ` forces the whole record up). The project is currently all `Set₀` (`Set`); any jump up the hierarchy must be justified. Gratuitously level-polymorphic helper lemmas `∀ {ℓ} {A : Set ℓ} → …` where `A : Set` would suffice are a finding.
26. **Equality discipline (`_≡_` vs `_==ᵇ_` vs `_≟_`)** -- propositional `_≡_` for proofs, boolean `_==ᵇ_`/`_<ᵇ_` for runtime branches, decidable `_≟_`/`_<?_` where you need both. Missing conversion lemmas (`P⇒Pᵇ`/`Pᵇ⇒P`) force duplicated proofs across call sites. **Owner boundary with cat 16**: this category owns the design choice ("which equality does this call site need?"), cat 16 owns the measured perf finding. Heuristic: if a `Dec`-valued check sits on a hot path but no benchmark has been run, it is a cat 26 finding (the choice is wrong). If the benchmark shows the regression, it is a cat 16 finding (the measured cost). Report it once, under the category matching the current evidence.

### Specification (6)

10. **Domain model fidelity** -- do the Agda types faithfully model the real-world CAN/DBC/LTL domain? Are there protocol features, edge cases, or real-world behaviors the model can't represent?
11. **Invariant sufficiency** -- inter-module contract strength: are type-level constraints the right ones? Runtime checks that could be compile-time guarantees? Over-constrained types rejecting valid inputs? Under-constrained types admitting invalid states? **Scope boundary with cat 7**: cat 7 is local ("this field could have been tighter"); cat 11 is systemic ("module X should guarantee P so that module Y's precondition is discharged at the type level"). A finding about a single field's type width is cat 7; a finding about the contract between two modules is cat 11
12. **Property completeness** -- are the proven properties the ones that matter for safety? Important unproven properties? Gap between what the proofs guarantee and what users believe the system guarantees?
13. **Assumption audit** -- implicit preconditions, unchecked coercions, model simplifications that could silently produce wrong results? Agreement with relevant standards (CAN 2.0B, ISO 11898, CAN-FD, DBC format)? MAlonzo compilation faithfulness?
19. **Hypothesis propagation** -- when a theorem takes a precondition (`Monotonic σ`, `TwoValued table`, `AllBelow b φ`), is the hypothesis enforced by an upstream runtime check, embedded as a structural type-level guarantee, or documented as an explicit caller obligation? A theorem whose hypothesis has no enforcement path is vacuously applicable and a finding. Pure mathematical identities (e.g. Kleene algebra laws on `⟦_⟧`) are the exception — they hold on all σ
21. **Safety flag & zero-postulate audit** -- every module carries `{-# OPTIONS --safe --without-K #-}` (plus `--no-main` where applicable); every production module contains zero `postulate` declarations; `*.Unsafe.agda` modules are the documented exception and must not be imported transitively by any safe module. Missing flags, stray postulates, or unsafe-via-import leakage are findings — this category is a gate on the whole soundness story

### Architecture & Performance (6)

14. **API surface** -- over-exported or under-exported names
15. **Module structure** -- modules mixing concerns or too large, dependency direction, circular or unnecessary dependencies; Properties modules that mix abstraction levels (e.g. termination bounds alongside completeness theorems in one file) should split per proof layer. Canonical worked example: on 2026-04-08 the 1581-line `CAN/Encoding/Properties.agda` and the 1256-line `Protocol/FrameProcessor/Properties.agda` were split into per-topic submodules (Arithmetic/Roundtrip/Disjoint and Step/Cache/Handlers/Bounded/Monotonic respectively) behind curated `open import X.Y public using (...)` facades. The facade pattern preserves the public API for downstream consumers (`LTL.Adequacy.WarmCache` still imports `AllBelow` and `mkPredTable-lookup` from the top-level path) and emits no runtime code of its own — MAlonzo's mangled symbols depend only on the submodule path, not the facade. Use this pattern when a Properties file passes ~600–800 lines or starts mixing termination/algebraic/topical abstraction layers
16. **Performance** -- MAlonzo compilation patterns: Fin compiles to O(n) suc chains (use ℕ on hot paths), normalization overhead, large pattern matches; **`Dec`-valued predicates allocate proof terms on every call — each `yes`/`no` is a closure, and nested quantifiers like `allBounded` build nested closures per iteration. Replacing an O(1) or Bool-valued check with a Dec-valued one in a hot path costs dramatically more than it looks on paper.** On 2026-04-07 commit `5aa345e` replaced the O(1) `rangesOverlap` in `BatchFrameBuilding.hasOverlaps` with the endianness-aware Dec-valued `physicallyDisjoint?`; CAN-FD frame building dropped 64% even though every correctness gate passed. The fix is a Bool-valued fast path with equivalence proofs (see `DBC/Properties.agda` `signalsPhysicallyOverlapᵇ` / `physicallyOverlapᵇ-sound` / `-complete`) — keep `Dec` for formal reasoning, use `Bool` for execution, and prove equivalence between them. Also watch: `Data.Sum.map₂`/`Maybe.map`/etc. allocate a per-call closure that direct pattern matching avoids. Any change to `Protocol/Handlers.agda`, `Protocol/StreamState.agda`, `CAN/Encoding*.agda`, `CAN/Batch*.agda`, `DBC/Properties.agda`, `LTL/Coalgebra.agda`, `LTL/Incremental.agda`, `LTL/SignalPredicate/Evaluation*.agda`, or anything transitively imported into `Main.agda` is NOT valid without pre-commit benchmark verification via `bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput` — correctness gates (ctest/go test/pytest/basedpyright) do not catch allocation-overhead regressions. See `feedback_hot_path_refactor_benchmark.md` for the full rule.
17. **Cross-layer** -- Agda ↔ Haskell ↔ binding boundaries: FFI assumptions, marshalling, type alignment, behavioral parity across all bindings. **Agda is the semantic source of truth.** Bindings conform to the Agda `Response` / `Protocol/ResponseFormat.agda` contract, not to each other. Python is the reference implementation for binding-layer ergonomics (context manager shape, exception types, CLI surface) but behavior differences between bindings are resolved by asking "what does Agda emit?", not "what does Python do?". **Response format specification**: when the Agda `Response` type or `responseToJSON` / `formatResponse` functions change, audit all three binding parsers for the affected operation. A new response variant (status string, field, or structure) that exists in Agda but is not handled by a binding parser is a finding. The canonical list of status strings per operation is derivable from `Protocol/ResponseFormat.agda` — if a binding parser accepts a status string not produced by that module, or rejects one that is, that is a cross-layer finding. **JSON wire-format evolution**: new status strings, new field names, field-type changes in `Response` are change-reviewed. Every such change requires: (a) an entry in this round's plan labeled `FIX`, (b) corresponding parser updates in all three bindings, (c) a round-trip test in at least one binding. An Agda-side change that lands without the three-binding update is a cross-layer finding. The worked example: Agda returns `"ack"` for error/remote events but C++ `parse_success` only accepted `"success"` (latent bug from 2026-04-10); Go discarded the response entirely. Both were cross-layer findings surfaced by tracing the response lifecycle from Agda to each binding
30. **MAlonzo export surface stability** -- `AletheiaFFI.hs` references MAlonzo mangled names (`d_processJSONLine_64`, `C_mkTs_26`, etc.). Renaming or reordering definitions changes the mangled suffix. The Shake build detects mismatches and prints a sed fix, but a review should verify any change to `Main.agda`, `Main/JSON.agda`, `Main/Binary.agda`, or any upstream module would not silently break Haskell shim references. Also checks the FFI export surface hasn't grown without a wire-format specification (parallel to the Binary FFI wire format guideline).
31. **Stdlib version pinning & API compatibility** -- `aletheia.agda-lib` pins `standard-library-2.3`. Imports must target 2.3's API, not 2.4+. Newly-added stdlib modules (post-2.3) must not be imported. Deprecation warnings in 2.3 should be noted. If the pin is bumped, review verifies no behavioral drift from any lemma reduction change between versions.

### Guidelines

Each guideline below carries a stable identifier (`G-A1`..`G-A20`) so the step-1/step-2 agent tables and finding reports can reference it directly. New guidelines should follow the shape: **Rule** (one-line imperative), **Why** (mechanism/incident), **How to apply** (when the reviewer should flag), **Example** (in-tree pointer or worked snippet). Existing guidelines vary in format — they were written over multiple review rounds and use the structure loosely; migrate them toward the shape when adjacent edits land, but do not rewrite en-masse.

**G-A1 — Import hygiene:**
- Bare `using ()` with no renaming clause is dead code -- remove the import line entirely.
- `using () renaming (A to B)` is valid and intentional -- it imports ONLY the renamed name. Do NOT flag as empty import.

**G-A2 — Proof style:**
- Prefer `cong`/`subst`/`trans` over chained `rewrite`. Each `rewrite` desugars to a with-auxiliary that copies the full goal type; on large goals (e.g., records with many fields), even 2 rewrites can cause >8 GB memory blowup. Max 1 rewrite per function on large goals.
- Don't pile up nested `suc`/`s≤s` constructors in absurd patterns. Use `_≤?_` with yes/no case analysis, helper lemmas, `Fin n`, or `toWitness`/`fromWitness` instead.
- Prove properties directly about the code that runs -- don't mediate through equivalence with an old code path. The specification is the desired behavior, not a prior implementation.
- Proofs can be updated for performance. When optimizing core functions, modify them directly and update dependent proofs rather than maintaining parallel "fast" and "proof" variants.
- **Overlapping Kleene clauses don't reduce on abstract operands.** `_∧TV_`/`_∨TV_` (in `LTL/SignalPredicate/Types.agda`) only reduce definitionally for the FIRST matching clause. With an abstract operand, expressions like `True ∧TV x`, `x ∧TV True`, `False ∨TV x`, `x ∨TV False` stay stuck. Two unblocking tools: (a) `rewrite sym ih` to replace abstract denotations with concrete `True`/`False`, then case-split; (b) identity lemmas from `LTL/TruthVal/Properties.agda` (`∧TV-true-l`, `∧TV-false-l`, `∨TV-false-l`, etc.). On small goals (TruthVal equalities) `rewrite` is fine — the memory caveat above only applies to large record goals.
- **`cong₂ _OP_ refl eq` fails when `_OP_` is non-injective.** `_∧TV_`/`_∨TV_` are functions, not constructors, so Agda can't unify `f a b ≡ f a' b'` with `a ≡ a' × b ≡ b'`; the `refl` argument leaves an unsolvable metavariable. Fix: merge `trans (cong₂ f A B) (cong₂ f refl C)` into `cong₂ f A (trans B C)`.
- **Mirror function discrimination in preservation proofs.** When a function uses overlapping pattern matching with `with` discrimination on a sub-component (e.g., `absorb` checks the right child of `And`/`Or` against ψ's 13 LTL constructors and `with φ ≡ᵇ-proc ψ` for special cases), the preservation proof must mirror that structure exactly: write **per-outer-constructor private helpers** (e.g., `absorb-And-bound`, `absorb-Or-bound`) each with one clause per right-side constructor, using identical `with` patterns for the special cases. The top-level lemma becomes a thin dispatcher (one clause per outer constructor). A flat top-level proof would require an N×N cross-product of clauses; mirroring keeps it linear. See `FrameProcessor/Properties.agda` Property 27.
- **`subst T eq` to bridge decision procedure witnesses with `with … in eq`.** Decision procedures like `<⇒<ᵇ : m < n → T (m <ᵇ n)` return `T _`, not `_ ≡ true`. In an absurd branch of `with b in eq` (where `b = m <ᵇ n` and the current branch has `eq : b ≡ false`), use `⊥-elim (subst T eq (<⇒<ᵇ m<n))` — `subst T eq` transports `T (m <ᵇ n)` through `eq` to `T false = ⊥`. Do NOT try `trans (sym (<⇒<ᵇ …)) eq`; it fails with `UnequalTerms` because `<⇒<ᵇ` does not return an equality. Applies symmetrically to `≤⇒≤ᵇ`, `≡⇒≡ᵇ`, and any `P⇒Pᵇ`. See `FrameProcessor/Properties.agda` Property 28 (`checkMonotonic-<`).

**G-A3 — `in eq` idiom:**
- Modern Agda supports `with expr in eq` which both scrutinizes `expr` AND introduces `eq : expr ≡ scrutinee_pattern` in one step. Prefer this over the legacy `inspect` idiom (`with expr | inspect (λ x → expr) x`). New proofs must use `in eq`; legacy `inspect` calls encountered during a review round should be migrated. Mixed usage within a file is a category 3 (Naming consistency) finding; standalone legacy `inspect` is a category 8 (Proof simplification) finding.

**G-A4 — Irrelevance:**
- Agda's irrelevance annotation `.(p : P)` marks an argument as computationally irrelevant — it is used only in type-checking, never in runtime behavior or proof obligations. Consider irrelevance for (a) FFI boundary proofs where Haskell cannot inspect the witness anyway (e.g. `Standard : (n : ℕ) → .(T (n <ᵇ 2048)) → CANId`), (b) bounded-constructor proofs whose inhabitant is discarded, (c) any `T _` or `P ≡ Q` field that exists solely to enforce a precondition. Irrelevance can eliminate entire classes of `subst`/`transport` obligations in downstream proofs because irrelevant fields are ignored by `≡`. The project currently uses relevant proofs everywhere — reviewers should flag load-bearing proof fields that could become `.(…)` to simplify call sites.

**G-A5 — Termination metric choice:**
- Structural recursion on constructor descent is always preferred; Agda infers the metric and no justification is needed.
- Length-based recursion on `length xs` is acceptable for operations that cannot recurse on structurally inductive form (e.g., parser combinators on `String`, which is a primitive, not an inductive type).
- Fuel-based termination is acceptable ONLY when the fuel size is a provable upper bound on the recursion depth, with a one-line comment stating why (e.g. `walkMux fuel = length signals` because a multiplexor chain visits each signal at most once before cycle detection forces termination). A bare numeric fuel with no justification is a finding.
- Well-founded recursion (`<′`, `Acc`) is a last resort — it bloats MAlonzo output, complicates proofs, and should only be used when the other three options genuinely don't work.

**G-A6 — Dead branches:**
- Defensive fallbacks (`nothing → default`, impossible-constructor catch-alls, "safety" Maybe returns) must be either (a) eliminated by type sharpening so the impossible state cannot be constructed, or (b) proven dead by an external bound theorem. A bare defensive fallback with no proof of unreachability and no comment pointing to one is a finding.
- The external-proof approach keeps the runtime signature simple while documenting unreachability. Canonical pattern: `mkPredTable`'s `nothing → Unknown` fallback combined with `FrameProcessor/Properties.agda` Property 27 (`indexHelper-bound` + `mkPredTable-bounded`), which proves the fallback is unreachable under the stepping pipeline without rewriting the API.
- **Do not re-raise type-sharpening of `mkPredTable`'s atom index.** A future review may notice Property 27 proves the `nothing → Unknown` branch is dead and propose lifting the index from `ℕ` to `Fin (length atoms)`. This was analysed on 2026-04-08 and deliberately deferred: MAlonzo compiles `Fin n` as a unary Peano chain (`data T_Fin_10 = C_zero_12 | C_suc_16 T_Fin_10`), so every index becomes k heap-allocated cells vs the current `ℕ`-via-BUILTIN `Integer` representation, and the refactor would put that allocation cost on a per-frame hot path (`mkPredTable` → `stepL` → every Atomic cell). Same class of hazard as the `Dec`-vs-`Bool` regression (commit `5aa345e`, 30–65% throughput loss). The full rationale — refactor scope, hazard, recovery path — is recorded in-source above `mkPredTable` in `src/Aletheia/Protocol/StreamState/Internals.agda:91`; read it before re-opening the discussion. Corresponding memory: `project_system_review_deferred.md` item 11.1, `feedback_in_source_deferral_notes.md`.

**G-A7 — Proof hypothesis discharge:**
- A theorem `thm : P σ → Q σ` establishes `Q σ` only for σ where `P σ` holds. For `Q` to apply to the running system, one of: (a) an entry point enforces `P σ` at runtime and rejects violators (e.g. `handleDataFrame` rejects non-monotonic frames via `checkMonotonic`, making all accepted σ satisfy `Monotonic σ`), (b) the stream type makes `P σ` structurally inevitable (rarely achievable for runtime traces), or (c) the property's public boundary documents `P σ` as a caller obligation with a pointer to the enforcement path.
- A hypothesis with no enforcement path is a vacuous guarantee; the theorem is provable but never applies to production σ. Pure mathematical identities (`eventually-always-dual`, Kleene laws on `⟦_⟧`) are exempt — they hold for all σ and need no discharge.
- Reviews should trace each major theorem's hypothesis from its introduction down to the boundary where the production pipeline would need to establish it. "The caller guarantees X" in a comment is not discharge; it defers the obligation to whoever reads the comment.

**G-A8 — Flag hygiene:**
- Every module must begin with `{-# OPTIONS --safe --without-K #-}` (plus `--no-main` for entry-point modules compiled separately). Missing flags → finding; partial flags (only `--safe`, only `--without-K`) → finding.
- Every production module contains zero `postulate` declarations. A `postulate` in `src/` outside a dedicated `*.Unsafe.agda` module → finding, regardless of what it postulates.
- `*.Unsafe.agda` modules must not be imported transitively from any `--safe` module. Run `grep -r "import.*Unsafe" src/` during every review to verify isolation. A safe module importing an unsafe one breaks the soundness story; it's a finding that blocks merge.

**G-A9 — Where-block provability:**
- Where-block helpers that return a pair `(state , f x)` where both branches share the same `state` prevent external proofs from seeing `proj₁ = state` without reducing through the case split. Refactor as `(state , g x)` where `g : A → B` returns only the varying component. This makes `proj₁` reduce immediately without needing to case-split on `x`.

**G-A10 — Bounded types and proof-carrying constructors:**
- When a constructor carries a `T (n <ᵇ max)` proof (like `Standard n pf`), do NOT use `with`-abstraction or `rewrite` on `n <ᵇ max` in roundtrip proofs. The constructor's rigid type dependency prevents generalization — abstracting `n <ᵇ max` to a fresh variable `w` makes `T w ≠ T (n <ᵇ max)`, producing an ill-typed with-abstraction.
- Use `ifᵀ-witness` from `Prelude` instead: it proves `ifᵀ b then f else e ≡ f pf` by splitting on `b` internally. Apply as a regular function (`= ifᵀ-witness _ _ pf`), not via `with`. η for `⊤` closes the `true` case.
- At the FFI boundary, supply `unsafeCoerce ()` for `T (n <ᵇ max)` proof fields ONLY after validating bounds in Haskell. MAlonzo compiles `⊤`/`tt` to a nullary constructor equivalent to `()`.

**G-A11 — Validity predicates — sum of constraint sets, not globally-quantified record:**
- When a validity predicate `P : ... → A → Set` has fields that only apply to a subset of `A` (e.g., only to one byte order, only to a specific signal kind), refactor the record into a data type with one constructor per semantic case. Each constructor carries only the constraints that apply to its case.
- A globally-quantified record forces the same set of constraints on every value of `A`, even when some constraints are nonsensical on some subset. Classic instance: `PhysicallyValid` used to be a 4-field record quantifying `msb-ge-len : bitLength ∸ 1 ≤ startBit` over every signal; the field is BigEndian-specific (LE addresses from the LSB, so "MSB index ≥ bit length" has no LE meaning), and as a record field it rejected `startBit = 0`, `bitLength = 1` LE signals.
- Refactor pattern: `data P : ... → A → Set where p-LE : byteOrder ≡ LE → P ...; p-BE : byteOrder ≡ BE → constraint₁ → constraint₂ → ... → P ...`. The LE witness is a single `refl`; the BE witness carries all the bounds. Downstream proofs pattern-match on the outer constructor and handle the cases separately — honest about the semantics and amenable to Agda's definitional equality.
- See `src/Aletheia/DBC/Formatter/WellFormed.agda` `PhysicallyValid` and the `signal-roundtrip-go` proof in `Formatter/SignalRoundtrip.agda` for a worked example (closed §12.1 on 2026-04-08).

**G-A12 — Decidable check combinators (DBC validity):**
- For check functions that case-split on a single `Dec P`, use `requireDec`/`rejectDec` from `Validity.Combinators` instead of raw `with`-patterns. `requireDec dec issue` returns `[]` when `dec = yes _` (property holds); `rejectDec dec issue` returns `[]` when `dec = no _` (property fails). Sound/complete proofs become one-liners via `requireDec-sound`/`rejectDec-sound` etc.
- For pairwise (triangular) AllPairs proofs, use `liftTriangular-sound`/`liftTriangular-complete` instead of manual induction with `++-≡[]-split`/`++-≡[]-combine`.

**G-A13 — Generalization:**
- When parameterizing types (e.g., `CANFrame n` for CAN-FD), generalize ALL layers (proofs, protocol, trace) with `∀ {n}` from the start. Do not pin at a fixed size as a shortcut.

**G-A14 — Error types:**
- All module-boundary error handling uses typed error ADTs from `Aletheia.Error` (not `String ⊎ A`). Each domain has its own error type (`ParseError`, `FrameError`, `RouteError`, `HandlerError`, `DispatchError`). Cross-domain lifting uses `mapₑ` + wrapper constructors (e.g., `WrappedParseError`). Handler-level context uses `WithContext`. Only binary FFI entry points in `Main.agda` use literal error strings (by design -- Haskell FFI returns `String ⊎ Vec Byte`). New error constructors that bypass the typed ADTs are a finding. This guideline and **G-A17 (Typed error handling)** overlap intentionally: G-A14 is the "which type goes at which boundary" rule, G-A17 is the "adding new error paths" rule.

**G-A15 — Combinator-first:**
- Before writing pattern matching on `_⊎_` / `Maybe` / `_×_`, check if a combinator handles it (`Data.Sum.map`, `Data.Maybe.map`, `Data.Product.map₂`). Explicit case analysis should be the fallback, not the default.

**G-A16 — Stdlib before rolling your own:**
- Check the standard library before writing a new lemma. Commonly missed modules: `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.List.Properties`, `Data.Vec.Properties`. A hand-written lemma that duplicates a stdlib export is a finding.

**G-A17 — Typed error handling:**
- All module-boundary operations use typed error ADTs from `Aletheia.Error`. The five domain types (`ParseError`, `FrameError`, `RouteError`, `HandlerError`, `DispatchError`) cover all error-producing paths. New error paths must use the appropriate typed constructor, not `inj₁ "string"`. If a new domain emerges, add a new error type to `Error.agda` and a corresponding `errorCode`/`formatError` case. Binary FFI entry points are the sole exception (they return `String ⊎ Vec Byte` for Haskell marshalling).

**G-A18 — State machine encoding:**
- When a protocol has phases or states, ask whether transitions are enforced by types or only checked at runtime. Runtime-only state machines are specification gaps -- invalid transitions should ideally be unrepresentable.

**G-A19 — Binary FFI wire format:**
- Every binary FFI endpoint must document its wire format (field types, sizes, endianness, field order) in exactly one canonical location. All binding implementations must reference this specification. An undocumented wire format is a finding.

**G-A20 — Module separation:**
- Separate domain Types, Operations, and Properties into distinct modules (e.g., `CAN/Frame.agda` for types, `CAN/Encoding.agda` for operations, `CAN/Encoding/Properties.agda` for proofs). Don't put proofs alongside the implementation they verify -- it conflates "what runs" with "what we know about what runs."

### Verification

```bash
cd src && agda +RTS -N32 -M4G -RTS Aletheia/YourModule.agda
```

Use `-M4G` for all proof modules (catches memory blowups from rewrite chains). Use `-M8G` for larger modules if `-M4G` is too tight.

---

## Go (32 categories)

Scope: ALL Go source files and test files in `go/aletheia/`.

### Hygiene/Style (6)

1. **Naming conventions** -- Go MixedCaps (not underscores), acronym casing (ID not Id, FFI not Ffi), receiver names, consistent across package
2. **Package API surface** -- exported vs unexported, godoc comments on all exports, no over-export
3. **Dead code** -- unused types, functions, imports, variables
4. **Comment/doc quality** -- godoc format, [Type] cross-references, explains "why" not "what", no stale comments
5. **Error message consistency** -- consistent format, lowercase per Go convention, no punctuation
6. **Formatting** -- gofmt compliance (non-negotiable in Go), goimports ordering

### Type & Safety (4)

7. **Strong type coverage** -- no raw int/float64/string where a domain type exists; validated constructors
8. **Interface design** -- sealed interfaces correct, minimal surface ("accept interfaces, return structs"), no interface pollution
9. **cgo safety** -- memory management across Go/C boundary, C.free after C.CString, defer for RAII-equivalent, LockOSThread for thread-pinned FFI
10. **Goroutine & concurrency safety** -- sync.Once correctness, no data races (would fail -race), proper context.Context cancellation, channel direction types

### Correctness (4)

11. **Serialization fidelity** -- JSON output matches Agda protocol exactly (field names, types, structure, command strings)
12. **Parsing robustness** -- handles all response variants, all three number formats (int/float/rational dict), error paths, no silent data loss. **Discarded protocol responses**: every `Backend` method that returns `(string, error)` must have its string return parsed by the caller — `_, err := backend.Foo(...)` discarding the response string is a finding. Protocol-level errors (Agda core returning `{"status":"error","code":"..."}`) are invisible when the response is discarded; only FFI-level failures (nil pointer, dlsym failure) would be caught. The pattern `_, err :=` on a protocol response is always a bug. Worked example: `Client.SendError` / `Client.SendRemote` discarded the backend response (fixed 2026-04-10)
13. **FFI lifecycle** -- dlopen/hs_init/close ordering, null checks, string ownership via defer, never hs_exit
14. **Test adequacy** -- sub-checks:
    - (a) **Baseline coverage**: public API, edge cases, negative paths, table-driven tests where appropriate, `-race` clean.
    - (b) **Mock fidelity**: for every `Backend` method, verify `MockBackend` produces responses with the same status strings, field set, and schema as the real `FFIBackend`. A mock that returns `"success"` where the real FFI returns `"ack"` creates latent bugs where tests pass but production fails.
    - (c) **Cross-binding mock agreement**: all three binding mocks (Python canned responses, C++ `IBackend` defaults + `MockBackend`, Go `MockBackend`) must agree for the same operation — if Go's mock returns `{"status":"ack"}` for `SendErrorBinary` but C++'s returns `{"status":"success"}`, that is a finding regardless of which is "correct".
    - (d) **Real-vs-mock divergence testing**: for operations where the mock response differs from the real FFI, there must be a test that exercises the real FFI format. If integration tests (real `.so`) are not available, update the mock to match and add a comment documenting what the real FFI returns. A mock chosen for convenience (e.g., `"success"` because `parseSuccessResponse` already works) rather than fidelity is a finding.
    - (e) **Regression test discipline**: every bug fix must be accompanied by a test that fails without the fix and passes with it. Landing a fix without a guarding test re-opens the regression surface the next time this file is refactored; prior-round fixes listed in memory are not substitutes — the test must live in the repo.

### Architecture (4)

15. **API ergonomics** -- idiomatic Go (io.Closer, functional options, error wrapping), pit of success, zero-value usability
16. **Package boundaries** -- clean separation, no circular imports, internal/ where needed, build tag isolation
17. **Extensibility** -- adding new predicates, new operations doesn't break existing callers
18. **Dependency discipline** -- minimal external deps, cgo requirements documented, go.sum hygiene

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Go binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go) must have identical behavior -- any divergence is a finding. **Response contract audit**: for every client method, trace the response lifecycle: (a) what status strings can the Agda core return for this operation? (b) does the binding's parser accept all of them? (c) does the client method actually call the parser (not discard the response)? A parser that accepts `"success"` but not `"ack"` for an operation where the Agda core returns `"ack"` is a finding. A client method that calls a backend method and discards the response string with `_` is a finding — protocol errors from the Agda core would be silently lost. **Concrete cross-binding comparison**: for each of the 15 `Backend` interface methods, compare: (1) what the Python client does with the response, (2) what the C++ client does, (3) what the Go client does. Any behavioral divergence is a finding. Python is the reference implementation — Python's `_ACK_BYTES` fast path in `send_error`/`send_remote` is the gold standard for event response handling

### Runtime Safety (3)

23. **Error wrapping & sentinel discipline** -- `fmt.Errorf("...: %w", err)` preserves the chain; `%v` silently drops it. Typed errors (`*aletheia.Error`) matched via `errors.As`, not string comparison. Sentinel errors must be package-level `var ErrX = errors.New(...)`, not re-created per call. `errors.Is`/`errors.As` at every catch point that reacts to a specific kind. No `strings.Contains(err.Error(), "...")` as a branch condition.
24. **`nil` & zero-value discipline** -- typed nil is not interface nil: `var e *Error = nil; var i error = e` satisfies `i != nil`. `nil` map writes panic; callers must initialize with `make(map[K]V)` before first write. `nil` slice vs empty slice differ in JSON output (`null` vs `[]`) — cross-binding parity requires one canonical form. Zero-value usability is a Go idiom: `&Client{}` must either work or fail loudly, never silently misbehave.
25. **Context propagation discipline** -- `context.Context` is the first parameter of any function that can block or be cancelled, never stored in a struct, never `nil` (`context.Background()` / `context.TODO()` instead). Every `ctx` argument must reach a `select { case <-ctx.Done(): }` or be passed downstream. Cancellation must propagate to every goroutine launched. `context.WithTimeout`/`WithCancel` must have their `cancel` called (usually via `defer cancel()`).

### Concurrency & Performance (2)

26. **Channel & goroutine lifecycle** -- the sender owns the close (closing from the receiver is a bug; closing twice panics; sending on closed panics). Every `go func(){…}()` must have a documented termination path. Goroutine leaks from forgotten `<-ch` on error paths are the most common Go bug; every `select` on a send or receive needs a `case <-ctx.Done():` unless the channel lifecycle is bounded. Buffered vs unbuffered is a design choice, not a performance knob -- buffer size must be justified.
27. **Hot-path performance** -- `defer` has per-call cost (~50ns) and matters inside tight loops; `strings.Builder` vs `+=` for concatenation; unnecessary interface boxing (`any` parameter causing heap escape); `sync.Pool` for per-frame allocations; `reflect` avoidance; slice growth via `append` without pre-sized capacity; map access patterns that can be a single compound op instead of lookup-then-insert. **Long-run stability**: a stability benchmark of ≥ 1M frames must not exceed the proven O(1) per-frame bound (no unbounded cache growth, no leaked goroutines, no slow map rehash amortized across millions of inserts). Per-frame throughput must stay within the variance band of the short-run benchmark. A run that degrades over time is a hot-path finding even if the short bench passes.

### Security & I/O (2)

28. **Security / input sanitisation at cgo boundary** -- every `C.size_t` from Haskell must be bounds-checked before cast to `int`, every `*C.char` return must be nil-checked, `C.GoStringN(ptr, length)` is unsafe if `length` is attacker-controlled, `unsafe.Slice(ptr, n)` can create an out-of-bounds slice header. Path inputs from user data must go through `filepath.Clean` and be rejected on `..` traversal.
29. **File I/O & encoding** -- `os.ReadFile` vs streaming for potentially large files (DBC files can be multi-MB), `bufio.Scanner` default 64KB buffer silently truncates long lines (must call `Buffer` explicitly), file open modes explicit (`os.O_RDONLY|os.O_CREATE|os.O_TRUNC` not magic numbers), library APIs accept `io.Reader` rather than `*os.File`, line endings handled portably, explicit UTF-8 validation for DBC strings, no `ioutil.*` usage (deprecated since Go 1.16).

### Observability & Diagnostics (1)

30. **Logging discipline (`slog` parity)** -- `slog` is the established logging path; same 15 event names, same field names, same field types as C++ `Logger` and Python logger. Use `slog.LogAttrs` in hot paths (skips the `any...` variadic allocation). Level discipline matches severity (Debug/Info/Warn/Error). No `log.Printf` or `fmt.Println` in library code. `slog.With` for scoped loggers at entry points, not per-call. Per-`Client` logger passed in, not pulled from `slog.Default()`.

### Build & Reproducibility (2)

31. **Build tag & module hygiene** -- `//go:build cgo && linux` for FFI files, `//go:build !cgo` stubs for portability (`ffi_nocgo.go`), no accidental duplicate symbols across build-tagged files, `go.mod` `go` directive matches CI version, `toolchain` directive explicit, no `replace` directives pointing at local paths in committed code, `go.sum` complete after every `go mod tidy`, minimal indirect deps.
32. **Determinism & reproducibility** -- Go `map` iteration order is randomized; user-visible output from `range m` is a correctness bug (tests pass locally, fail in CI). `slices.Sort` is not stable — use `slices.SortStableFunc` when tie-breaking matters. No `time.Now()` in library code that produces output. No `math/rand` at package level without an explicit `rand.NewSource(seed)`. JSON encoding order must match Python/C++ for cross-binding parity.

### Verification

```bash
cd go && gofmt -l ./aletheia/
cd go && go test ./aletheia/ -v -count=1 -race
cd go && go vet ./...
cd go && CGO_ENABLED=0 go build ./aletheia/
```

---

## C++ (32 categories)

Scope: ALL source files, headers, and test files in `cpp/`.

**Tooling gates (hard requirements):**
- `clang-format --dry-run -Werror` must produce **zero violations** on all source files.
- `clang-tidy -p build` must produce **zero errors and zero warnings** on all source files.
- **Adding any suppression annotation** (`NOLINT`, `NOLINTNEXTLINE`, `NOLINTBEGIN/END`) **requires user approval**. Propose the annotation with justification; do not add it without explicit permission.

### Hygiene/Style (6)

1. **Naming consistency** -- matches .clang-tidy conventions across all files
2. **Formatting** -- .clang-format compliance
3. **Include hygiene** -- minimal includes, no implementation details leaking into public headers
4. **Dead code** -- no unused types, functions, or includes
5. **const-correctness** -- const where possible, no unnecessary mutability
6. **Comment quality** -- explains "why" not "what"; no stale comments

### Type & Safety (4)

7. **Strong type coverage** -- no raw int/double/string where a domain type exists
8. **Ownership & RAII** -- unique_ptr, move semantics, no raw owning pointers, no double-free
9. **Memory safety** -- no dangling references, no use-after-move, no buffer overflows
10. **Thread safety** -- per-instance isolation correct, documented, and tested

### Correctness (4)

11. **Serialization fidelity** -- JSON output matches the Agda protocol exactly (field names, types, structure)
12. **Parsing robustness** -- handles all response variants, rational formats, error paths; no silent data loss. **Response-status exhaustiveness**: response parsers that switch on status strings must account for all statuses the Agda core can produce for the operations they serve. A parser used by multiple client methods (e.g., `parse_success` serving both `parse_dbc` and `send_error`) must accept the union of all valid statuses across those methods. When a parser serves operations with different valid statuses, document the accepted set in a comment. Worked example: `parse_success` only accepted `"success"` but `send_error`/`send_remote` receive `"ack"` from the real FFI — latent bug fixed 2026-04-10 by adding `"ack"` acceptance
13. **FFI lifecycle** -- dlopen/hs_init/close ordering correct, null checks, string ownership
14. **Test adequacy** -- sub-checks:
    - (a) **Baseline coverage**: public API, edge cases, negative paths, concurrency.
    - (b) **Mock fidelity**: for every `IBackend` virtual method, verify the default implementation and `MockBackend` produce responses with the same status strings, field set, and schema as the real `FfiBackend`. A default that returns `"success"` where the real FFI returns `"ack"` creates latent bugs where tests pass but production fails.
    - (c) **Cross-binding mock agreement**: all three binding mocks (Python canned responses, C++ `IBackend` defaults + `MockBackend`, Go `MockBackend`) must agree for the same operation.
    - (d) **Real-vs-mock divergence testing**: for operations where the mock/default response differs from the real FFI, there must be a test that exercises the real FFI format. If integration tests (real `.so`) are not available, update the default to match and add a comment documenting what the real FFI returns. A default chosen for convenience (e.g., `"success"` because `parse_success` already works) rather than fidelity is a finding. Worked example: `IBackend::send_error_binary` / `send_remote_binary` defaults returned `"success"` while real FFI returns `"ack"` — fixed 2026-04-10.
    - (e) **Regression test discipline**: every bug fix must be accompanied by a test that fails without the fix and passes with it. A fix landed without a guarding test re-opens the regression surface the next time the file is refactored.

### Architecture (4)

15. **API surface** -- minimal, consistent, hard to misuse (pit of success)
16. **Encapsulation** -- detail/ stays private, public headers don't expose nlohmann or implementation
17. **Extensibility** -- adding new predicates, new commands doesn't break existing API
18. **Build system** -- correct dependencies, no unnecessary exports to consumers

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the C++ binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go) must have identical behavior -- any divergence is a finding. **Response contract audit**: for every client method, trace the response lifecycle: (a) what status strings can the Agda core return for this operation? (b) does the binding's parser accept all of them? (c) does the client method actually call the parser? A parser that accepts `"success"` but not `"ack"` for an operation where the Agda core returns `"ack"` is a finding. **Concrete cross-binding comparison**: for each of the 15 `IBackend` virtual methods, compare: (1) what the Python client does with the response, (2) what the C++ client does, (3) what the Go client does. Any behavioral divergence is a finding. Python is the reference implementation

### Runtime Safety (3)

23. **Exception safety & `noexcept` discipline** -- move constructors/assignment must be `noexcept` for STL container efficiency (vector reallocation picks copy over throwing-move), destructors must not throw during stack unwinding, exceptions must not cross the FFI boundary (would unwind through Haskell RTS frames), basic/strong/nothrow guarantees documented on public APIs, `throw;` vs `throw e;` distinction respected, destructor exception guards (`try`/`catch` around logging in destructors).
24. **Undefined behavior hazards** -- signed integer overflow (prefer unsigned or `__builtin_add_overflow` at boundaries), strict-aliasing violations (prefer `std::bit_cast`), unaligned loads on primitive types, lifetime-extended temporaries bound to `auto&&`, dangling references returned from functions, uninitialized reads, `reinterpret_cast` through non-matching types, pointer arithmetic outside array bounds.
25. **Data race & memory order discipline** -- `std::atomic` memory order choice justified (no gratuitous `seq_cst`, no unsound `relaxed`), lock hierarchy / acquisition order documented, no lock held across FFI call that could re-enter through Haskell, `std::mutex` vs `std::shared_mutex` choice justified, condition variable spurious wakeups handled via predicate loops, no plain reads/writes on shared non-atomic data without a lock.

### Performance & Runtime Discipline (2)

26. **Hot-path performance** -- unnecessary copies (`const T&` vs `T` on params, missing `std::move` on rvalues, copy-on-return killing NRVO), heap allocation in tight loops (prefer `std::array`/small-buffer types), `std::shared_ptr` where `std::unique_ptr` suffices, `std::function` indirection where templates fit, repeated `.find()` + `.insert()` pairs that should be `.try_emplace()`, small-string optimisation misses, `std::vector<bool>` surprises. **Long-run stability**: a stability benchmark of ≥ 1M frames must not exceed the proven O(1) per-frame bound (no unbounded cache growth, no arena fragmentation that slows allocation over time, no leaked `std::thread`). Per-frame throughput must stay within the variance band of the short-run benchmark. A run that degrades over time is a hot-path finding even if the short bench passes.
27. **Standard library idiomatic usage** -- C++23 features used where appropriate (`std::expected`, `std::print`, ranges, `std::byteswap`, `std::span`), `std::string_view` lifetime hazards (no views of temporaries), `std::optional` vs pointer for optional references, `std::from_chars` vs locale-dependent `strtod`/`stoi`, `std::format` vs iostream for non-log output, `std::span<const std::byte>` over `(const uint8_t*, size_t)` pairs.

### Security & I/O (2)

28. **Security / input sanitisation at FFI boundary** -- bounds checks on all size/length fields from callers, integer overflow on `size_t` arithmetic (`n * sizeof(T)` can wrap), null pointer checks on all input pointers including return values from `dlsym`, validation of DLC/frame-length fields before indexing, no trust of structure layout across the ABI, defensive handling of caller-owned strings.
29. **File I/O & encoding** -- `std::ifstream`/`std::ofstream` opened in correct mode (binary for payloads, text for DBC/YAML), stream state checked after every read (`good()`/`fail()`), `std::locale::global` never mutated, locale-independent parsing for numbers, `std::filesystem::path` instead of string concatenation, explicit handling of multi-byte UTF-8 in DBC strings.

### Observability & Diagnostics (1)

30. **Logging discipline** -- `Logger` class usage matches Go `slog` and Python parity (same 15 event names, same field names), lazy formatting (no string construction unless logger present), log level discipline (DEBUG/INFO/WARN/ERROR matches actual severity), `std::println(stderr, ...)` reserved for documented startup warnings (rts_cores mismatch), no `std::cout`/`std::cerr` in library code outside documented warning paths, no eager concatenation in disabled log calls.

### Build & Packaging (2)

31. **ABI & compiler portability** -- targets g++ >= 14 and clang >= 21 on Linux only; any `__attribute__`/`[[gnu::...]]` extension must work on both; no GCC-only builtins without a fallback; public headers use only C++23 features supported by both compilers; no reliance on undocumented layout of `std::` types; anonymous namespaces only in `.cpp` files, never in headers (ODR violations).
32. **Build reproducibility & CMake hygiene** -- `target_include_directories` uses `BUILD_INTERFACE`/`INSTALL_INTERFACE` correctly, no absolute paths baked into binaries, `__DATE__`/`__TIME__` not used, `target_link_libraries` scope (`PRIVATE`/`PUBLIC`/`INTERFACE`) intentional with no leaky `PUBLIC` on implementation-only deps, ctest targets isolated from each other (no shared temp files), FetchContent pinned to exact commits not floating branches, no global `add_definitions`.

### Verification

```bash
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
clang-format --dry-run -Werror include/aletheia/*.hpp src/*.cpp src/detail/*.hpp tests/*.cpp
clang-tidy -p build src/*.cpp
```

---

## Python (33 categories)

Scope: ALL source files in `python/aletheia/` and test files in `python/tests/`. The Python binding is the original and most mature. Review with the same rigor as Go and C++.

**Tooling gates (hard requirements):**
- `pylint` score must stay **10.00/10**. Any score drop is a blocking finding.
- `basedpyright` must produce **zero errors and zero warnings**. Any new diagnostic is a blocking finding.
- **Adding any suppression annotation** (`# type: ignore`, `# pylint: disable`, `# noqa`, `# pyright: ignore`) **requires user approval**. Propose the annotation with justification; do not add it without explicit permission.

### Hygiene/Style (6)

1. **PEP 8 & formatting** -- consistent style, line lengths, import ordering
2. **Naming conventions** -- snake_case for functions/variables, PascalCase for classes, UPPER_CASE for constants, leading underscore for private
3. **Dead code** -- unused imports, unreachable branches, unused variables, commented-out code
4. **Comment/doc quality** -- Google-style docstrings on public API, explains "why" not "what", no stale comments
5. **Error message consistency** -- consistent format across client, CLI, loaders; actionable messages
6. **Module organization** -- each module has a single concern; no circular imports; private modules prefixed with underscore

### Type & Safety (4)

7. **Type annotation coverage** -- all public functions fully annotated; basedpyright strict mode clean; TypedDict/Protocol/Literal used correctly
8. **Strong type usage** -- no bare `dict`/`list`/`Any` where a TypedDict, Protocol, or domain type exists; validated constructors
9. **Error handling** -- exceptions are specific (not bare `except`), raised with context, documented in docstrings; no silent swallowing
10. **Resource safety** -- ctypes handles cleaned up, file handles closed, context managers used where appropriate

### Correctness (4)

11. **Serialization fidelity** -- JSON output matches Agda protocol exactly (field names, types, structure, command strings)
12. **Parsing robustness** -- handles all response variants, all number formats (int/float/rational dict), error paths; no silent data loss. Response parsers must accept all status strings the Agda core can produce for the operations they serve
13. **FFI lifecycle** -- ctypes CDLL loading, hs_init ref-counting, string marshalling, GHC RTS constraints (never hs_exit)
14. **Test adequacy** -- sub-checks:
    - (a) **Baseline coverage**: public API, edge cases, negative paths, fixture reuse via `conftest`; `pytest -v` clean.
    - (b) **Mock fidelity**: for every operation, verify canned test responses use the same status strings, field set, and schema as the real FFI backend.
    - (c) **Cross-binding mock agreement**: all three binding mocks (Python canned responses, C++ `IBackend` defaults + `MockBackend`, Go `MockBackend`) must agree for the same operation — a divergence between mocks is a finding regardless of which is "correct".
    - (d) **Real-vs-mock divergence testing**: for operations where the mock response differs from the real FFI, there must be a test that exercises the real FFI format via the real `.so` integration tests. A mock chosen for convenience rather than fidelity is a finding.
    - (e) **Regression test discipline**: every bug fix must be accompanied by a test that fails without the fix and passes with it. A fix landed without a guarding test re-opens the regression surface the next time the file is refactored.

### Architecture (4)

15. **API ergonomics** -- Pythonic API (context managers, keyword args, sensible defaults), pit of success, clear import path from `aletheia`
16. **Package boundaries** -- clean separation between client, DSL, checks, loaders, CLI; no leaking of internal modules
17. **Extensibility** -- adding new predicates, loaders, or check types doesn't break existing callers
18. **Dependency discipline** -- minimal external deps; cantools/openpyxl/python-can/pyyaml justified; no unnecessary additions

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Python binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go) must have identical behavior -- any divergence is a finding. **Response contract audit**: for every client method, trace the response lifecycle: (a) what status strings can the Agda core return for this operation? (b) does the binding's parser accept all of them? (c) does the client method actually call the parser? **Python is the reference implementation**: when reviewing Python, check whether the C++/Go bindings match Python's response handling for each operation. Python's `_ACK_BYTES` fast path in `send_error`/`send_remote` is the gold standard for event response handling — the other bindings must match it. **Concrete cross-binding comparison**: for each of the 15 backend operations, compare what Python, C++, and Go do with the response. Any behavioral divergence is a finding

### Concurrency & Performance (3)

23. **Concurrency & GIL discipline** -- ctypes calls release the GIL, so concurrent `AletheiaClient` instances on distinct state pointers are legal but must not share mutable Python state without a lock. Flag shared `threading.Lock`/`RLock` missing on cross-thread mutable state, `hs_init` ref-counting races, per-thread state pointers held across threads, and any assumption that `hs_init` is called more than once per process.
24. **Mutability & aliasing hazards** -- default mutable arguments (`def f(x=[])`), shared list/dict aliasing across instances, `dataclass` without `frozen=True` where immutability is intended, `.copy()` vs `copy.deepcopy` at API boundaries, mutation of internal caches (`_signal_cache`, DSL state) during iteration.
25. **Hot-path performance** -- `json.dumps(..., sort_keys=True)` inside per-frame loops, unnecessary `ctypes.cast` round-trips, eager f-string formatting in `logger.debug(f"...")` (use `%`-style lazy args), `list()` materialization of generators used only for iteration, repeated attribute lookups inside tight loops. **Long-run stability**: a stability benchmark of ≥ 1M frames must not exceed the proven O(1) per-frame bound (no unbounded Python dict growth, no `ctypes` handle leaks, no logger-handler accretion across reconfigurations). Per-frame throughput must stay within the variance band of the short-run benchmark. A run that degrades over time is a hot-path finding even if the short bench passes.

### Security & I/O (2)

26. **Security / input sanitisation** -- `yaml.safe_load` (not `yaml.load`), no `pickle` on untrusted input, `subprocess` without `shell=True`, file path traversal from untrusted DBC/log inputs, XML entity expansion safety, credential leakage in logs.
27. **File I/O & encoding** -- `open()` must pass explicit `encoding=` (prefer `"utf-8"`), `pathlib.Path` used consistently rather than `os.path` string concatenation, resource loading via `importlib.resources` rather than `__file__`-relative paths, newline handling on text files, binary mode for non-text payloads.

### Observability & Diagnostics (2)

28. **Logging discipline** -- structured logging parity with Go `slog` and C++ `Logger` (same 15 event names, same fields); lazy log message formatting (`%`-style, not f-strings); `exc_info=True` on error paths; level usage matches severity (DEBUG/INFO/WARNING/ERROR); no `print()` in library code. Any helper that wraps `logger.log(...)` on a hot path MUST check `logger.isEnabledFor(level)` and early-return before building `extra` dicts / f-strings — R12's `log_event` missed this and regressed Python Stream LTL by −16.1% until `1e40b4d` restored the guard.
29. **Exception chaining & context** -- `raise X from Y` to preserve `__cause__`, never `except ... as e: raise RuntimeError(str(e))` (loses traceback), no bare `except:` (use `except Exception:` minimum), re-raises preserve original context, error messages are actionable.

### Packaging & Reproducibility (3)

30. **Determinism & reproducibility** -- no reliance on `dict`/`set` iteration order where output is user-visible, stable sort keys, no timestamp-dependent output in library code, explicit `random.Random(seed)` rather than module-level `random`, no `datetime.now()` in serialization paths.
31. **Packaging hygiene** -- `pyproject.toml` version pin policy (minimum versions, not exact pins for library code), entry points declared correctly, optional dependency groups (`[project.optional-dependencies]`), wheel/sdist symmetry, `[tool.*]` section consistency (pylint, basedpyright, pytest all configured here).
32. **Doctest & example validity** -- docstring `>>>` examples actually run (`pytest --doctest-modules`), README snippets type-check and execute, tutorial code in `docs/` stays in sync with the actual API, no stale imports or removed symbols in examples.

### Command-line Interface (1)

33. **Command-line interface quality** -- argparse wiring on every CLI subcommand: every flag/positional has a non-empty `help=` string, every subcommand has a one-line description visible from `--help`, mutually exclusive flags are grouped (`add_mutually_exclusive_group`), required arguments are validated at parse time not at use site. Exit codes follow Unix convention: `0` success, `1` generic failure, `2` argument/usage error (`argparse` default), distinct non-zero codes for distinct failure classes (parse error vs runtime error vs I/O error). Stderr/stdout discipline: diagnostic messages (warnings, errors, progress) go to stderr; primary output (parsed JSON, validation results, query responses) goes to stdout so downstream tools can pipe the output. No `print()` of progress to stdout. Argument validation happens before any FFI/I/O side effect — parse and type-check all flags before opening the shared library or any file. Tab-completion (argcomplete) is optional but if present must stay in sync with the `add_argument` declarations; stale completion specs are a finding.

### Verification

```bash
cd python && python3 -m pytest tests/ -v
cd python && basedpyright aletheia/
cd python && pylint aletheia/
```

---

## Documentation (22 categories)

Scope: ALL docs -- CLAUDE.md, PROJECT_STATUS.md, BUILDING.md, DESIGN.md, PITCH.md, README.md, and any other .md files.

Also applies to infrastructure changes (Shakefile, dist targets, packaging) since the docs describing them must be accurate.

### Hygiene (8)

1. **Accuracy** -- do stated facts (module counts, file paths, command examples) match reality?
2. **Staleness** -- references to removed files, old workflows, or completed phases described as in-progress
3. **Consistency** -- do different docs agree on the same facts?
4. **Completeness** -- are important features/workflows undocumented?
5. **Redundancy / single source of truth** -- each piece of information must appear in exactly one place; other docs must cross-reference, not duplicate. Duplicated facts across files are always a finding. Consistency between copies is not a defense — if the same fact appears in two files and both are correct, that is still a category 5 finding because one copy should be a cross-reference. **Scope boundary with cat 17**: cat 5 catches the same fact duplicated across multiple files (resolved by making one canonical and the rest cross-references). Cat 17 catches a single file contradicting itself (two sections disagreeing). Same-file duplication that is consistent is cat 5; same-file statements that disagree are cat 17.
6. **Command correctness** -- do shell commands actually work as written?
7. **Link integrity** -- do internal cross-references resolve?
8. **Audience fit** -- is the right level of detail in the right doc?

### Precision (1)

9. **Precision & terseness** -- documentation must be precise, concise, non-ambiguous, and terse. Flag verbose/vague/ambiguous language.

### Deep (12)

10. **Structure & navigation** -- is there a clear reading path from "I just cloned this" to "I'm productive"?
11. **Worked examples & error guidance** -- do guides cover real use cases, not just the happy path? When something goes wrong, do docs explain why and how to fix?
12. **Decision rationale** -- are key design decisions explained where someone would naturally ask "why"?
13. **Onboarding friction** -- walk through as a newcomer. What assumptions are unstated?
14. **Hardcoded values & durability** -- counts, versions, performance numbers that will rot. Are they concentrated or scattered? **Scope boundary with cat 16**: cat 14 catches durability/location issues (the same number living in five places that will drift). Cat 16 catches the qualifiers that must accompany the number (what hardware, what protocol, what entry-point produced the measurement). A "9,704 fps" scattered across three docs is cat 14; a "9,704 fps" stated anywhere without "(C++, binary FFI, CAN 2.0B, Ryzen 9 5950X)" is cat 16. A single number that is both scattered and unqualified yields one finding under each category.
15. **Code example testability** -- can every code snippet be copy-pasted and run? Check for wrong signatures, missing imports, undefined variables, wrong argument counts. Cross-check every call site against the actual API.
16. **Qualifier accuracy** -- are numbers qualified with their conditions? Every benchmark needs language, protocol, and entry-point context. "~48,000 fps" without "C++, CAN 2.0B, binary FFI" is a finding. **Scope boundary with cat 14**: cat 16 is about the qualifiers accompanying a number (do we know what produced it?); cat 14 is about the durability of the number itself (is it living in one place, or scattered across docs that will drift?). Fix the qualifier with cat 16, fix the location with cat 14.
17. **Internal consistency** -- does a single file contradict itself? This catches a file that states one thing in one section and the opposite in another. **Scope boundary with cat 3 and cat 5**: cat 3 catches two files disagreeing on the same fact; cat 5 catches the same fact duplicated across files (even when consistent); cat 17 catches a single file contradicting itself. A file that says "120 modules" in the introduction and "119 modules" in a later table is a cat 17 finding, not cat 3 or cat 5.
18. **Scope labels on aggregates** -- when a number aggregates sub-items, is the scope stated? "532 tests" without "Python-only" is a finding when the total is 900+.
19. **Missing content & improvements** -- documentation that should exist but does not: missing troubleshooting sections, missing error guidance, missing design rationale, missing onboarding steps, missing recipes for common failure modes. These are findings, not suggestions — absent documentation is a defect when users would reasonably expect it.
20. **Numerical correctness** -- verify all arithmetic in examples: byte encodings, bit positions, scaling computations (factor × raw + offset), DLC-to-bytes mappings, unit conversions, and signal range calculations. A code example can have the right API call with wrong numbers. Cross-check every worked example against the DBC definition it references (start bit, length, byte order, factor, offset, signedness). This is distinct from category 15 (which checks that code *runs*) — this checks that the numbers are *mathematically correct*.
21. **Cross-language parity** -- when docs claim a feature exists in multiple bindings (Python, C++, Go), verify the claim against the actual code in each binding. Check that feature tables, API descriptions, and "all bindings support X" statements are accurate per-language. A feature documented as available in Go but missing from `go/aletheia/` is a finding. Compare: type names, method signatures, constructor options, error handling patterns, and enrichment fields across all three bindings.

### Operational (1)

22. **Operational runbook — log-keyed symptom → cause → action** -- for every structured log event the bindings emit (the 12 shared slog/Logger/Python event names), the operations docs must contain an entry keyed on the event name with three fields: symptom (what the operator sees), likely cause (what produces it), suggested action (what to do next). The runbook must cover both library events (the standard 12) and binding-specific diagnostic paths (rts_cores mismatch warning, hs_init failure, .so load failure, ctypes signature mismatch). Missing runbook entries for emitted events are a finding — an event the code emits but the docs do not explain leaves an operator blind. The table of common error codes (PROTOCOL.md) is related but not identical: error codes describe protocol-level failures, runbook entries describe observational/operational events that may or may not carry an error code.
