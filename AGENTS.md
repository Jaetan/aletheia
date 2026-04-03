# AGENTS.md -- Code Review Protocol

This file defines the review protocol for the Aletheia project. Every review round must follow these rules exactly.

## Universal Rules (All Languages)

**A finding is a finding.** Every diagnostic surfaced by a tool run or manual review is an action item. The only correct response to a finding is to investigate it. Do not classify findings before investigating them. Any label that could justify inaction -- temporal ("pre-existing"), authorial ("not from our changes"), systemic ("build system artifact", "tooling issue", "compiler warning"), or scoping ("out of scope", "separate concern") -- is a dismissal mechanism disguised as a category. A finding has no origin, no age, no owner, and no source system. It is a thing that is wrong, and it gets fixed.

**Every finding must be fixed.** There are no exceptions. Nits, test gaps, polish, documentation, architecture, design -- everything. "Investigate" means: understand what is producing the diagnostic, determine whether the project can eliminate it, and either fix it or surface it to the user with an explanation. Concluding that a finding is not actionable without investigation is never acceptable.

**Reviews cover specification, design, and architecture, not just implementation.** A review is re-reading all the code and checking if every detail makes sense and is built correctly. Question the specification itself: are the features right? Do they make sense? Are assumptions correct? Should something be reworked? Reviews are the only opportunity to reconsider these choices. Nothing is "disproportionate" for a review round. Cascading type-level changes, API redesigns, module restructuring, and specification corrections are all valid review outcomes.

**No category may be skipped.** Every category listed below must be checked in every review round, against every file in scope. Large files are not an excuse to skim -- recommending a split is itself a valid finding.

**Both local and end-to-end issues are in scope.** Review each file individually AND consider cross-module interactions, data flow, and layer boundaries.

**The only valid dismissal is "suspected false positive".** Suspected false positives must be identified with explicit justification, but no finding may be discarded from the plan without the user's permission. Present all findings -- including those believed to be false positives -- and let the user decide.

**Backward compatibility is never a reason to avoid a change.** When writing or reviewing code, never let "this would break backward compatibility" prevent making the right design choice. Compatibility shims, deprecated aliases, old field names kept alongside new ones, and preserved-but-wrong interfaces are all forms of technical debt. Design the cleanest interface for the current need.

## Review Procedure

1. Launch parallel review agents (typically 3), each covering a subset of categories.
2. Cross-verify all findings against the actual code before planning.
3. Enter plan mode to collate findings into a single actionable plan. Present suspected false positives with justification; the user decides what to dismiss.
4. Implement all approved fixes, then run the verification suite.

**Cross-document pass (mandatory).** Documentation categories 5, 15, 16, 17, and 18 cannot be checked per-file — they require comparing what multiple files say about the same topic. After the per-file review agents finish, launch a dedicated cross-document agent that: (a) identifies every fact stated in more than one file, (b) flags each duplicate as a category 5 finding — agreement between copies does not make duplication acceptable, and (c) for each duplicate, identifies which file is the canonical source and which copies should become cross-references. A fact that appears in N files produces N-1 findings. This pass is separate from and in addition to the per-file rounds.

---

## Agda (16 categories)

Scope: ALL Agda modules -- production code and proofs alike. Never skip a file because it is large or proof-heavy.

### Hygiene/Style (12)

1. **Import/dead-code cleanup** -- unused imports, dead exports, unreferenced definitions
2. **Magic numbers** -- hardcoded numeric literals that should be named constants
3. **Comment quality** -- stale comments that no longer match the code, or misleading descriptions
4. **Naming consistency** -- inconsistent naming patterns across modules
5. **Proof simplification** -- proofs that could be shorter using better stdlib lemmas, or unnecessary case splits
6. **Redundant code patterns** -- repeated logic across modules that could share a helper
7. **Type tightness** -- places where `N` could be `Fin n`, or `List` could be `Vec`, or `String` could be an enum
8. **Error message consistency** -- inconsistent error/reason strings across modules
9. **API surface** -- over-exported or under-exported names
10. **Module size** -- modules that mix concerns or are large enough to split
11. **Structural patterns** -- repeated case-analysis boilerplate that could use combinators
12. **Unused where-block variables** -- computed but never referenced bindings

### Deep (4)

13. **Architectural** -- module boundaries, dependency direction, abstraction leaks, circular or unnecessary dependencies
14. **Specification** -- do the types/proofs capture the intended properties? Gaps where a property is stated but not fully proven, or where the formalization diverges from the real-world requirement. Proof correctness, completeness, and strategy -- are the right things being proven? Are proofs about the code that runs?
15. **Performance** -- MAlonzo compilation patterns that hurt runtime (Fin vs N, unnecessary normalization, large pattern matches that compile poorly)
16. **Cross-layer** -- Agda <-> Haskell <-> Python/C++/Go boundary correctness: FFI assumptions, marshalling, type alignment. All bindings must have identical behavior -- any divergence is a finding.

### Guidelines

**Import hygiene:**
- Bare `using ()` with no renaming clause is dead code -- remove the import line entirely.
- `using () renaming (A to B)` is valid and intentional -- it imports ONLY the renamed name. Do NOT flag as empty import.

**Proof style:**
- Prefer `cong`/`subst`/`trans` over chained `rewrite`. Each `rewrite` desugars to a with-auxiliary that copies the full goal type; on large goals (e.g., records with many fields), even 2 rewrites can cause >8 GB memory blowup. Max 1 rewrite per function on large goals.
- Don't pile up nested `suc`/`s≤s` constructors in absurd patterns. Use `_≤?_` with yes/no case analysis, helper lemmas, `Fin n`, or `toWitness`/`fromWitness` instead.
- Prove properties directly about the code that runs -- don't mediate through equivalence with an old code path. The specification is the desired behavior, not a prior implementation.
- Proofs can be updated for performance. When optimizing core functions, modify them directly and update dependent proofs rather than maintaining parallel "fast" and "proof" variants.

**Generalization:**
- When parameterizing types (e.g., `CANFrame n` for CAN-FD), generalize ALL layers (proofs, protocol, trace) with `∀ {n}` from the start. Do not pin at a fixed size as a shortcut.

### Verification

```bash
cd src && agda +RTS -N32 -M4G -RTS Aletheia/YourModule.agda
```

Use `-M4G` for all proof modules (catches memory blowups from rewrite chains). Use `-M8G` for larger modules if `-M4G` is too tight.

---

## Go (22 categories)

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
12. **Parsing robustness** -- handles all response variants, all three number formats (int/float/rational dict), error paths, no silent data loss
13. **FFI lifecycle** -- dlopen/hs_init/close ordering, null checks, string ownership via defer, never hs_exit
14. **Test adequacy** -- public API coverage, edge cases, negative paths, table-driven tests where appropriate, -race clean

### Architecture (4)

15. **API ergonomics** -- idiomatic Go (io.Closer, functional options, error wrapping), pit of success, zero-value usability
16. **Package boundaries** -- clean separation, no circular imports, internal/ where needed, build tag isolation
17. **Extensibility** -- adding new predicates, new operations doesn't break existing callers
18. **Dependency discipline** -- minimal external deps, cgo requirements documented, go.sum hygiene

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Go binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go) must have identical behavior -- any divergence is a finding.

### Verification

```bash
cd go && gofmt -l ./aletheia/
cd go && go test ./aletheia/ -v -count=1 -race
cd go && go vet ./...
cd go && CGO_ENABLED=0 go build ./aletheia/
```

---

## C++ (22 categories)

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
12. **Parsing robustness** -- handles all response variants, rational formats, error paths; no silent data loss
13. **FFI lifecycle** -- dlopen/hs_init/close ordering correct, null checks, string ownership
14. **Test adequacy** -- public API coverage, edge cases, negative paths, concurrency

### Architecture (4)

15. **API surface** -- minimal, consistent, hard to misuse (pit of success)
16. **Encapsulation** -- detail/ stays private, public headers don't expose nlohmann or implementation
17. **Extensibility** -- adding new predicates, new commands doesn't break existing API
18. **Build system** -- correct dependencies, no unnecessary exports to consumers

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the C++ binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go) must have identical behavior -- any divergence is a finding.

### Verification

```bash
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
clang-format --dry-run -Werror include/aletheia/*.hpp src/*.cpp src/detail/*.hpp tests/*.cpp
clang-tidy -p build src/*.cpp
```

---

## Python (22 categories)

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
12. **Parsing robustness** -- handles all response variants, all number formats (int/float/rational dict), error paths; no silent data loss
13. **FFI lifecycle** -- ctypes CDLL loading, hs_init ref-counting, string marshalling, GHC RTS constraints (never hs_exit)
14. **Test adequacy** -- public API coverage, edge cases, negative paths, fixture reuse via conftest; pytest -v clean

### Architecture (4)

15. **API ergonomics** -- Pythonic API (context managers, keyword args, sensible defaults), pit of success, clear import path from `aletheia`
16. **Package boundaries** -- clean separation between client, DSL, checks, loaders, CLI; no leaking of internal modules
17. **Extensibility** -- adding new predicates, loaders, or check types doesn't break existing callers
18. **Dependency discipline** -- minimal external deps; cantools/openpyxl/python-can/pyyaml justified; no unnecessary additions

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Python binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go) must have identical behavior -- any divergence is a finding.

### Verification

```bash
cd python && python3 -m pytest tests/ -v
cd python && basedpyright aletheia/
cd python && pylint aletheia/
```

---

## Documentation (21 categories)

Scope: ALL docs -- CLAUDE.md, PROJECT_STATUS.md, BUILDING.md, DESIGN.md, PITCH.md, README.md, and any other .md files.

Also applies to infrastructure changes (Shakefile, dist targets, packaging) since the docs describing them must be accurate.

### Hygiene (8)

1. **Accuracy** -- do stated facts (module counts, file paths, command examples) match reality?
2. **Staleness** -- references to removed files, old workflows, or completed phases described as in-progress
3. **Consistency** -- do different docs agree on the same facts?
4. **Completeness** -- are important features/workflows undocumented?
5. **Redundancy / single source of truth** -- each piece of information must appear in exactly one place; other docs must cross-reference, not duplicate. Duplicated facts are always a finding. Consistency between copies is not a defense — if the same fact appears in two files and both are correct, that is still a category 5 finding because one copy should be a cross-reference. Check within each file too: the same fact stated twice in one document is also a finding.
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
14. **Hardcoded values & durability** -- counts, versions, performance numbers that will rot. Are they concentrated or scattered?
15. **Code example testability** -- can every code snippet be copy-pasted and run? Check for wrong signatures, missing imports, undefined variables, wrong argument counts. Cross-check every call site against the actual API.
16. **Qualifier accuracy** -- are numbers qualified with their conditions? Every benchmark needs language, protocol, and entry-point context. "~48,000 fps" without "C++, CAN 2.0B, binary FFI" is a finding.
17. **Internal consistency** -- does a single file contradict itself? Different from category 3 (cross-document): this catches a file that states one thing in one section and the opposite in another.
18. **Scope labels on aggregates** -- when a number aggregates sub-items, is the scope stated? "532 tests" without "Python-only" is a finding when the total is 900+.
19. **Missing content & improvements** -- documentation that should exist but does not: missing troubleshooting sections, missing error guidance, missing design rationale, missing onboarding steps, missing recipes for common failure modes. These are findings, not suggestions — absent documentation is a defect when users would reasonably expect it.
20. **Numerical correctness** -- verify all arithmetic in examples: byte encodings, bit positions, scaling computations (factor × raw + offset), DLC-to-bytes mappings, unit conversions, and signal range calculations. A code example can have the right API call with wrong numbers. Cross-check every worked example against the DBC definition it references (start bit, length, byte order, factor, offset, signedness). This is distinct from category 15 (which checks that code *runs*) — this checks that the numbers are *mathematically correct*.
21. **Cross-language parity** -- when docs claim a feature exists in multiple bindings (Python, C++, Go), verify the claim against the actual code in each binding. Check that feature tables, API descriptions, and "all bindings support X" statements are accurate per-language. A feature documented as available in Go but missing from `go/aletheia/` is a finding. Compare: type names, method signatures, constructor options, error handling patterns, and enrichment fields across all three bindings.
