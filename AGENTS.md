# AGENTS.md -- Code Review Protocol

This file defines the review protocol for the Aletheia project. Every review round must follow these rules exactly.

## Universal Rules (All Languages)

**Every finding must be fixed.** There are no exceptions. Nits, test gaps, polish, documentation, architecture, design -- everything. There is no such thing as "separate concern from a code review" or "not a review fix."

**Pre-existing issues are in scope.** If a review surfaces it, it gets fixed. Do not dismiss findings because they predate the current change.

**Reviews cover design and architecture, not just implementation.** A review is re-reading all the code and checking if every detail makes sense and is built correctly. Reviews are the only opportunity to reconsider design and architectural choices. Nothing is "disproportionate" for a review round. Cascading type-level changes, API redesigns, and module restructuring are all valid review outcomes.

**No category may be skipped.** Every category listed below must be checked in every review round, against every file in scope. Large files are not an excuse to skim -- recommending a split is itself a valid finding.

**Both local and end-to-end issues are in scope.** Review each file individually AND consider cross-module interactions, data flow, and layer boundaries.

## Review Procedure

1. Launch parallel review agents (typically 3), each covering a subset of categories.
2. Cross-verify all findings against the actual code before planning.
3. Dismiss false positives with explicit justification.
4. Enter plan mode to collate findings into a single actionable fix list.
5. Implement all fixes, then run the verification suite.

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
14. **Specification** -- do the types/proofs capture the intended properties? Gaps where a property is stated but not fully proven, or where the formalization diverges from the real-world requirement
15. **Performance** -- MAlonzo compilation patterns that hurt runtime (Fin vs N, unnecessary normalization, large pattern matches that compile poorly)
16. **Cross-layer** -- Agda <-> Haskell <-> Python/C++/Go boundary correctness: FFI assumptions, marshalling, type alignment

### Always in Scope

- Question all implementation choices -- is this the right algorithm, data structure, approach?
- Question all design and architecture -- are module boundaries right, are abstractions justified, is coupling minimized?
- Proof correctness, completeness, and strategy -- are the right things being proven? Are proofs about the code that runs?
- End-to-end issues that span multiple modules or layers

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
22. **Cross-layer alignment** -- does the Go binding correctly mirror the Agda core's semantics? Protocol details where the binding diverges?

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
22. **Cross-layer alignment** -- does the C++ binding correctly mirror the Agda core's semantics? Protocol details where the binding diverges?

### Verification

```bash
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
```

---

## Python

Python reviews follow the same principles as Go and C++. The Python binding is the original and most mature. Review with the same rigor.

### Verification

```bash
cd python && python3 -m pytest tests/ -v
cd python && basedpyright aletheia/
cd python && pylint aletheia/
```

---

## Documentation (14 categories)

Scope: ALL docs -- CLAUDE.md, PROJECT_STATUS.md, BUILDING.md, DESIGN.md, PITCH.md, README.md, and any other .md files.

Also applies to infrastructure changes (Shakefile, dist targets, packaging) since the docs describing them must be accurate.

### Hygiene (8)

1. **Accuracy** -- do stated facts (module counts, file paths, command examples) match reality?
2. **Staleness** -- references to removed files, old workflows, or completed phases described as in-progress
3. **Consistency** -- do different docs agree on the same facts?
4. **Completeness** -- are important features/workflows undocumented?
5. **Redundancy / single source of truth** -- each piece of information must appear in exactly one place; other docs must cross-reference, not duplicate. Duplicated facts are always a finding.
6. **Command correctness** -- do shell commands actually work as written?
7. **Link integrity** -- do internal cross-references resolve?
8. **Audience fit** -- is the right level of detail in the right doc?

### Precision (1)

9. **Precision & terseness** -- documentation must be precise, concise, non-ambiguous, and terse. Flag verbose/vague/ambiguous language.

### Deep (5)

10. **Structure & navigation** -- is there a clear reading path from "I just cloned this" to "I'm productive"?
11. **Worked examples & error guidance** -- do guides cover real use cases, not just the happy path? When something goes wrong, do docs explain why and how to fix?
12. **Decision rationale** -- are key design decisions explained where someone would naturally ask "why"?
13. **Onboarding friction** -- walk through as a newcomer. What assumptions are unstated?
14. **Hardcoded values & durability** -- counts, versions, performance numbers that will rot. Are they concentrated or scattered?
