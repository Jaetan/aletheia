## Rust (33 categories)

Scope: ALL Rust source files and test files in `rust/src/` and `rust/tests/`
(and `rust/excel/` where present). Mirrors the Go/C++ 33-category scheme so
cross-binding cross-references (`Rust cat 28`, `Rust cat 22`, …) line up with
their Go/C++ counterparts.

### Hygiene/Style (6)

1. **Naming conventions** -- Rust casing (`snake_case` items/fields, `UpperCamelCase` types/traits/variants, `SCREAMING_SNAKE_CASE` consts), acronym casing per the API guidelines (`CanId`, not `CANID`; `Ffi`, not `FFI`), consistent across the crate.
2. **Public API surface** -- `pub` vs `pub(crate)` vs private, `///` / `//!` doc comments on every public item, no over-export, re-exports (`pub use`) only for the intended prelude surface (`Client`, `ClientBuilder`, `Frame`, `AsyncClient`, `Backend`, `Check`, `Formula`/`Predicate`, `MockBackend`).
3. **Dead code** -- unused items, imports, and `#[allow(dead_code)]` escape hatches (clippy `dead_code` / `unused_imports` must be clean without suppression).
4. **Comment/doc quality** -- rustdoc format, intra-doc links (`[Client]`), explains "why" not "what", no stale comments, `# Examples` blocks are real doctests.
5. **Error message consistency** -- `Display` impls use a consistent lowercase-leading format with no trailing punctuation; error text does not leak internal type names.
6. **Formatting** -- `cargo fmt --check` clean (non-negotiable) and clippy import ordering; a formatter run is not a linter run (see `feedback_rust_verify_fmt_and_clippy.md`).

### Type & Safety (4)

7. **Strong type coverage** -- no raw `u32`/`u8`/`String` where a domain newtype exists; validated constructors (`CanId::standard` / `CanId::extended`, DLC-checked `Frame` builders), no primitive obsession at the public surface.
8. **Trait & enum design** -- sealed traits where the ADT is closed upstream (Agda-pinned `CanId`, `Predicate`, `Formula` are discriminated-union `enum`s, not open trait objects), minimal trait surface, `#[non_exhaustive]` used deliberately, no trait pollution.
9. **`unsafe` & FFI discipline (via `libloading`)** -- every `unsafe` block is minimal and carries a `// SAFETY:` justification; `libloading::Symbol` lifetimes are tied to the process-lifetime `Library` (the `Symbols` cache is `Symbol<'static>` on a leaked/`'static` handle); C-string ownership across the boundary is explicit; no dangling symbol after the library is dropped.
10. **`Send`/`Sync` & concurrency safety** -- `Send`/`Sync` bounds across the FFI seam are correct and justified, the GHC RTS init is thread-pinned, no data races, and the async surface is cancellation-safe (a dropped future must not leave the worker wedged).

### Correctness (4)

11. **Serialization fidelity** -- `serde_json` output matches the Agda protocol exactly (field names, types, structure, command strings); numeric fields honor the decimal SSOT (`rust/tests/decimal_ssot.rs`) — a bare int for denominator 1, `{numerator, denominator}` otherwise, never a float.
12. **Parsing robustness** -- handles all response variants, all three number formats (int / float / rational dict), error paths, no silent data loss. A decoder that silently blanks a malformed `code` / `errors` / `absent` field instead of rejecting it is a finding (the r24 lenient-outlier lesson — Rust was the lone binding that blanked; the fix restored parity).
13. **FFI lifecycle** -- `dlopen` (via `libloading`) / `aletheia_init` / close ordering, null-pointer checks on every returned handle, never call `hs_exit`, and the symbol cache resolves once and stays non-latching (an export-less library fail-fasts but stays loaded).
14. **Test adequacy** -- sub-checks:
    - (a) **Baseline coverage**: public API, edge cases, negative paths, `cargo test` clean including the `async` and `--no-default-features` matrices.
    - (b) **Mock fidelity**: for every `Backend` method, `MockBackend` (`rust/tests/mock_backend.rs` / `rust/src`) produces responses with the same status strings, field set, and schema as the real `FfiBackend`.
    - (c) **Cross-binding mock agreement**: the four binding mocks (Python canned responses, C++ `IBackend` defaults + `MockBackend`, Go `MockBackend`, Rust `MockBackend`) must agree for the same operation — a divergence is a finding regardless of which is "correct".
    - (d) **Real-vs-mock divergence testing**: where the mock response differs from the real FFI, a test exercises the real `.so` format (or the mock is corrected and a comment documents the real FFI shape). A mock chosen for convenience over fidelity is a finding.
    - (e) **Regression test discipline**: every bug fix ships with a test that fails without the fix and passes with it; a prior-round memory note is not a substitute for an in-repo test.
    - (f) **Test isolation**: tests must not depend on execution order or shared global state; env-var mutation is scoped and restored; no leaked worker threads observed by the next test.
    - (g) **Mutation testing**: where `cargo-mutants` support exists, a mutation pass over hot-path source (`response.rs`, `dbc.rs`, `types.rs`, the FFI backend) — surviving mutants on operational logic are findings; justify any survivor with a source-site comment (equivalent/unreachable), never a fake-state test (see `feedback_unkillable_mutant_is_design_signal.md`).

### Architecture (4)

15. **API ergonomics** -- idiomatic Rust: builder pattern (`ClientBuilder`), `Result`-returning fallible APIs, `Default` usability, the pit of success, `impl Trait` / `IntoIterator` inputs where laziness is the contract (per `feedback_property_defined_task_acceptance.md`).
16. **Module boundaries** -- clean module separation (`types` / `dbc` / `response` / `log` / `yaml`), no cyclic module deps, `pub(crate)` for internals, feature-gated modules compile in isolation.
17. **Extensibility** -- adding a predicate, response variant, or operation does not break existing callers; `#[non_exhaustive]` guards the enums that will grow.
18. **Dependency discipline** -- minimal crates, optional features off by default where they pull weight (`async`), the async surface stays runtime-agnostic (only `futures-channel`/`futures-util` combinators, never a committed runtime), `Cargo.lock` committed.

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps the model cannot express?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Rust binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go, Rust) must have identical behavior -- any divergence is a finding. **Response contract audit**: for every client method, trace the response lifecycle: (a) what status strings can the Agda core return for this operation? (b) does the binding's parser accept all of them? (c) does the client method actually consume the parsed response? **Concrete cross-binding comparison**: for each of the 13 backend operations, compare what Python, C++, Go, and Rust do with the response. Any behavioral divergence is a finding. Python is the reference implementation for binding-layer ergonomics; behavior differences are resolved by "what does Agda emit?", not "what does Python do?".

### Runtime Safety (3)

23. **Typed error & `?` discipline** -- a typed `Error` enum implementing `std::error::Error`, matched by variant (never by `Display` string comparison); `?` propagation over manual `match`; no `unwrap()` / `expect()` / `panic!` on a reachable library path (test code may `unwrap`). Typed protocol errors (`input_bound_exceeded`, the validation-issue variants) are surfaced as distinct enum variants, not stringly-typed.
24. **Ownership & borrow discipline** -- no needless `clone()` on the hot path, lifetimes tightened rather than `'static`-escaped, `&str` over `String` at API boundaries, no `Rc`/`RefCell` where plain ownership suffices, no `Arc<Mutex<…>>` where a channel token would do (the `Client` concurrency seam mirrors the Go 1-deep semaphore choice — see `docs/architecture/CANCELLATION.md`).
25. **Async cancellation discipline** -- the `AsyncClient` is runtime-agnostic (works under tokio / async-std / smol); a dropped in-flight future releases the worker; cancellation propagates to the reply channel; no `block_on` in library code; the DI seam (`build_async_with_backend`) exists so cancellation is deterministically testable without sleeps (`feedback_no_physical_time_in_tests.md`).

### Concurrency & Performance (2)

26. **Channel & task lifecycle** -- the `oneshot` reply channel has a documented sender/receiver ownership; every spawned worker has a termination path; a forgotten receiver on an error path must not wedge the worker; buffered vs unbuffered is a justified design choice, not a perf knob.
27. **Hot-path performance** -- avoid per-frame allocation (mirror the `Bool` fast-path parity of the other bindings), pre-size `Vec` capacity, avoid needless boxing / dynamic dispatch on the send path, reuse the resolved symbol cache. **Long-run stability**: a ≥ 1M-frame run must hold the O(1) per-frame bound (no unbounded cache growth, no leaked threads, no RSS drift); a run that degrades over time is a finding even if the short bench passes.

### Security & I/O (2)

28. **Security / adversarial-input bounds at the FFI entry** -- every input crossing the FFI boundary (response payloads, length fields, DBC/JSON/YAML text) is bounds-checked against the documented maxima in `docs/architecture/PROTOCOL.md` § Limits before use — the Agda kernel checks bounds first (definitive), and the binding short-circuits oversized inputs at the FFI entry. Overflow surfaces as a typed `input_bound_exceeded` error carrying the field and limit, never a `panic!`, never an OOM. Path inputs are validated against `..` traversal. See Universal Rules → "Adversarial-input bounds at parser surfaces".
29. **File I/O & encoding** -- large DBC/YAML files handled without unbounded buffering surprises, explicit UTF-8 validation for DBC strings (`String::from_utf8` errors are surfaced, not `from_utf8_lossy`-swallowed), file open modes explicit, APIs accept `impl Read` where streaming matters.

### Observability & Diagnostics (1)

30. **Logging discipline** -- structured logging parity with the C++ `Logger`, Go `slog`, and Python logger: the shared event set (count in `docs/LOG_EVENTS.yaml`), same field names, same field types. Lazy formatting (no string construction unless a logger is attached), level discipline matching severity, no `println!` / `eprintln!` in library code outside documented startup-warning paths, a per-`Client` logger passed in rather than a global.

### Build & Reproducibility (2)

31. **Feature-flag & crate hygiene** -- the crate builds under `--no-default-features` and under each feature (`yaml`, `async`) in isolation; optional deps are gated with `dep:`; `Cargo.lock` is committed; the published manifest carries no path dependencies; the SPDX header + license field match the repo (`BSD-2-Clause`).
32. **Determinism & reproducibility** -- `HashMap` iteration order must never reach user-visible output (use `BTreeMap` or an explicit sort); no `SystemTime::now()` / `Instant::now()` in output-producing library code; JSON key/collection order matches the Python/C++/Go serialization for cross-binding parity.

### Dynamic Correctness Analysis (1)

33. **Dynamic correctness analysis (sanitizers, fuzzers, property-based, cross-binding)** -- four sub-lanes, each aspirational where toolchain support exists:
    - (a) **`unsafe`-path checking**: run Miri and/or ASan against the `libloading` FFI paths where the GHC RTS permits it; an unmitigated gap ("we can't run Miri across the FFI because of the RTS") is itself a documented finding, not silence.
    - (b) **Fuzzing** (`cargo fuzz`): one target per binding-side parser/serializer (response decode, command marshal, binary-frame decode, rational-number parse, DBC-JSON parse); seed corpus committed; a short CI smoke plus an extended nightly lane.
    - (c) **Property-based tests** (`proptest` / `quickcheck`): round-trip properties for every wire-format encode/decode pair, and parity invariants for every `Backend` method (`MockBackend` and `FfiBackend` field-sets must agree over generated inputs).
    - (d) **Cross-binding parity**: the shared replay-corpus integration harness (`libaletheia-ffi.so` in lockstep) currently covers Python/Go/C++; Rust's cross-binding guarantee is carried by the FEATURE_MATRIX parity gate (`rust/tests/feature_matrix.rs`), which resolves every `implemented` matrix entry against `rust/src/`. Extending the replay harness to Rust is a valid finding, but do not describe Rust as already in it.

### Verification

```bash
cd rust && cargo fmt --check
cd rust && cargo clippy --all-targets -- -D warnings
cd rust && cargo test
cd rust && cargo test --no-default-features          # yaml/async features off
cd rust && cargo test --features async               # async client surface
cd rust && cargo doc --no-deps                        # rustdoc warnings are findings
```

`rust/tests/feature_matrix.rs` is the cross-binding parity gate: it parses
`docs/FEATURE_MATRIX.yaml` and, for every row marked `implemented` on the `rust`
binding, verifies the stated entry resolves as a whole-word symbol over
`rust/src/`. A silent removal or rename of a public symbol fails this test the
same way a broken unit test does — updating the YAML is part of the change, not
a follow-up.

---
