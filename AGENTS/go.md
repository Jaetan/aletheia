## Go (33 categories)

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
    - (c) **Cross-binding mock agreement**: all four binding mocks (Python canned responses, C++ `IBackend` defaults + `MockBackend`, Go `MockBackend`, Rust `MockBackend`) must agree for the same operation — if Go's mock returns `{"status":"ack"}` for `SendErrorBinary` but C++'s returns `{"status":"success"}`, that is a finding regardless of which is "correct".
    - (d) **Real-vs-mock divergence testing**: for operations where the mock response differs from the real FFI, there must be a test that exercises the real FFI format. If integration tests (real `.so`) are not available, update the mock to match and add a comment documenting what the real FFI returns. A mock chosen for convenience (e.g., `"success"` because `parseSuccessResponse` already works) rather than fidelity is a finding.
    - (e) **Regression test discipline**: every bug fix must be accompanied by a test that fails without the fix and passes with it. Landing a fix without a guarding test re-opens the regression surface the next time this file is refactored; prior-round fixes listed in memory are not substitutes — the test must live in the repo.
    - (f) **Test isolation**: `go test -shuffle=on -count=1 -race ./aletheia/` must pass — order-dependent flakes (shared tempdir, package-level state leaked between tests, goroutine leaks observed by the next test, `os.Setenv` without a paired restore, sync.Once consumed in a prior test) are findings. Tests must clean up tempdirs via `t.TempDir()`, register `t.Cleanup`, and use `t.Setenv` instead of raw `os.Setenv`. The `-shuffle=on` lane runs in CI alongside the deterministic lane; both must be green.
    - (g) **Mutation testing**: a mutation pass (`gomut`, `go-mutesting`, or `mutate`) on hot-path source files (`client.go`, `dbc.go`, `protocol.go`, `ffi_*.go`, `frame.go`) — surviving mutants on operational logic (not on log-string formatting, comment-tagged unreachable branches, or pure metadata/version strings) are findings. Justify any survivor with a comment block at the source site naming why the mutant is equivalent or unreachable; an unjustified survivor is a test gap. Mutation testing runs as a separate CI lane (cost is high) — once per PR is sufficient; per-commit is overkill.

### Architecture (4)

15. **API ergonomics** -- idiomatic Go (io.Closer, functional options, error wrapping), pit of success, zero-value usability
16. **Package boundaries** -- clean separation, no circular imports, internal/ where needed, build tag isolation
17. **Extensibility** -- adding new predicates, new operations doesn't break existing callers
18. **Dependency discipline** -- minimal external deps, cgo requirements documented, go.sum hygiene

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Go binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go, Rust) must have identical behavior -- any divergence is a finding. **Response contract audit**: for every client method, trace the response lifecycle: (a) what status strings can the Agda core return for this operation? (b) does the binding's parser accept all of them? (c) does the client method actually call the parser (not discard the response)? A parser that accepts `"success"` but not `"ack"` for an operation where the Agda core returns `"ack"` is a finding. A client method that calls a backend method and discards the response string with `_` is a finding — protocol errors from the Agda core would be silently lost. **Concrete cross-binding comparison**: for each of the 13 `Backend` interface methods, compare: (1) what the Python client does with the response, (2) what the C++ client does, (3) what the Go client does, (4) what the Rust client does. Any behavioral divergence is a finding. Python is the reference implementation — Python's `_ACK_BYTES` fast path in `send_error`/`send_remote` is the gold standard for event response handling

### Runtime Safety (3)

23. **Error wrapping & sentinel discipline** -- `fmt.Errorf("...: %w", err)` preserves the chain; `%v` silently drops it. Typed errors (`*aletheia.Error`) matched via `errors.As`, not string comparison. Sentinel errors must be package-level `var ErrX = errors.New(...)`, not re-created per call. `errors.Is`/`errors.As` at every catch point that reacts to a specific kind. No `strings.Contains(err.Error(), "...")` as a branch condition.
24. **`nil` & zero-value discipline** -- typed nil is not interface nil: `var e *Error = nil; var i error = e` satisfies `i != nil`. `nil` map writes panic; callers must initialize with `make(map[K]V)` before first write. `nil` slice vs empty slice differ in JSON output (`null` vs `[]`) — cross-binding parity requires one canonical form. Zero-value usability is a Go idiom: `&Client{}` must either work or fail loudly, never silently misbehave.
25. **Context propagation discipline** -- `context.Context` is the first parameter of any function that can block or be cancelled, never stored in a struct, never `nil` (`context.Background()` / `context.TODO()` instead). Every `ctx` argument must reach a `select { case <-ctx.Done(): }` or be passed downstream. Cancellation must propagate to every goroutine launched. `context.WithTimeout`/`WithCancel` must have their `cancel` called (usually via `defer cancel()`).

### Concurrency & Performance (2)

26. **Channel & goroutine lifecycle** -- the sender owns the close (closing from the receiver is a bug; closing twice panics; sending on closed panics). Every `go func(){…}()` must have a documented termination path. Goroutine leaks from forgotten `<-ch` on error paths are the most common Go bug; every `select` on a send or receive needs a `case <-ctx.Done():` unless the channel lifecycle is bounded. Buffered vs unbuffered is a design choice, not a performance knob -- buffer size must be justified.
27. **Hot-path performance** -- `defer` has per-call cost (~50ns) and matters inside tight loops; `strings.Builder` vs `+=` for concatenation; unnecessary interface boxing (`any` parameter causing heap escape); `sync.Pool` for per-frame allocations; `reflect` avoidance; slice growth via `append` without pre-sized capacity; map access patterns that can be a single compound op instead of lookup-then-insert. **Long-run stability**: a stability benchmark of ≥ 1M frames must not exceed the proven O(1) per-frame bound (no unbounded cache growth, no leaked goroutines, no slow map rehash amortized across millions of inserts). Per-frame throughput must stay within the variance band of the short-run benchmark. A run that degrades over time is a hot-path finding even if the short bench passes. **Long-run resource leakage sub-checks**: the stability bench must record (a) FD count delta — `len(must(os.ReadDir("/proc/self/fd")))` at start vs end — drift indicates a forgotten `Close` somewhere on the FFI/file-loader path; (b) goroutine count delta via `runtime.NumGoroutine()`, capturing the goroutine stack via `pprof.Lookup("goroutine").WriteTo(os.Stderr, 1)` on drift > 0 so the leaking call site is identifiable; (c) RSS delta via `runtime/metrics` (`/memory/classes/heap/objects:bytes` start vs end after `runtime.GC()`); (d) Haskell `StablePtr` accounting on the cgo side — a `StablePtr` retained past `Close()` is a bug regardless of whether `runtime.SetFinalizer` would eventually catch it. Every drift is a finding, not a "monitor over time" item.

### Security & I/O (2)

28. **Security / input sanitisation at cgo boundary** -- every `C.size_t` from Haskell must be bounds-checked before cast to `int`, every `*C.char` return must be nil-checked, `C.GoStringN(ptr, length)` is unsafe if `length` is attacker-controlled, `unsafe.Slice(ptr, n)` can create an out-of-bounds slice header. Path inputs from user data must go through `filepath.Clean` and be rejected on `..` traversal. **Adversarial-input bounds at the cgo entry**: every input from the C side (`*C.char` from `dlsym`'d return values, `C.size_t` length fields, response payloads from `processJSONLine` / `processFrameDirect`) must be bounds-checked against a documented maximum from `docs/architecture/PROTOCOL.md` § Limits before use — the Agda kernel checks bounds first (definitive), but the binding short-circuits oversized inputs at the FFI entry to avoid marshaling a payload that will be rejected. Overflow returns a typed `*aletheia.InputBoundExceededError` carrying the field name and limit, never a panic, never a slice header pointing past the buffer. See Universal Rules → "Adversarial-input bounds at parser surfaces".
29. **File I/O & encoding** -- `os.ReadFile` vs streaming for potentially large files (DBC files can be multi-MB), `bufio.Scanner` default 64KB buffer silently truncates long lines (must call `Buffer` explicitly), file open modes explicit (`os.O_RDONLY|os.O_CREATE|os.O_TRUNC` not magic numbers), library APIs accept `io.Reader` rather than `*os.File`, line endings handled portably, explicit UTF-8 validation for DBC strings, no `ioutil.*` usage (deprecated since Go 1.16).

### Observability & Diagnostics (1)

30. **Logging discipline (`slog` parity)** -- `slog` is the established logging path; the shared event set (count in `docs/LOG_EVENTS.yaml`), same field names, same field types as the C++ `Logger`, Python logger, and Rust binding logger. Use `slog.LogAttrs` in hot paths (skips the `any...` variadic allocation). Level discipline matches severity (Debug/Info/Warn/Error). No `log.Printf` or `fmt.Println` in library code. `slog.With` for scoped loggers at entry points, not per-call. Per-`Client` logger passed in, not pulled from `slog.Default()`.

### Build & Reproducibility (2)

31. **Build tag & module hygiene** -- `//go:build cgo && linux` for FFI files, `//go:build !cgo` stubs for portability (`ffi_nocgo.go`), no accidental duplicate symbols across build-tagged files, `go.mod` `go` directive matches CI version, `toolchain` directive explicit, no `replace` directives pointing at local paths in committed code, `go.sum` complete after every `go mod tidy`, minimal indirect deps.
32. **Determinism & reproducibility** -- Go `map` iteration order is randomized; user-visible output from `range m` is a correctness bug (tests pass locally, fail in CI). `slices.Sort` is not stable — use `slices.SortStableFunc` when tie-breaking matters. No `time.Now()` in library code that produces output. No `math/rand` at package level without an explicit `rand.NewSource(seed)`. JSON encoding order must match Python/C++ for cross-binding parity.

### Dynamic Correctness Analysis (1)

33. **Dynamic correctness analysis (sanitizers, fuzzers, property-based, cross-binding integration)** -- four sub-lanes that each cover correctness surfaces unit tests cannot reach:
    - (a) **Sanitizers beyond `-race`**: where toolchain support exists, run `CGO_CFLAGS="-fsanitize=address" CGO_LDFLAGS="-fsanitize=address" go test -tags=asan ./aletheia/` against the cgo paths. ASan catches use-after-free / double-free / heap-buffer-overflow on the cgo boundary that `-race` does not see. If the GHC RTS interferes with ASan instrumentation, document the gap in `docs/architecture/CGO_NOTES.md`; "we can't run ASan on the FFI path because of GHC" is itself a finding because the gap is unmitigated.
    - (b) **Native Go fuzz tests** (`testing.F`, Go ≥1.18): one fuzz target per binding-side parser/serializer (`FuzzParseResponse`, `FuzzMarshalCommand`, `FuzzDecodeBinaryFrame`, `FuzzParseRationalNumber`, `FuzzParseDBCJSON`); seed corpus committed under `go/aletheia/testdata/fuzz/<target>/`; CI runs each corpus as a 60s smoke (`go test -fuzz=Fuzz... -fuzztime=60s`) plus a nightly extended lane (`-fuzztime=1h`).
    - (c) **Property-based tests** (`testing/quick`): round-trip properties for every wire-format encode/decode pair (frame encode → decode → frame, response marshal → parse → response, command marshal → parse → command); parity invariants for every `Backend` method (the response field-set returned by `MockBackend` and `FFIBackend` must agree over generated inputs). A binding-side data type without a round-trip property is a finding under cat 14 (b)/(c) compounded — per-binding mock fidelity AND per-binding property-test coverage are the two halves.
    - (d) **Cross-binding integration test**: a single replay corpus (frames + DBC + checks) is fed through Python, Go, and C++ bindings via `libaletheia-ffi.so` in lockstep; the test asserts identical sequences of parsed responses, log events, and error cases — any divergence across bindings is a parity finding regardless of which binding is "right" (per `feedback_cross_language_parity.md`). Test lives at `go/aletheia/cross_binding_integration_test.go`, opt-in via `//go:build cross_binding` build tag, paired with the matching Python (`python/tests/test_cross_binding_integration.py`) and C++ (`cpp/tests/cross_binding_integration_tests.cpp`) entry points so the three bindings exercise the same fixtures from one canonical corpus.

### Verification

```bash
cd go && gofmt -l ./aletheia/
cd go && go test ./aletheia/ -v -count=1 -race
cd go && go test ./aletheia/ -shuffle=on -count=1 -race
cd go && go vet ./...
cd go && CGO_ENABLED=0 go build ./aletheia/
# Cat 33 dynamic-analysis lanes (opt-in via build tags or extended runs):
cd go && go test ./aletheia/ -fuzz=Fuzz -fuzztime=60s -run='^$'   # one target at a time; iterate
cd go && go test ./aletheia/ -tags=cross_binding -v               # cross-binding integration
# Cat 33 (a) sanitizer lane (when toolchain supports it):
cd go && CGO_CFLAGS="-fsanitize=address" CGO_LDFLAGS="-fsanitize=address" go test -tags=asan ./aletheia/
```

The `go test ./aletheia/` battery includes the Track D.2 doc-example
harness (`TestDocExamples`) — every ```go fence across `README.md`,
`docs/PITCH.md`, `docs/architecture/CANCELLATION.md`,
`docs/reference/INTERFACES.md`, and `docs/development/DISTRIBUTION.md`
is wrapped as `package main` in a per-fence tempdir (with a
`replace`-directive go.mod pointing at the local repo) and executed via
`go run`. The companion structural gate `TestNoNotestGoFences` rejects
`<!-- go notest -->` annotations: non-runnable fences must use the
`text` info string, mirroring the Python `python notest` ban
(`python/tests/test_doc_examples_harness.py`). Adding a new user-facing
markdown file means adding it to the `docFiles` list in
`go/aletheia/doc_examples_test.go`. Skipped automatically when
`libaletheia-ffi.so` is missing (run `cabal run shake -- build` first).

---

