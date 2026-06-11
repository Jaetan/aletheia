## C++ (33 categories)

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
    - (f) **Test isolation**: `ctest --schedule-random --output-on-failure` must pass — order-dependent flakes (shared tempdirs, static-init ordering surprises, `std::thread` leaks across cases, libaletheia-ffi state retained between cases) are findings. Each test fixture must clean up via RAII; static globals modified during a test must be restored via scope-exit guard. The `--schedule-random` lane runs in CI alongside the deterministic lane; both must be green.
    - (g) **Mutation testing**: a Mull (or equivalent — Dextool-mutate, mull-runner) pass on `cpp/src/*.cpp` — surviving mutants on operational logic are findings. Justify any survivor with a comment block at the source site; an unjustified survivor is a test gap. Mutation testing runs as a separate CI lane (cost is high) — once per PR is sufficient.

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

26. **Hot-path performance** -- unnecessary copies (`const T&` vs `T` on params, missing `std::move` on rvalues, copy-on-return killing NRVO), heap allocation in tight loops (prefer `std::array`/small-buffer types), `std::shared_ptr` where `std::unique_ptr` suffices, `std::function` indirection where templates fit, repeated `.find()` + `.insert()` pairs that should be `.try_emplace()`, small-string optimisation misses, `std::vector<bool>` surprises. **Long-run stability**: a stability benchmark of ≥ 1M frames must not exceed the proven O(1) per-frame bound (no unbounded cache growth, no arena fragmentation that slows allocation over time, no leaked `std::thread`). Per-frame throughput must stay within the variance band of the short-run benchmark. A run that degrades over time is a hot-path finding even if the short bench passes. **Long-run resource leakage sub-checks**: the stability bench captures (a) RSS via `/proc/self/status` `VmRSS` start vs end (after explicit shrink-to-fit on caches); (b) FD count via `count_if(directory_iterator("/proc/self/fd"), …)`; (c) `std::thread` lifecycle — every constructed thread joined or detached deliberately, no `std::async` chain that accumulates a `std::future` queue, no detached-thread escape; (d) heap fragmentation via `malloc_info` snapshot diff, since arena fragmentation that does not show as RSS still inflates allocation latency over time. Drift on any sub-check is a finding.
27. **Standard library idiomatic usage** -- C++23 features used where appropriate (`std::expected`, `std::print`, ranges, `std::byteswap`, `std::span`), `std::string_view` lifetime hazards (no views of temporaries), `std::optional` vs pointer for optional references, `std::from_chars` vs locale-dependent `strtod`/`stoi`, `std::format` vs iostream for non-log output, `std::span<const std::byte>` over `(const uint8_t*, size_t)` pairs.

### Security & I/O (2)

28. **Security / input sanitisation at FFI boundary** -- bounds checks on all size/length fields from callers, integer overflow on `size_t` arithmetic (`n * sizeof(T)` can wrap), null pointer checks on all input pointers including return values from `dlsym`, validation of DLC/frame-length fields before indexing, no trust of structure layout across the ABI, defensive handling of caller-owned strings. **Adversarial-input bounds at the FFI entry**: every input from the FFI side (`dlsym`'d return values, payload pointers from `process_json_line`, length fields from `process_frame_direct`, response strings, response payloads) must be bounds-checked against a documented maximum from `docs/architecture/PROTOCOL.md` § Limits before use — the Agda kernel checks bounds first (definitive), but the binding short-circuits oversized inputs at the FFI entry to avoid copying a payload that will be rejected. Overflow throws `aletheia::InputBoundExceededError` (or returns `std::unexpected<…>` where the API uses `std::expected`), never reads past the buffer, never relies on UB caught by an ASan run that is not in the standard CI lane. See Universal Rules → "Adversarial-input bounds at parser surfaces".
29. **File I/O & encoding** -- `std::ifstream`/`std::ofstream` opened in correct mode (binary for payloads, text for DBC/YAML), stream state checked after every read (`good()`/`fail()`), `std::locale::global` never mutated, locale-independent parsing for numbers, `std::filesystem::path` instead of string concatenation, explicit handling of multi-byte UTF-8 in DBC strings.

### Observability & Diagnostics (1)

30. **Logging discipline** -- `Logger` class usage matches Go `slog` and Python parity (same 16 event names, same field names), lazy formatting (no string construction unless logger present), log level discipline (DEBUG/INFO/WARN/ERROR matches actual severity), `std::println(stderr, ...)` reserved for documented startup warnings (rts_cores mismatch), no `std::cout`/`std::cerr` in library code outside documented warning paths, no eager concatenation in disabled log calls.

### Build & Packaging (2)

31. **ABI & compiler portability** -- targets **Clang 22 on Linux only** ([the supported toolchain](../docs/development/BUILDING.md#toolchain-support-policy)); any `__attribute__`/`[[gnu::...]]` extension or compiler builtin must be available under Clang 22; public headers use only C++23 features the toolchain's libstdc++/libc++ provides (`<expected>`, `<format>`); no reliance on undocumented layout of `std::` types; anonymous namespaces only in `.cpp` files, never in headers (ODR violations).
32. **Build reproducibility & CMake hygiene** -- `target_include_directories` uses `BUILD_INTERFACE`/`INSTALL_INTERFACE` correctly, no absolute paths baked into binaries, `__DATE__`/`__TIME__` not used, `target_link_libraries` scope (`PRIVATE`/`PUBLIC`/`INTERFACE`) intentional with no leaky `PUBLIC` on implementation-only deps, ctest targets isolated from each other (no shared temp files), FetchContent pinned to exact commits not floating branches, no global `add_definitions`.

### Dynamic Correctness Analysis (1)

33. **Dynamic correctness analysis (sanitizers, fuzzers, property-based, cross-binding integration)** -- four sub-lanes that each cover correctness surfaces unit tests cannot reach:
    - (a) **Sanitizer build matrix**: a separate CI lane builds with `-fsanitize=address,undefined` (ASan + UBSan) and runs the full ctest battery green; this is the standing UB gate that the regular Release build cannot replace. Add MSan if achievable on cgo-style boundaries; if the GHC RTS interferes with the sanitizer's instrumentation, document the gap in `docs/architecture/CGO_NOTES.md` rather than dismissing it. The ASan/UBSan lane catches lifetime, aliasing, and signed-overflow bugs that survive every other gate.
    - (b) **libFuzzer harnesses**: one fuzz target per binding-side parser (`fuzz_parse_response`, `fuzz_decode_binary_frame`, `fuzz_parse_dbc_json`, `fuzz_parse_rational_number`); seed corpus under `cpp/tests/fuzz/seed/<target>/`; CI runs each corpus as a 60s smoke plus a nightly extended lane (`-max_total_time=3600`). Fuzz targets compile under both Release and ASan to catch UB-on-fuzzed-input paths.
    - (c) **Property-based tests** via Catch2 generators (`GENERATE`, `GENERATE_REF`): round-trip properties for every wire-format encode/decode pair, parity invariants for `IBackend` defaults vs `FfiBackend` over generated inputs (the response field-set must agree). A binding-side data type without a round-trip property is a finding compounding cat 14 (b)/(c).
    - (d) **Cross-binding integration test**: mirror of Go cat 33d / Python cat 34d — one replay corpus across all three bindings produces identical sequences. Test lives at `cpp/tests/cross_binding_integration_tests.cpp`, opt-in via the same `cross_binding` build flag as the Go and Python entries so the three bindings exercise the same fixtures from one canonical corpus.

### Verification

```bash
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
cd cpp && ctest --test-dir build --schedule-random --output-on-failure
clang-format --dry-run -Werror include/aletheia/*.hpp src/*.cpp src/detail/*.hpp tests/*.cpp
clang-tidy -p build src/*.cpp
# Cat 33 dynamic-analysis lanes:
cd cpp && cmake -B build-asan -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer" -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address,undefined" && cmake --build build-asan && ctest --test-dir build-asan
cd cpp && cmake --build build --target fuzz_parse_response && ./build/tests/fuzz_parse_response -max_total_time=60 tests/fuzz/seed/parse_response/
cd cpp && cmake --build build --target cross_binding_integration_tests && ctest --test-dir build -R cross_binding
```

The `ctest` battery includes the Track D.1 doc-example harness
(`doc_example_tests`) — every ```cpp fence across `README.md`,
`docs/PITCH.md`, `docs/architecture/CANCELLATION.md`,
`docs/reference/INTERFACES.md`, and `docs/development/DISTRIBUTION.md`
is extracted, wrapped (3 shapes — full `int main()` / `#include` block
+ decls / body fragment with `using namespace aletheia` and
predeclared `client`/`backend`/`ts`/`can_id`/`dlc`/`data`/`frames`),
compiled by `${CMAKE_CXX_COMPILER}` (linked against
`$<TARGET_FILE:aletheia-cpp>` plus the static yaml-cpp / OpenXLSX
archives), and executed end-to-end. The companion structural gates
ban `<!-- cpp notest -->` annotations and enforce a `≥6` collective
fence floor — non-runnable fences must use the `text` info string,
mirroring the Python and Go ban. Adding a new user-facing markdown
file means adding it to `kDocFiles` in
`cpp/tests/doc_example_tests.cpp`. Skipped automatically when
`libaletheia-ffi.so` is missing (run `cabal run shake -- build` first).

---

