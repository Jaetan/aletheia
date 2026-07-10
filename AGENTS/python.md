## Python (34 categories)

Scope: ALL source files in `python/aletheia/`, test files in `python/tests/`, benchmark scripts in `python/benchmarks/`, the repo-root `conftest.py`, and developer tooling in `tools/`. The Python binding is the original and most mature. Review with the same rigor as Go and C++.

**Tooling gates (hard requirements):**
- `pylint` score must stay **10.00/10**. Any score drop is a blocking finding.
- `basedpyright` must produce **zero errors and zero warnings**. Any new diagnostic is a blocking finding.
- **Adding any suppression annotation** (`# type: ignore`, `# pylint: disable`, `# noqa`, `# pyright: ignore`) **requires user approval**. Propose the annotation with justification; do not add it without explicit permission.
- **`tools/` is in scope, same bar, no exceptions** (user directive 2026-05-26): every `tools/*.py` gate/helper script must reach pylint 10.00 / basedpyright 0/0/0 **by FIXING the code, never by suppressing or ignoring what the linters report**. The suppression rule above applies in full; for `tools/` the standing answer is fix-don't-suppress. Existing debt is NOT grandfathered — it gets fixed (remove any `# pylint: disable=...`, then fix the underlying issue), not waived. Worked example: the IWYU stack (`iwyu.py` / `_iwyu.py` / `_warm.py` / `warm_check_properties.py`) all sit at 10.00 / 0/0/0 with zero suppressions.

### Hygiene/Style (6)

1. **PEP 8 & formatting** -- consistent style, line lengths, import ordering
2. **Naming conventions** -- snake_case for functions/variables, PascalCase for classes, UPPER_CASE for constants, leading underscore for private
3. **Dead code** -- unused imports, unreachable branches, unused variables, commented-out code
4. **Comment/doc quality** -- Google-style docstrings on public API, explains "why" not "what", no stale comments
5. **Error message consistency** -- consistent format across client, CLI, loaders; actionable messages
6. **Module organization** -- each module has a single concern; no circular imports; private modules prefixed with underscore

### Type & Safety (4)

7. **Type annotation coverage** -- all public functions fully annotated; basedpyright strict mode clean; TypedDict/Protocol/Literal used correctly
8. **Strong type usage** -- sub-checks:
    - (a) **Domain types over primitives**: no bare `dict`/`list`/`Any` where a TypedDict, Protocol, or domain type exists; validated constructors over raw `int`/`str` at boundaries.
    - (b) **Tightness**: type hints must be as tight as the underlying value permits. basedpyright accepts any supertype (including `object`), so loose annotations silently pass the gate — reviewer must check that each annotation reflects the narrowest type the value can hold. If a third-party library produces a more specific type (e.g. `Fraction` over `float`, `Literal[0, 1, 2]` over `int`), use that; do not fall back to `object` just because it type-checks.
9. **Error handling** -- exceptions are specific (not bare `except`), raised with context, documented in docstrings; no silent swallowing
10. **Resource safety** -- ctypes handles cleaned up, file handles closed, context managers used where appropriate

### Correctness (4)

11. **Serialization fidelity** -- JSON output matches Agda protocol exactly (field names, types, structure, command strings)
12. **Parsing robustness** -- handles all response variants, all number formats (int/float/rational dict), error paths; no silent data loss. Response parsers must accept all status strings the Agda core can produce for the operations they serve
13. **FFI lifecycle** -- ctypes CDLL loading, hs_init ref-counting, string marshalling, GHC RTS constraints (never hs_exit)
14. **Test adequacy** -- sub-checks:
    - (a) **Baseline coverage**: public API, edge cases, negative paths, fixture reuse via `conftest`; `pytest -v` clean.
    - (b) **Mock fidelity**: for every operation, verify canned test responses use the same status strings, field set, and schema as the real FFI backend.
    - (c) **Cross-binding mock agreement**: all four binding mocks (Python canned responses, C++ `IBackend` defaults + `MockBackend`, Go `MockBackend`, Rust `MockBackend`) must agree for the same operation — a divergence between mocks is a finding regardless of which is "correct".
    - (d) **Real-vs-mock divergence testing**: for operations where the mock response differs from the real FFI, there must be a test that exercises the real FFI format via the real `.so` integration tests. A mock chosen for convenience rather than fidelity is a finding.
    - (e) **Regression test discipline**: every bug fix must be accompanied by a test that fails without the fix and passes with it. A fix landed without a guarding test re-opens the regression surface the next time the file is refactored.
    - (f) **Test isolation**: `pytest --random-order --random-order-bucket=package` (plugin pinned in dev deps) must pass — order-dependent flakes (shared tempdir, module-import side effects, fixture leakage between tests, `os.environ` mutation outside `monkeypatch`, ctypes handle retained between tests) are findings. Each test must clean up via `tmp_path` fixtures, register cleanup via fixture teardown or `addfinalizer`, and never mutate global state without a paired restore. The `--random-order` lane runs in CI alongside the deterministic lane; both must be green.
    - (g) **Mutation testing**: `mutmut` (or `cosmic-ray`) on hot-path modules (`client/_client.py`, `dbc/_converter.py`, `yaml_loader.py`, `codes/_issue.py`, `types.py` — the `[tool.mutmut] source_paths` set) — surviving mutants on operational logic are findings. Justify any survivor with a comment block at the source site; an unjustified survivor is a test gap. Mutation testing runs as a separate CI lane (cost is high) — once per PR is sufficient.

### Architecture (4)

15. **API ergonomics** -- Pythonic API (context managers, keyword args, sensible defaults), pit of success. Import path: the top-level `aletheia` package is the single canonical public surface -- cross-cutting names (client, the exception hierarchy) flat there; domain interfaces in cohesive sub-namespaces (`aletheia.dbc` / `aletheia.dsl` / `aletheia.codes` / `aletheia.types` / the loaders)
16. **Package boundaries** -- clean separation between client, DSL, checks, loaders, CLI. Every public submodule declares `__all__`; internal modules are `_`-prefixed and are never a supported public import path (e.g. `aletheia.client` is internal — its surface is re-exported only from the top-level package)
17. **Extensibility** -- adding new predicates, loaders, or check types doesn't break existing callers
18. **Dependency discipline** -- minimal external deps; openpyxl/python-can/pyyaml justified; no unnecessary additions

### Specification/Design (4)

19. **Domain model fidelity** -- do the types and abstractions faithfully represent the CAN/DBC/LTL domain? Are there gaps?
20. **Design coherence** -- are the right things grouped together? Are abstractions justified or gratuitous? Is coupling minimized?
21. **Use-case coverage** -- does the API serve its intended users well? Are there missing capabilities or workflows harder than they should be?
22. **Cross-layer alignment** -- does the Python binding correctly mirror the Agda core's semantics? All bindings (Python, C++, Go, Rust) must have identical behavior -- any divergence is a finding. **Response contract audit**: for every client method, trace the response lifecycle: (a) what status strings can the Agda core return for this operation? (b) does the binding's parser accept all of them? (c) does the client method actually call the parser? **Python is the reference implementation**: when reviewing Python, check whether the C++/Go bindings match Python's response handling for each operation. Python's `_ACK_BYTES` fast path in `send_error`/`send_remote` is the gold standard for event response handling — the other bindings must match it. **Concrete cross-binding comparison**: for each of the 13 backend operations, compare what Python, C++, Go, and Rust do with the response. Any behavioral divergence is a finding

### Concurrency & Performance (3)

23. **Concurrency & GIL discipline** -- ctypes calls release the GIL, so concurrent `AletheiaClient` instances on distinct state pointers are legal but must not share mutable Python state without a lock. Flag shared `threading.Lock`/`RLock` missing on cross-thread mutable state, `hs_init` ref-counting races, per-thread state pointers held across threads, and any assumption that `hs_init` is called more than once per process.
24. **Mutability & aliasing hazards** -- default mutable arguments (`def f(x=[])`), shared list/dict aliasing across instances, `dataclass` without `frozen=True` where immutability is intended, `.copy()` vs `copy.deepcopy` at API boundaries, mutation of internal caches (`_signal_cache`, DSL state) during iteration.
25. **Hot-path performance** -- `json.dumps(..., sort_keys=True)` inside per-frame loops, unnecessary `ctypes.cast` round-trips, eager f-string formatting in `logger.debug(f"...")` (use `%`-style lazy args), `list()` materialization of generators used only for iteration, repeated attribute lookups inside tight loops. **Long-run stability**: a stability benchmark of ≥ 1M frames must not exceed the proven O(1) per-frame bound (no unbounded Python dict growth, no `ctypes` handle leaks, no logger-handler accretion across reconfigurations). Per-frame throughput must stay within the variance band of the short-run benchmark. A run that degrades over time is a hot-path finding even if the short bench passes. **Long-run resource leakage sub-checks**: the stability bench captures (a) RSS via `psutil.Process().memory_info().rss` start vs end (after explicit `gc.collect()`); (b) FD count via `psutil.Process().num_fds()` on Linux (`num_handles()` on Windows); (c) ctypes handle accounting — no `cdll.LoadLibrary` accumulation across iterations, no `c_void_p` retained past `Client.close()`; (d) logger-handler count via `len(logging.getLogger().handlers)` start vs end (a logger-handler accreted across `dictConfig` reconfigurations is a leak even if RSS is stable). Drift on any sub-check is a finding.

### Security & I/O (2)

26. **Security / input sanitisation** -- `yaml.safe_load` (not `yaml.load`), no `pickle` on untrusted input, `subprocess` without `shell=True`, file path traversal from untrusted DBC/log inputs, XML entity expansion safety, credential leakage in logs. **Adversarial-input bounds at user-data entrypoints**: every entrypoint that accepts user-supplied data — `load_dbc`, `load_checks`, `load_checks_from_excel`, `load_dbc_from_excel`, `dbc_to_json`, `iter_can_log`, `Client.send_frame*` payloads — must enforce documented bounds from `docs/architecture/PROTOCOL.md` § Limits before invoking the parser: max file size (via `pathlib.Path.stat().st_size` pre-check), max identifier length, max list cardinality (signals/messages/attributes per file), max nesting depth for JSON-shaped inputs (validated via a recursive-descent depth counter, not a stack-overflow trampoline). Overflow raises `aletheia.InputBoundExceededError` (a domain-specific exception type carrying the field name and limit), never relies on the FFI parser to OOM and never trusts cantools / openpyxl / pyyaml to bound the input. See Universal Rules → "Adversarial-input bounds at parser surfaces".
27. **File I/O & encoding** -- `open()` must pass explicit `encoding=` (prefer `"utf-8"`), `pathlib.Path` used consistently rather than `os.path` string concatenation, resource loading via `importlib.resources` rather than `__file__`-relative paths, newline handling on text files, binary mode for non-text payloads.

### Observability & Diagnostics (2)

28. **Logging discipline** -- structured logging parity with Go `slog`, C++ `Logger`, and the Rust binding logger (the shared event set — count in `docs/LOG_EVENTS.yaml` — same fields); lazy log message formatting (`%`-style, not f-strings); `exc_info=True` on error paths; level usage matches severity (DEBUG/INFO/WARNING/ERROR); no `print()` in library code. Any helper that wraps `logger.log(...)` on a hot path MUST check `logger.isEnabledFor(level)` and early-return before building `extra` dicts / f-strings — an earlier `log_event` missed this and regressed Python Stream LTL by −16.1% until `1e40b4d` restored the guard.
29. **Exception chaining & context** -- `raise X from Y` to preserve `__cause__`, never `except ... as e: raise RuntimeError(str(e))` (loses traceback), no bare `except:` (use `except Exception:` minimum), re-raises preserve original context, error messages are actionable.

### Packaging & Reproducibility (3)

30. **Determinism & reproducibility** -- no reliance on `dict`/`set` iteration order where output is user-visible, stable sort keys, no timestamp-dependent output in library code, explicit `random.Random(seed)` rather than module-level `random`, no `datetime.now()` in serialization paths.
31. **Packaging hygiene** -- `pyproject.toml` version pin policy (minimum versions, not exact pins for library code), entry points declared correctly, optional dependency groups (`[project.optional-dependencies]`), wheel/sdist symmetry, `[tool.*]` section consistency (pylint, basedpyright, pytest all configured here).
32. **Doctest & example validity** -- docstring `>>>` examples actually run (`pytest --doctest-modules`), README snippets type-check and execute, tutorial code in `docs/` stays in sync with the actual API, no stale imports or removed symbols in examples. **Doc-example harness (runtime gate)**: every ```python fence across the user-facing docs (`README.md`, `docs/PITCH.md`, `docs/guides/{QUICKSTART,COOKBOOK}.md`, `docs/reference/{CLI,PYTHON_API,INTERFACES}.md`, `docs/architecture/{CANCELLATION,DESIGN,PROTOCOL}.md`, `python/README.md`, `examples/README.md`) must execute end-to-end under `pytest --markdown-docs` against the real FFI. The repo-root `conftest.py` injects globals (pre-built `dbc`, entered `client`, loader fakes for `dbc_to_json`/`iter_can_log`/`load_checks`/`load_checks_from_excel`/`load_dbc_from_excel`/`create_template`) so doc prose stays readable while still exercising live code. Fence tagging conventions: use ```text (not ```python) for pseudo-signatures, JSON return-value shapes, and class-body-shape sketches; use ```python continuation for fences that chain onto a prior runnable fence's namespace; never use ```python notest (the structural gate test `python/tests/test_doc_examples_harness.py` rejects this tag so the "skipped" state is unambiguous). **Structural gate (static)**: `python/tests/test_doc_examples_harness.py` parametrises over the doc-file list above and fails on any `python notest` fence — this runs inside the default `pytest tests/` battery. **Runtime gate (executes the fences)**: the markdown-docs invocation below exercises every live `python` fence against the real FFI. Both cross-binding mirrors are in place: Go via `go/aletheia/doc_examples_test.go` (2026-05-04 — see Go § Verification) and C++ via `cpp/tests/doc_example_tests.cpp` (2026-05-04 — see C++ § Verification).

### Command-line Interface (1)

33. **Command-line interface quality** -- argparse wiring on every CLI subcommand: every flag/positional has a non-empty `help=` string, every subcommand has a one-line description visible from `--help`, mutually exclusive flags are grouped (`add_mutually_exclusive_group`), required arguments are validated at parse time not at use site. Exit codes follow Unix convention: `0` success, `1` generic failure, `2` argument/usage error (`argparse` default), distinct non-zero codes for distinct failure classes (parse error vs runtime error vs I/O error). Stderr/stdout discipline: diagnostic messages (warnings, errors, progress) go to stderr; primary output (parsed JSON, validation results, query responses) goes to stdout so downstream tools can pipe the output. No `print()` of progress to stdout. Argument validation happens before any FFI/I/O side effect — parse and type-check all flags before opening the shared library or any file. Tab-completion (argcomplete) is optional but if present must stay in sync with the `add_argument` declarations; stale completion specs are a finding.

### Dynamic Correctness Analysis (1)

34. **Dynamic correctness analysis (sanitizers, fuzzers, property-based, cross-binding integration)** -- four sub-lanes that each cover correctness surfaces unit tests cannot reach:
    - (a) **`python -X dev` mode**: a CI lane runs `python -X dev -m pytest tests/` in addition to the standard lane — `dev` mode enables `ResourceWarning` (catches unclosed file/socket/ctypes handles), debug `asyncio` (catches unawaited coroutines), and surfaces deprecation warnings as visible output. Findings under `dev` mode that pass the standard lane are findings, not noise — they are real bugs the standard lane silently masks.
    - (b) **`hypothesis`-driven property tests**: one strategy per wire-format encode/decode pair (`hyp_test_response_roundtrip`, `hyp_test_dbc_to_json_roundtrip`, `hyp_test_command_marshal_roundtrip`, `hyp_test_rational_number_roundtrip`); strategies pinned in `python/tests/conftest.py` via `@hypothesis.strategies.composite`. Hypothesis profile pinned for CI (`max_examples=200`, deterministic seed) and developer (`max_examples=20`, statistically-shrunk failures). A binding-side parser without a hypothesis property is a finding compounding cat 14 (b)/(c).
    - (c) **`atheris` fuzz harnesses**: one entry per binding-side parser (`fuzz_parse_response.py`, `fuzz_dbc_to_json.py`, `fuzz_iter_can_log.py`); seed corpus under `python/tests/fuzz/seed/<target>/`. Atheris dependency is opt-in (`[project.optional-dependencies]` group `fuzz`). CI runs each corpus as a 60s smoke plus a nightly extended lane.
    - (d) **Cross-binding integration test**: mirror of Go cat 33d / C++ cat 33d — one replay corpus across all three bindings produces identical sequences. Test lives at `python/tests/test_cross_binding_integration.py`, opt-in via `pytest -m cross_binding`. Python is the reference implementation per cross-layer alignment guidance — when the three bindings diverge on a sequence, Python's behavior is the baseline against which Go and C++ are reconciled (per `feedback_cross_language_parity.md`).

### Verification

```bash
cd python && python3 -m pytest tests/ -v
cd python && python3 -X dev -m pytest tests/ -v
cd python && python3 -m pytest tests/ --random-order --random-order-bucket=package
cd python && basedpyright aletheia/ benchmarks/  # benchmarks/ joined the gate 2026-05-09 per feedback_no_subsumption_asymmetry
cd python && pylint aletheia/
cd python && pylint tests/ ../conftest.py  # same 10.00/10 gate applies (feedback_pylint_10_mandatory); conftest.py lives at repo root
cd python && pylint benchmarks/  # same 10.00/10 gate applies; benchmarks/ joined the gate 2026-05-09 per feedback_no_subsumption_asymmetry
pylint tools/ && basedpyright tools/  # tools/*.py — same 10.00 / 0/0/0 gate, fix-don't-suppress (user directive 2026-05-26); run from repo root
# Cat 32 doc-example harness — runs every ``python`` fence across the
# user-facing docs against the real FFI. Must be run from the repo root
# so pytest picks up the repo-root ``conftest.py`` (which provides the
# harness globals and loader fakes) instead of the ``python/pyproject.toml``
# rootdir that the ``cd python`` commands above use.
cd "$(git rev-parse --show-toplevel)" && python3 -m pytest --markdown-docs \
  --rootdir="$(pwd)" \
  README.md docs/PITCH.md \
  docs/guides/QUICKSTART.md docs/guides/COOKBOOK.md \
  docs/reference/CLI.md docs/reference/PYTHON_API.md docs/reference/INTERFACES.md \
  docs/architecture/CANCELLATION.md docs/architecture/DESIGN.md docs/architecture/PROTOCOL.md \
  python/README.md examples/README.md
```

---

