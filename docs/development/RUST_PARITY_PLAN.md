# Rust Binding — Parity Plan

> **Terminology — read first.** The work below is organized into **slices** —
> the project's established term for incremental Rust-binding deliverables
> ("tracer-bullet slice", "a later Rust slice"). They are deliberately **not**
> called "phases": the word *Phase* (capital P) is reserved for whole-project
> phases (Phase 1 … Phase 6 — see [PROJECT_STATUS.md](../../PROJECT_STATUS.md)).
> Calling a sub-plan's units "phases" conflates them with project phases and
> causes confusion. See [CLAUDE.md § Key terms](../../CLAUDE.md).

## Where the binding stands

The Rust binding (`rust/`, shipped 2026-06-14, PR C) covers the **streaming
verification hot path**: validated value types (`CanId` / `Dlc` / `Rational` /
`Timestamp` / `TimeBound`), native `Predicate` / `Formula` enums serializing to
the core's exact wire shape, DBC text parse, property binding, binary-FFI frame
streaming, signal extraction, and send-error / send-remote — **plus the full
typed DBC document model (Slice R1 ✅ complete 2026-06-17, PRs #53/#54/#55; see
`memory/project_rust_parity_r1.md`), frame construction (Slice R2 ✅ complete
2026-06-18, #57 — `build_frame`/`update_frame`/`send_frames` + mux extraction),
the fluent check DSL (Slice R3a ✅ complete 2026-06-18, #59 —
`check::signal`/`check::when` → LTL formulas + `Client::add_checks`), and the
YAML check loader (Slice R3b ✅ complete 2026-06-18, #62 —
`load_checks_from_yaml`, schema-portable with the peers, with the shared
`Rational::from_f64` convention + trust-boundary hardening), and the Excel
check + DBC loader (Slice R3c ✅ complete 2026-06-19, #65 — the separate
`aletheia-excel` crate, which also unified strict, by-name Excel column handling
across all four bindings)**.
**Slice R4 (ergonomics & runtime infra) is also complete** (R4a #67 — structured
logging + RTS-cores config, `lazy_streaming_batch`→`not_applicable`; R4b #68 —
client-side violation enrichment; R4c #69 — runtime-agnostic `AsyncClient`,
cancellation = drop the future).
That is **36 of 40** `docs/FEATURE_MATRIX.yaml` rows `implemented` for the `rust`
column (+ 1 `not_applicable`, `lazy_streaming_batch`) — **Slices R1–R5 complete;
the in-plan slices are done.**

The remaining **3 `planned`** rows are all carved out to **Phase 6** (below);
none remain in this plan.

## Out of scope — deferred to Phase 6 (with the python-can replacement)

Per user decision (2026-06-14), these ride with the broader Phase 6
host-surface / python-can work, **not** this plan — handled when the
`can_logger` is removed from Python:

- **`can_log_reader`** — the python-can replacement; unbuilt in *every* binding
  (needs verified Agda log-format parsers per
  `feedback_parsers_are_agda_with_proof`). This is the timing anchor for the
  other two.
- **`cli`** — the Rust host CLI (Python / C++ / Go already ship one).
- **`doc_example_gate_checks`** — the Rust doc-example gate.

## The slices (26 rows — R1's 11 + R2's 4 + R3a's 2 + R3b's 1 + R3c's 1 + R4's 5 + R5's 2 = 26 ✅ all done)

### Slice R1 — Typed DBC document model (keystone, 11 rows) — ✅ DONE 2026-06-17 (#53/#54/#55)

Rows: `parse_dbc_json`, `validate_dbc`, `format_dbc`, `dbc_text_format`,
`dbc_metadata_tier1`, `dbc_metadata_tier2`, `dbc_signal_receivers`,
`dbc_signal_value_descriptions`, `dbc_message_senders`, `dbc_queries_mux`,
`dbc_lookup`.

Build a typed `Dbc` / `DbcMessage` / `DbcSignal` document family — the Rust
analogue of Python `DbcDefinition`, C++ `DbcDefinition`, Go `DBCDefinition` —
(de)serialized from the core's canonical JSON. Then layer the operations that
need it: `parse_dbc` (JSON input), `validate_dbc`, `format_dbc`,
`format_dbc_text` (DBC struct → `.dbc` text), the Tier-1 / Tier-2 / receivers /
value-description / sender metadata accessors, and the mux / lookup queries.

- **Dependency:** none — foundational.
- **Why first:** single highest-leverage block (38% of the gap); R3 leans on it.
- **Effort:** large — the struct family + serde mapping + ~11 client methods +
  per-row matrix flips + roundtrip tests against the shared `dbc_corpus`.

### Slice R2 — Frame construction / binary endpoints (4 rows) — ✅ DONE 2026-06-18 (#57)

Rows: `build_frame` (`build_frame_bin`), `update_frame` (`update_frame_bin`),
`mux_extraction`, `batch_frame_send`.

Wire the binary build / update FFI (`aletheia_build_frame_bin` /
`aletheia_update_frame_bin`) — encoding signals *into* frames, the reverse of
the extraction path already done — plus multiplexed extraction and batched send.

- **Dependency:** none (independent of R1; could run in parallel).
- **Effort:** medium — FFI signatures + `SignalInjection`-style input + tests.

### Slice R3 — Higher-level Check interface tier (4 rows)

Rows: `check_dsl`, `add_checks` (**R3a ✅ done 2026-06-18, #59**),
`yaml_check_loader` (**R3b ✅ done 2026-06-18, #62**), `excel_check_loader`
(**R3c ✅ done 2026-06-19, #65**). **Slice R3 complete.**

The fluent Check builder, runtime check attachment, and the YAML / Excel
loaders — the "engineers / CI / technicians" tiers above the raw LTL DSL.

- **R3a ✅ (#59)** — `rust/src/check.rs`: fluent `check::signal`/`check::when`
  builders compiling domain checks to LTL `Formula`s + display metadata
  (`Check` with name/severity/condition), bound by `Client::add_checks`. Same
  features as the Go/Python check builders, presented the idiomatic Rust way
  (`impl Into<Rational>` + `From<i64>`, `u64` ms so negative time is
  unrepresentable, `Result` range/overflow guards); raw LTL combinators stay on
  `Formula`. `settles_between → MetricAlways` (= Go `AlwaysWithin` = Python
  `for_at_least`, verified). Flips `check_dsl` / `add_checks`.
- **R3b ✅ (#62)** — `rust/src/yaml.rs`: `load_checks_from_yaml` /
  `load_checks_from_yaml_file` behind a **default-on** `yaml` cargo feature
  (default-on so the plain `cargo test` lane exercises it + matches the peers'
  built-in YAML; opt out via `--no-default-features`). Schema matches Python
  `load_checks` / Go `LoadChecksFromYAML`, proven by a test loading the shared
  `go/aletheia/testdata/doc_examples/checks.yaml` fixture. New `Rational::from_f64`
  replicates the shared `round(v×10⁹),10⁹` convention (gcd-reduced; NaN/Inf/overflow
  → `Err`). Trust-boundary hardening (64 MiB cap + symlink/non-regular rejection)
  mirrors the peers. Flips `yaml_check_loader`.
- **R3c ✅ (#65)** — `rust/excel/`: a *separate optional crate* (`aletheia-excel`)
  mirroring Go's `go/excel/` split — `load_checks_from_excel`,
  `load_dbc_from_excel`, `create_template` (calamine read + rust_xlsxwriter + zip).
  The `feature_matrix` gate now resolves a single-colon `pkg:symbol` entry against
  `rust/<pkg>/src`. Beyond the Rust slice, a design review unified **Excel column
  handling across all four bindings**: lookup by header name, all columns read, an
  absent column ≡ an empty cell, and **strict coercion** — a number stored as
  *text* is rejected for a numeric field (BREAKING for Go/C++, previously lenient;
  `Extended`/mux/`Unit` now optional everywhere). Each binding gained a gated
  demo-workbook DBC test + a number-as-text rejection test. Flips
  `excel_check_loader`.
- **Dependency:** R1 (the Check DSL references the typed DBC signal model) —
  confirmed (R3a built on it).

### Slice R4 — Ergonomics & runtime infra (5 rows) — ✅ DONE 2026-06-19 (#67/#68/#69)

Rows: `structured_logging`, `violation_enrichment`, `rts_cores_config`,
`cancellation_contract`, `lazy_streaming_batch`.

- `structured_logging` ✅ (#67) — a callback `Logger` trait (level + event + typed
  fields) over the shared 16-event vocabulary (`docs/LOG_EVENTS.yaml`), injected
  via `ClientBuilder::logger()` with `.min_level()` filtering; chosen over a
  `tracing`/`log` facade so the event set is enforced by a parity gate
  (`rust/tests/log_events.rs`) exactly like the Go/Python peers.
- `violation_enrichment` ✅ (#68) — client-side signal-value attachment on
  violations: a per-property diagnostic cache (referenced signals + a formula
  description) plus last-known values → `Enrichment.enriched_reason`, mirroring
  Go `enrich.go` / Python `_enrichment.py` (the core emits only the raw reason).
- `rts_cores_config` ✅ (#67) — `ClientBuilder::rts_cores(k)` passes `+RTS -N<k>`
  through `hs_init`; the RTS is process-global, so the first client latches the
  count (a later mismatch is a no-op + `rts.cores_mismatch` warning).
- `cancellation_contract` ✅ (#69) — resolved **`implemented`**, not
  `not_applicable`: the idiomatic Rust form is **dropping a future**, expressed by
  the opt-in `AsyncClient` (feature `async`). The `!Send` sync `Client` is owned by
  a dedicated worker thread; a queued job is skipped via the reply
  `oneshot::Sender::is_canceled()` and an in-flight FFI call commits its prefix —
  honoring `CANCELLATION.md` (now
  with a Rust §2.4/§3.4). Runtime-agnostic (futures-channel oneshot); `Send + Sync`.
- `lazy_streaming_batch` ✅ (#67) — resolved **`not_applicable`**: `send_frames`
  already delivers commit-prefix-and-report; a lazy iterator variant is additive,
  the same call made by the Go/C++ peers.
- **Effort:** medium; partly design-gated. (Done.)

### Slice R5 — Test / DI seam (2 rows) — ✅ DONE

Rows: `backend_di_seam`, `mock_backend`.

A public, open `trait Backend` (`rust/src/backend.rs`) — Rust's analogue of Go's
`Backend` interface / C++'s `IBackend` — plus a public, `Clone`-able
`MockBackend` (`rust/src/mock.rs`) recording the cross-binding `<binary:OP>`
sentinels (the mock must not fabricate wire shapes the real backend never
emits). The `Client` holds a `Box<dyn Backend>`, injected via
`Client::with_backend` / `ClientBuilder::build_with_backend`, so the client can
be unit-tested without loading the `.so` (`rust/tests/mock_backend.rs`).

**Idiomatic divergences** (same features, Rust form — per the user's
"parity, each language its own way"):
- **RAII, not handle-threading.** The peer seams put `init`/`close`/`state` in
  the interface and thread a raw `void* state` through every method. Rust drops
  all three: the production `FfiBackend` owns its session handle and closes it in
  `Drop`, so the trait never traffics in a raw pointer and a double needs no fake
  handle. (One backend owns one session; multiple sessions = multiple clients.)
- **Shared-state mock.** `MockBackend` wraps `Rc<RefCell<…>>` and is `Clone`, so
  a test keeps one clone to assert on (`captured()`) while the `Client` owns
  another — Rust's equivalent of the peers keeping a pointer to the injected mock.
- **Errors on queue exhaustion** (matching Go), rather than synthesising a
  default `ack`/`success` (Python/C++) — the no-surprise, `Result`-returning
  contract avoids fabricated mock behavior.
- **Terminal injection.** Injection is `ClientBuilder::build_with_backend(self,
  backend)` (not a stored field), keeping `ClientBuilder: Send` so the async
  client can still move the builder onto its worker thread.

- **Dependency:** best after R1–R4 stabilize the client surface the trait abstracts.
- **Effort:** medium. **Done.**

## Suggested order

`R1 → R2 → R3 → R4 → R5`. R1 first (keystone); R2 is independent and can
parallel R1; R5 last (it abstracts the surface the earlier slices build).

## Per-slice exit criteria

Each slice: flip its matrix rows to `implemented` (the `entry` resolving under
the `rust/tests/feature_matrix.rs` gate); `cargo test` + `cargo fmt --check` +
`cargo clippy -- -D warnings` green; a `CHANGELOG.md` entry for new public
surface (per AGENTS.md § Public API stability); and the four FEATURE_MATRIX
parity gates passing. Any row that resolves `not_applicable` records a reason
(matrix schema requirement) rather than being silently skipped.

## On reaching parity — thorough Rust review (owed)

**User-requested 2026-06-19:** once the Rust binding reaches feature parity with
the other API languages, conduct a **thorough review of the entire Rust binding**
(`rust/` + the `rust/excel/` crate) — a full code review in the spirit of the
Agda / cross-language review rounds, not a per-slice spot check.

**Trigger (milestone, not dated): R5 merged** — the last in-plan slice. R5 is
now ✅ done: the in-plan slices are complete at **36 `implemented` +
1 `not_applicable`** (`lazy_streaming_batch`), i.e. all 37 non-Phase-6 rows
resolved. The Rust binding now has functional parity with Python / Go / C++, so
**this review is due** once R5 merges. The three remaining `planned` rows (`cli`,
`can_log_reader`, `doc_example_gate_checks`) are the shared **Phase-6**
host-surface track (`can_log_reader` is unbuilt in *every* binding), so they need
not gate the review — though it should note them as the known remaining deltas,
and fold any `cli` / doc-gate work into scope if it has landed by then. The
trigger is the R5 merge, not a row count, so number-drift can't mis-fire it.
**Re-confirm the scope with the user before starting it.**

## References

- `docs/FEATURE_MATRIX.yaml` — authoritative `rust`-column status (the 26
  in-scope rows across slices R1–R5; the 3 Phase-6 rows note their deferral inline).
- [PARITY_PLAN.md](PARITY_PLAN.md) — cross-binding parity rules ("behavioral,
  not syntactic"; one row per capability).
- [PROJECT_STATUS.md](../../PROJECT_STATUS.md) § Phase 6 — the Rust binding's
  place in the whole-project roadmap.
