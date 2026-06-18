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
`memory/project_rust_parity_r1.md`) and frame construction (Slice R2 ✅ complete
2026-06-18, #57 — `build_frame`/`update_frame`/`send_frames` + mux extraction)**.
That is **26 of 40** `docs/FEATURE_MATRIX.yaml` rows `implemented` for the `rust`
column.

The remaining **14 `planned`** rows: **11** in this plan (slices **R3–R5**), and
**3** carved out to **Phase 6** (below).

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

## The slices (26 rows — R1's 11 + R2's 4 ✅ done; 11 remain in R3–R5)

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

Rows: `check_dsl`, `add_checks`, `yaml_check_loader`, `excel_check_loader`.

The fluent Check builder, runtime check attachment, and the YAML / Excel
loaders — the "engineers / CI / technicians" tiers above the raw LTL DSL.

- **Dependency:** R1 (the Check DSL references the typed DBC signal model) —
  confirm before starting.
- **Effort:** medium-large — the Excel loader likely pulls a Rust `.xlsx` crate
  as a *separate optional module*, mirroring Go's `go/excel/` split.

### Slice R4 — Ergonomics & runtime infra (5 rows)

Rows: `structured_logging`, `violation_enrichment`, `rts_cores_config`,
`cancellation_contract`, `lazy_streaming_batch`.

- `structured_logging` — a `tracing`/`log`-based event surface (the 16 event
  types matching Go `slog` / Python).
- `violation_enrichment` — client-side signal-value attachment on violations
  (the raw core `reason` is already surfaced).
- `rts_cores_config` — pass the RTS `-N` count through `hs_init` flags (today
  uses defaults).
- `cancellation_contract`, `lazy_streaming_batch` — **design call first.** These
  may resolve `not_applicable` once the idiomatic Rust form is chosen (a
  cancellation token / `Iterator`), exactly as C++ / Go marked some of these
  `not_applicable` because `std::stop_token` / `context.Context` / iterators
  already express the contract. The matrix can't pre-decide this; the slice does.
- **Effort:** medium; partly design-gated.

### Slice R5 — Test / DI seam (2 rows)

Rows: `backend_di_seam`, `mock_backend`.

A `trait`-based backend abstraction (Rust's analogue of Go's `Backend`
interface / C++'s `IBackend`) plus a test mock recording `<binary:OP>`
sentinels — matching the cross-binding mock-fidelity convention (the mock must
not fabricate wire shapes the real backend never emits). Enables testing the
client without loading the `.so`.

- **Dependency:** best after R1–R4 stabilize the client surface the trait abstracts.
- **Effort:** medium.

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

## References

- `docs/FEATURE_MATRIX.yaml` — authoritative `rust`-column status (the 26
  in-scope `planned` rows; the 3 Phase-6 rows note their deferral inline).
- [PARITY_PLAN.md](PARITY_PLAN.md) — cross-binding parity rules ("behavioral,
  not syntactic"; one row per capability).
- [PROJECT_STATUS.md](../../PROJECT_STATUS.md) § Phase 6 — the Rust binding's
  place in the whole-project roadmap.
