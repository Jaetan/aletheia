# Cross-Binding Parity Plan

> **Status:** Active. Locked 2026-04-20 as the post-R17 roadmap.
> **Scope:** Make Python / C++ / Go bindings expose the same user-facing capabilities, enforce it mechanically.

## Goal

All three bindings expose the same complete set of user-facing capabilities, expressed idiomatically per language. **Parity means behavioral equivalence, not identical API shapes.** Python `async def`, Go `func(ctx context.Context, ...)`, and C++ `std::stop_token` can all express the same cancellation contract — that is parity.

Cross-language divergence is a bug per `feedback_cross_language_parity.md`. This plan is the mechanism that stops drift from happening by accident.

## Approach — Three Parts

1. **Language-agnostic logic → Agda core.** DBC text parsing, DBC metadata, mux queries live in the verified kernel and flow to every binding via the JSON protocol. One implementation, three surfaces.
2. **Language-native ergonomics.** Cancellation, streaming iteration, async composition: idiomatic per language, behaviorally equivalent (same cancel semantics, same partial-commit rules, same error surface).
3. **Declarative feature matrix + structural gates.** `docs/FEATURE_MATRIX.yaml` is the single source of truth for what parity means. Each binding has a structural test that reads it and fails when its surface drifts.

## Locked Decisions (2026-04-20)

| | Decision |
|---|---|
| **A.1 Matrix source** | YAML as authoritative; markdown generated for reading. |
| **B.3 DBC parser scope** | Full cantools equivalence. User DBCs are unknown; minimal-subset risks silent rejection. |
| **B.3 cantools removal** | Drop the Python dep as soon as B.3 reaches equivalence (B.3.g). |
| **C.0 Cancellation SSOT** | Needs its own review round — including whether the doc should exist at all. |
| **API shape** | Idiomatic per language; cross-binding identity is behavioral, not syntactic. |

## Matrix Granularity Rule

**One row per user-facing capability, not per method.** "Load a DBC file" is a row. `cpp::load_dbc`, `go.LoadDBC`, `aletheia.load_dbc` are all entries on the same row. If the three bindings for a row fit on one line, the granularity is right.

**`not_applicable` requires `reason`.** A binding cell with `status: not_applicable` MUST carry a non-empty `reason` string. The structural test fails if either is missing. The canonical `not_applicable` example is CLI: C++ and Go are library bindings; a CLI is a host-application concern.

## Phases

### Phase A — Feature Matrix + Structural Gates

Sets the rules of the game. No Part 1 or Part 2 work lands without a matching matrix row.

- **A.1** Draft `docs/FEATURE_MATRIX.yaml` schema. Fields per row: `id`, `name`, `description`, optional `related` (for tracking items like R17-DEF-4), and `bindings.{python,cpp,go}.{status, entry?, reason?, notes?}`.
- **A.2** Seed with currently-shipped capabilities (~15 rows — RTS cores, structured logging, Check DSL, YAML/Excel check loaders, YAML DBC loader, batch frame send, core streaming, CAN-FD, Python-only DBC text parse, mux extraction, violation enrichment, validation errors, custom logger backend, MockBackend). Then add `planned` rows for every R17-DEF and pre-R17 backlog item.
- **A.3** Python structural test first (`python/tests/test_feature_matrix_parity.py`). Pass on the seeded matrix before mirroring.
- **A.4** Go structural test (`go/aletheia/feature_matrix_test.go`); uses `gopkg.in/yaml.v3`.
- **A.5** C++ structural test (`cpp/tests/test_feature_matrix_parity.cpp`); uses `yaml-cpp` (already a dep).
- **A.6** Wire all three into the default test battery. Cat 32 contract: absence = CI failure.

**Deliverable:** matrix plus three tests, all green on current code. After this, any new feature requires a matrix row or the gate fails.

### Phase B — Agda-Core Migrations (Part 1)

#### B.1 — DBC Metadata Exposure (Tier 1, R17-DEF-2)

Low risk; data is already preserved in the Agda core, just dropped at the FFI boundary. Scope of B.1 is strictly **Tier 1** — the three arrays that exist on `Aletheia.DBC.Types.DBC` and round-trip through `Formatter`/`JSONParser` today (`signalGroups`, `environmentVars`, `valueTables`). Fields that do not exist in the Agda core (nodes, comments, attributes, signal receivers) are carved out as **B.1.x** below.

- B.1.a Audit — **complete 2026-04-20.** Tier 1 fields: Agda core ✓, formatter ✓, optional-array parser ✓; dropped in `dbc_converter.dbc_to_json` and in `DbcDefinition` for all three bindings. Tier 2 fields: not in core.
- B.1.b Python `DBCDefinition` TypedDict — add `signalGroups`, `environmentVars`, `valueTables` as `NotRequired` entries plus supporting row TypedDicts (`DBCSignalGroup`, `DBCEnvironmentVar`, `DBCValueTable`).
- B.1.c `dbc_to_json` — populate the three arrays from cantools (`db.signal_groups`, `db.environment_variables`, `db.dbc.value_tables`). Preserve empty-list semantics when cantools has nothing.
- B.1.d Go `DbcDefinition` struct — add matching fields + row types.
- B.1.e C++ `DbcDefinition` struct — add matching fields + row types.
- B.1.f Roundtrip test: fully-loaded DBC → JSON → reparse → byte-identical (lives per-binding alongside existing DBC suites).
- B.1.g Update `docs/FEATURE_MATRIX.yaml`: add row `dbc_metadata_tier1` covering the three arrays. Mark all three bindings `implemented` once B.1.b–f land.

**Estimate:** 2–3 days. **Matrix row:** `dbc_metadata_tier1`.

#### B.1.x — DBC Metadata Tier 2 (nodes, comments, attributes, receivers)

Adds DBC fields that the Agda core does not currently carry. Heavier than B.1 because every step touches the verified kernel.

- B.1.x.a Extend `Aletheia.DBC.Types.DBC` with `nodes : List Node`, `comments : List DBCComment` (node/message/signal-scoped), `attributes : List DBCAttribute` (including `BA_DEF_`, `BA_DEF_DEF_`, `BA_`, and the rel variants). Extend `DBCSignal`/`DBCMessage` with `receivers : List String`.
- B.1.x.b Update `JSONParser.agda` (optional-array parsing for the new fields, strict for `receivers` on existing rows).
- B.1.x.c Update `Formatter.agda` and its roundtrip properties (`Formatter/Properties.agda`, `MessageRoundtrip.agda`, `SignalRoundtrip.agda`). Every new field needs its roundtrip proof closed before binding work starts.
- B.1.x.d Validator updates — attribute-name uniqueness, comment target existence, node reference integrity in message sender/receivers.
- B.1.x.e Widen the three binding structs + `dbc_to_json` the same way B.1 did for Tier 1.
- B.1.x.f Cross-binding roundtrip: fully-loaded DBC with every Tier 2 field → identical `DbcDefinition` across all three.
- B.1.x.g Update `docs/FEATURE_MATRIX.yaml`: either add row `dbc_metadata_tier2` or promote `dbc_metadata_tier1` → `dbc_metadata_full` when both tiers land.

**Estimate:** 1 week (Agda + proofs dominate; binding work mirrors B.1 once the core settles). **Matrix row:** `dbc_metadata_tier2`. Scheduled immediately after B.1, before B.2.

#### B.2 — Mux Query Helpers (R8, from `project_go_features_to_explore.md`)

Read-only query API over in-memory DBC. Agda already handles mux.

- B.2.a Locate mux logic in Agda; define the query surface (signals present for a mux value; mux relationship graph).
- B.2.b Add JSON protocol command.
- B.2.c Python method on `AletheiaClient`.
- B.2.d Go method on `Client`.
- B.2.e C++ method on `Client`.
- B.2.f Parity test: same DBC + mux value → same signal set across all three.

**Estimate:** 2–3 days. **Matrix row:** `mux_query`.

#### B.3 — DBC Text Parser in Agda (R17-DEF-4) — Heaviest Item

**Scope: full cantools equivalence** — users may feed DBCs with any construct cantools accepts, and silent rejection is worse than loud failure.

**Done-criterion: the construct inventory below must round-trip identically to cantools on a corpus of representative real-world DBCs.**

| Category | Constructs |
|---|---|
| Metadata | `VERSION`, `NS_` (namespaces), `BS_` (bus speed) |
| Structure | `BU_` (nodes), `BO_` (messages), `SG_` (signals) |
| Signal attributes (inside SG_) | start bit, length, byte order (`0`/`1` = Motorola/Intel), signedness (`+`/`-`), factor, offset, min/max, unit, receiver nodes, mux indicator (`M`, `m<n>`) |
| Message attributes (inside BO_) | extended CAN ID (bit 31), CAN-FD flag (attribute-encoded), sender node, DLC |
| Value tables | `VAL_` (signal-scoped), `VAL_TABLE_` (global) |
| Attributes | `BA_DEF_`, `BA_DEF_DEF_`, `BA_`, `BA_DEF_REL_`, `BA_REL_` |
| Comments | `CM_` (node/message/signal scoped) |
| Signal groups | `SIG_GROUP_` |
| Signal value types | `SIG_VALTYPE_` (float32/float64) |
| Extended mux | `SG_MUL_VAL_` |
| Environment vars | `EV_`, `EV_DATA_`, `ENVVAR_DATA_` |

Plan:

- B.3.a Build the construct corpus: 5–10 real-world DBCs (open-source automotive projects; cantools test fixtures) that exercise every row above. This is the parser's test corpus.
- B.3.b Design grammar in `Parser/Combinators.agda` style (structural recursion on length; `--safe --without-K` throughout).
- B.3.c Implement incrementally, bottom-up. Order: `VERSION`/`NS_`/`BS_`; `BU_`/`BO_`/`SG_`; `VAL_`/`VAL_TABLE_`; attributes (`BA_*`); comments; signal groups; value types; extended mux; environment vars.
- B.3.d Roundtrip property: `parse ∘ format ≡ id` for canonical DBC shape.
- B.3.e Add JSON protocol command `{"command": "parse_dbc_text", "text": "..."}`.
- B.3.f Python: switch `parse_dbc` to Agda core. Keep the cantools path behind a single feature flag for the transition window.
- B.3.g Drop cantools dep once the corpus passes and a time-boxed grace window elapses with no regressions (see Risks §4). LGPL win per `project_lgpl_contingency.md`.
- B.3.h C++ `parse_dbc_text` API.
- B.3.i Go `ParseDBCText` API.
- B.3.j Cross-binding parity test: same DBC text → byte-identical `DbcDefinition` across all three.

**Estimate: 3–6 weeks of Agda work + proofs.** Driven primarily by the attribute subsystem and mux edge cases. The lower bound assumes clean real-world DBCs; the upper bound covers encoding quirks (signed value tables, bit-ordering subtleties, Motorola-endianness × mux).

**Matrix row:** `dbc_text_parse` (python=implemented/cpp,go=planned → all three=implemented after B.3.j).

### Phase C — Idiomatic Ergonomics (Part 2) — Design Rounds First

Every item below was proposed during R17 and **rejected** by the user ("The solutions will have to be discussed again — I do not like some of your proposals"). Each requires a fresh design round before code.

#### C.0 — Cancellation Contract SSOT (gated on its own review)

**Decision locked but subject to review:** does this doc exist at all, and if so what does it say?  Open questions before committing:
- Which operations support cancellation (long streams, big batches, live-bus loops)?
- What happens to partial work (rollback? return-what-you-have? commit-first-error?)?
- Is the contract identical across bindings, or does each idiom differ on partial-commit semantics?
- Does the contract need its own doc, or is a section in `docs/architecture/DESIGN.md` enough?

**Deliverable if approved:** `docs/architecture/CANCELLATION.md` — or rejection of the doc itself, with reasoning captured in memory.

#### C.1 + C.2 — Python `async` path + `send_frames_iter` (bundled)

Per `project_async_api_phase6.md`: both items share the Python streaming surface and their design decisions (chunking, cancellation, iterator-vs-async-iter contract) cannot be made coherently in isolation.

Open questions: sync generator first or native async? Shared `chunk_size` parameter? Cancellation via asyncio or generator `.close()`?

#### C.3 — Go `context.Context` on Client ops (R17-DEF-5)

Per `project_go_features_to_explore.md`. Open questions: per-method `...Context(ctx, ...)` overload, ctx-carrying `Client` variant, or both? How does ctx cancellation interact with `sync.Mutex` during an in-flight FFI call?

#### C.4 — C++ cancellation (new backlog item, surfaced by this plan)

Not in the R17 backlog but required for behavioral parity with C.1/C.3. `std::stop_token` is the obvious candidate. Design round required.

#### C.5 — Streaming iteration parity

Python has `iter_can_log` and a planned `send_frames_iter`. Does Go/C++ need a lazy variant for iteration over large traces, or is `SendFrames` / `send_frames_batch` (shipped) plus caller-side chunking enough? Part of C.1/C.2 design round.

### Phase D — Cross-Binding Doc Harness (R17-DEF-6)

Python shipped in R17 C6 via `pytest --markdown-docs`. C++/Go need equivalents.

- **D.1 C++** — catch2-based harness walking tracked markdown files, extracting fenced `cpp` blocks, synthesizing `#include` + `main()` wrappers, compiling with the project toolchain, running. Exclusion syntax: `<!-- cpp notest -->` above fence (mirrors the Python `notest` syntax).
- **D.2 Go** — test helper walking markdown, emitting `_test.go` wrappers, running `go test`. Simpler because `go run` exists and minimal boilerplate is needed.
- Both maintain a tracked-files list (same contract as R17 C6) and structurally ban undocumented `notest` escapes.
- Matrix row: `doc_example_gate_checks` (python=implemented, cpp/go=planned → implemented after D.1/D.2).

## Sequencing

```
Week 1:     Phase A (matrix + gates)         ──┐
                                                │
Week 1–2:   Phase B.1 → B.1.x (sequential)   ──┤
Week 2:     Phase B.2                        ──┤ parallel with B.1.x tail
                                                │
Week 2–3:   Phase D (doc harness C++/Go)     ──┤
                                                │
Week 2–6:   Phase B.3 (DBC parser)           ──┤ longest lead time
                                                │
Week 3+:    Phase C design rounds            ──┘
            (C.0 → C.1+C.2 → C.3 → C.4; implementation gated on user approval per round)
```

Calendar time is dominated by B.3 and Phase C review latency — both are acceptable because the alternative (skipping either) reintroduces the drift this plan exists to stop.

## Risks

1. **B.3 scope creep.** The cantools construct inventory may surface corner cases that push the upper bound past 6 weeks. Mitigation: the construct corpus in B.3.a is the hard boundary; anything outside it is documented as unsupported and deferred, not silently widened.
2. **Phase C review latency.** Four design rounds, each with user sign-off required. Weeks of calendar time for a few days of implementation. Acceptable because previous proposals were rejected — rushing is how we got here.
3. **Matrix gate becomes noise.** If the structural test fails for reasons unrelated to actual parity (e.g., an internal rename), it gets disabled. Mitigation: row `entry` fields must be public API, never internals; review each entry during the A.2 seed.
4. **Cantools fallback becomes permanent.** B.3.g drops the dep after a grace window. Time-box the window to 8 weeks from B.3.j; drop regardless after that and handle remaining issues as forward fixes. An indefinite "grace" becomes load-bearing by default.

## Out of Scope

- **LGPL hard-forced rewrite.** Tracked separately in `project_lgpl_contingency.md`. B.3 naturally resolves the cantools piece; this plan does not commit to the broader contingency (python-can, libgmp).
- **CLI parity for C++/Go.** `not_applicable` in the matrix with reason: "library bindings; CLI is a host-application concern."
- **FFI `unsafeCoerce` guard (R17-DEF-1).** Tracked separately in `project_ffi_unsafecoerce_guard.md`; not a parity concern.

## Related Memory

- `project_binding_feature_gaps.md` — R17-era feature gap snapshot (superseded by `FEATURE_MATRIX.yaml` after A.2 seed)
- `project_async_api_phase6.md` — Python streaming API evolution (drives C.1 + C.2)
- `project_go_features_to_explore.md` — Go backlog (C.3; mux helper merged into B.2)
- `project_ffi_unsafecoerce_guard.md` — explicit non-goal of this plan
- `project_lgpl_contingency.md` — adjacent concern, B.3 partially unblocks
- `feedback_cross_language_parity.md` — rationale for this plan's existence
- `feedback_defer_semantics.md` — these items are not Phase-6-gated; "right after R17"
