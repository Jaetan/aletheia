<!--
SPDX-FileCopyrightText: 2025 Nicolas Pelletier
SPDX-License-Identifier: BSD-2-Clause
-->

# Deferred-items plan & re-examination

> **Status: DRAFT (post-`ci-speed`-merge work).** This document collects every
> in-source deferral / owed-work note currently in the tree into one place, and
> records a first-pass *re-examination* of each: is it still worth doing, what
> would it cost, what blocks it, and the recommended next step.
>
> Provenance: compiled 2026-06-08 during the `ci-speed` pre-merge review. None
> of these were introduced by `ci-speed`; all pre-date it on `main`. The
> closed review record (r20–r23: 196/196 findings closed) holds **zero** open
> findings — everything below is an *in-source* deferral, not a review carry-over.

## How to read this

Each item carries:

- **Where** — `file:line` anchor(s) for the in-source note.
- **Origin** — the round / system-review / category that introduced it.
- **Today** — the current behaviour (what the code does in lieu of the deferred work).
- **Done looks like** — the end state if we close it.
- **Cost / risk** — rough effort + the main hazard.
- **Blockers / deps** — anything that must be true first.
- **Verdict (first pass)** — `DO` / `HOLD` / `CAN'T` / `INVESTIGATE`, with the reason.

The verdict is a *recommendation for re-examination*, not a decision. Decisions
are taken with the user, item by item.

---

## A. DBC `.dbc` text round-trip — feature completeness

These three are facets of one gap: the verified text formatter/parser round-trip
covers the common DBC shape, but a few constructs are parsed-and-dropped or
emitted as empty. The binary/JSON path is unaffected — this is specific to the
**text** (`parseText` / `formatText`) surface.

### A.1 — Multi-value mux `SG_MUL_VAL_` → real `When` selectors

- **Where** — `src/Aletheia/DBC/TextParser/ExtendedMux.agda` (drop-parser);
  `src/Aletheia/DBC/TextParser/Topology.agda:55`;
  `src/Aletheia/DBC/TextFormatter/Topology.agda:32`.
- **Origin** — Track B.3.c.8 (text-parser construct corpus).
- **Today** — `SG_MUL_VAL_` lines are syntactically parsed and **discarded**
  (`parseSigMulVal : Parser ⊤`). Single-value `m<N>` selectors map to a
  singleton `When _ (N ∷ [])`; multi-value ranges are not materialised.
- **Done looks like** — the parsed ranges flow into actual multi-value
  `When _ (v₀ ∷ v₁ ∷ …)` selectors on the parse side, and the formatter emits
  `SG_MUL_VAL_` for signals carrying multi-value presence; round-trip proven.
- **Cost / risk** — **High.** This is *cross-line coordination*: `SG_MUL_VAL_`
  lives on a different line from the `SG_` it annotates, so the aggregator must
  correlate them, and the round-trip proof has to thread that correlation. The
  existing per-line `many`-based roundtrip lemmas don't compose across the
  correlation.
- **Blockers / deps** — needs a data-model decision: where multi-value presence
  is stored on `DBCSignal` and how the aggregator joins `SG_` + `SG_MUL_VAL_`.
- **Verdict** — `INVESTIGATE`. Real feature, real cost. Worth it only if a
  consuming DBC actually uses multi-value mux; check the target corpus first.

### A.2 — `BO_TX_BU_` message senders on the text path

- **Where** — `src/Aletheia/DBC/TextFormatter/Topology.agda:188`;
  `src/Aletheia/DBC/TextParser/Topology.agda:59`.
- **Origin** — Track B.3.c (text round-trip).
- **Today** — `senders = []` on the **text** round-trip; `BO_TX_BU_` lines are
  not emitted/parsed by the topology path. NB message senders **are** modelled
  and shipped on the binary/JSON path (`FEATURE_MATRIX dbc_message_senders`,
  B.1.x commit-3) — so this is a text-surface gap, not a missing capability.
- **Done looks like** — formatter emits `BO_TX_BU_ <id> <node>,…;`, parser
  reads it back into `DBCMessage.senders`, round-trip proven.
- **Cost / risk** — **Medium.** Self-contained: a single line shape, list of
  identifiers, no cross-line correlation. The round-trip lemma mirrors the
  existing receiver-list pattern (`parseReceiverList∘strip-roundtrip`).
- **Blockers / deps** — none material; the data already exists on `DBCMessage`.
- **Verdict** — `DO` (if any text-round-trip item is taken first, this is the
  cheapest). The receiver-list precedent makes the proof tractable.

### A.3 — Nested multiplexors `m<N>M`

- **Where** — `src/Aletheia/DBC/TextFormatter/Topology.agda:32`.
- **Origin** — Track B.3.c; flagged Phase-6-adjacent.
- **Today** — not emitted; the formatter emits the head value of `When _ values`
  only (matches single-value cantools output).
- **Done looks like** — extended-mux marker `m<N>M` emitted/parsed for signals
  that are both multiplexed and multiplexors.
- **Cost / risk** — **High**, and entangled with A.1 (both are the extended-mux
  story). Nested mux is rare in practice.
- **Verdict** — `HOLD`. Lowest practical demand; revisit only alongside A.1.

---

## B. Predicate vocabulary

### B.1 — CAN-FD bus-bit predicates (BRS / ESI)

- **Where** — `src/Aletheia/Trace/CANTrace.agda:46`.
- **Origin** — Phase 5.1 scope note (explicitly Phase 6).
- **Today** — `Maybe Bool` BRS/ESI metadata is pass-through to bindings via the
  FFI/JSON response, but is **not** liftable to LTL atomic predicates (LTL
  atoms are signal-level only).
- **Done looks like** — `BRS-set` / `ESI-set` as truth-valued atomic predicates
  in the LTL vocabulary, with the semantics + adequacy proofs extended.
- **Cost / risk** — **Medium–High.** Touches the verified LTL kernel
  (Syntax / Semantics / Adequacy / SignalPredicate), which is the most
  proof-expensive surface to extend.
- **Blockers / deps** — a use case (does any target property reference BRS/ESI?).
- **Verdict** — `HOLD` (Phase-6 feature by prior scoping). Promote to
  `INVESTIGATE` only with a concrete consumer.

---

## C. Performance

### C.1 — `lookupByKey` Bool fast path (AA-16.8)

- **Where** — `src/Aletheia/Prelude.agda:72`.
- **Origin** — review category AA-16 (Dec-allocation hot-path sweep).
- **Today** — `lookupByKey` uses `⌊ _≟ₛ_ ⌋`, allocating a `Dec` cell per
  comparison. Unlike its hot-path siblings (AA-16.2 `findSignalInList`,
  AA-16.3 `lookupEntries`), this lookup is **cold** — its only callers are
  per-JSON-command parsing helpers, not per-frame.
- **Done looks like** — a `Bool`-valued fast path + equivalence lemma, as done
  for the hot-path siblings.
- **Cost / risk** — **Low effort, near-zero payoff, and partly blocked.** The
  real speedup needs `primStringEquality` bridged into propositional form, which
  requires a **postulate** → impossible under `--safe` outside the allowlisted
  Unsafe substrate. Stdlib `_==_` gives no real speedup (wraps `isYes (_≟_)`).
- **Verdict** — `CAN'T` (under current constraints) / `HOLD`. The marginal Dec
  alloc is dominated by JSON parsing itself; not worth an Unsafe-module entry.

---

## D. Accepted constraints (documented exceptions, not pending work)

### D.1 — Cat-29 `NonZero` instance args on stdlib `_÷_`

- **Where** — `src/Aletheia/CAN/Encoding/Properties/Arithmetic/Rational.agda:31`;
  `src/Aletheia/Data/BitVec/Conversion.agda:14`;
  `src/Aletheia/CAN/Endianness.agda:28`.
- **Origin** — review Cat 29 (stdlib-mandate) in-source exception path.
- **Today** — these modules use `.{{_ : NonZero q}}` on stdlib ℚ `_÷_`; every
  call site supplies the witness explicitly, so there is **no instance-search
  ambiguity**.
- **Done looks like** — n/a. "Closing" this would mean abandoning stdlib
  division and reimplementing it witness-free — a regression, not progress.
- **Verdict** — `HOLD` permanently (accepted constraint). Listed for
  completeness; not actionable work.

---

## E. Proof completeness

### E.1 — `isIdentStart→¬isHSpace` owed bridge lemma

- **Where** — `src/Aletheia/DBC/TextParser/Properties/Topology/Signal.agda:88`
  (`SignalNameStop`); tracked in `memory/project_b3d_layer4_owed_lemmas.md`.
- **Origin** — B.3.d Layer-4 owed lemmas.
- **Today** — `SignalNameStop sig` (the signal name decomposes as `c ∷ cs` with
  `isHSpace c ≡ false`) is taken as a **precondition** of the signal-line
  round-trip, rather than derived from the identifier-start invariant.
- **Done looks like** — prove `isIdentStart c → isHSpace c ≡ false` so the
  precondition discharges automatically wherever a well-formed identifier is in
  scope, removing the owed hypothesis.
- **Cost / risk** — **Low–Medium.** A character-class bridge lemma; the shape is
  known (`Format.SignalLine.Roundtrip.NameStop` modulo a record-η rewrite).
- **Blockers / deps** — none; both predicates are decidable Char classifiers.
- **Verdict** — `DO`. Self-contained, removes a standing precondition, improves
  the universality of the round-trip statement. Good first re-examination target.

### E.2 — `WellFormedTextDBCAgg` runtime discharge (AGDA-D-11.2 / 19.6)

- **Where** — `src/Aletheia/DBC/TextParser/WellFormed.agda:46`.
- **Origin** — R18 cluster 14 deferral.
- **Today** — the `FormatDBCText` FFI handler is required to discharge
  `WellFormedTextDBCAgg` at runtime; the obligation is documented but tracked
  separately rather than proven at the handler boundary.
- **Done looks like** — the handler constructs the well-formedness witness (or
  rejects) at runtime, with the obligation proven where the boundary is crossed.
- **Cost / risk** — **Medium.** Handler-boundary proof work; mirrors other
  handler-boundary discharge patterns (`feedback_handler_vs_parser_bound_placement`).
- **Verdict** — `INVESTIGATE`. Confirm whether the runtime path can currently
  hit an undischarged case; if so, this is correctness-relevant, not cosmetic.

---

## F. Parked by prior user decision (re-confirm, don't re-open lightly)

### F.1 — CL10-3: Go `FormatDBC` → structured result

- **Where** — `go/aletheia/client.go:396` (in-source DEFERRED/TRACKED block).
- **Origin** — R19P2 cluster 10.
- **Today** — `FormatDBC` returns `*DBCDefinition`; no structured wrapper.
- **User decision (2026-06-06)** — "don't do anything yet, keep the note." It's
  a **speculative** feature (rendering-options metadata no consumer needs);
  building it adds unused wire structure across all 3 bindings + the kernel.
- **Verdict** — `HOLD` (anti-YAGNI). In-source gate stands: "revisit when a
  consumer needs richer return metadata."

### F.2 — Agda atom-table `Fin` (system-review 11.1)

- **Where** — `StreamState` internals.
- **Today** — atom table indexed without `Fin n`.
- **User decision** — deliberately NOT done: MAlonzo compiles `Fin n` as a unary
  Peano chain → per-frame heap allocation on the hot path. Soundness is already
  closed by Property 27.
- **Verdict** — `HOLD` permanently. Closing it **regresses** performance.

---

## G. Docs / tooling consistency (discovered drift, not an in-source note)

### G.1 — venv convention: docs say repo-root `.venv`, tooling uses `python/.venv`

- **Where** — repo-root form in ~15 doc locations: `docs/development/BUILDING.md`
  (203, 206, 219, 222, 281, 403, 428, 444, 465–467, 561–563, 702),
  `docs/PITCH.md` (342–343), `docs/development/BENCHMARKS.md` (23). Canonical
  `python/.venv` form: `tools/run_ci.py:348`, `tools/mutation_run.py:200,206`,
  `tools/stability_run.py:179`, `.github/workflows/pr-full-ci.yml`,
  `python/pyproject.toml` (basedpyright `venvPath="."`), `CLAUDE.md`.
- **Origin** — discovered 2026-06-09 during the `ci-speed` PR #7 GHA debugging.
  The basedpyright `venvPath` bug (fixed `9f0954b`) was masked locally by a
  stray `<repo_root>/.venv` that had been created by following these docs.
- **Today** — docs instruct creating + **activating** a repo-root `.venv`; all
  automation expects `python/.venv` (run_ci falls back to system `python3.14`
  if `python/.venv` is absent). A contributor who follows BUILDING.md ends up
  with a venv the gates don't use. The stray `<repo_root>/.venv` itself was
  **deleted 2026-06-09** (untracked/git-ignored, 385 MB, stale `aletheia 0.3.2`)
  — this item is about preventing its *regeneration* from the docs.
- **Done looks like** — every doc standardized on `python/.venv`
  (`cd python && python3 -m venv .venv` + `source python/.venv/bin/activate`).
  In particular `BUILDING.md:555` — which documents *this exact* "basedpyright
  runs against the system Python instead of your venv" symptom with a now-stale
  repo-root remedy — corrected.
- **Cost / risk** — **Low** (mechanical doc edits, ~15 locations) but touches
  the primary build guide. Harness-safe: `pytest --markdown-docs` executes only
  ```python fences (per `conftest.py`), not the ```bash venv blocks.
- **Blockers / deps** — none; the convention is already settled (`python/.venv`
  is canonical across all tooling + CLAUDE.md).
- **Verdict** — `DO` as a **dedicated post-merge docs PR** (user decision
  2026-06-09: align as a follow-up, keep `ci-speed` focused on PR #7 green).

---

## Re-examination order (proposed)

Cheapest / highest-confidence first, so early wins de-risk the harder items:

1. **E.1** (owed bridge lemma) — self-contained proof, removes a precondition.
2. **A.2** (`BO_TX_BU_` text senders) — self-contained feature, receiver-list
   precedent.
3. **E.2** (`WellFormedTextDBCAgg`) — investigate correctness relevance first.
4. **A.1 / A.3 / B.1** — gated on a concrete consuming DBC / property.
5. **C.1 / D.1 / F.1 / F.2** — accepted/blocked; no action unless constraints change.

**G.1** runs on its own track — a docs-only PR independent of the Agda backlog
above, scheduled for right after the `ci-speed` merge.

> Each item graduates from this doc to a real task only after a per-item
> decision with the user. This file is the backlog + rationale, not a commitment.
