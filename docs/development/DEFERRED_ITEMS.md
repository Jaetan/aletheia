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
- **Was** — `senders = []` on the **text** round-trip; `BO_TX_BU_` lines were
  not emitted/parsed by the topology path. (Senders were already modelled on the
  binary/JSON path — `FEATURE_MATRIX dbc_message_senders`, B.1.x commit-3 — so
  this was a text-surface gap, not a missing capability.)
- **Done looks like** — formatter emits `BO_TX_BU_ <id> <node>,…;`, parser
  reads it back into `DBCMessage.senders`, round-trip proven.
- **Verdict** — `DONE` (2026-06-11, branch `agda/e1-isidentstart-hspace-bridge`).
  Wired as an 8th synthesized top-level section (`BO_TX_BU_`) in the universal
  text round-trip, mirroring VAL_: a Format DSL `MsgSenders-format` + a senders
  inverse-bridge (`attachSenders ∘ collectSenders`) composed with the VAL_
  inverse over `clearBothMsg` parse output.  The universal theorem
  `parseText (formatText d) ≡ inj₂ d` now holds with senders round-tripping;
  `WellFormedTextDBCAgg` is strictly weaker (`MessageWF.senders-empty` removed,
  no new obligation).  Runtime behaviour flipped: external `BO_TX_BU_` lines now
  attach to `DBCMessage.senders` (keyed by CAN ID) instead of being dropped —
  cross-binding corpus parity snapshot (`kitchen_sink.json`) regenerated to
  match.  Shipped for its own text-surface value — NOT to close E.2 (the E.2
  full-closure scoping found ~7 independent walls; see E.2).  Note: the
  formatter-side `Formatter.WellFormedText.WellFormedTextMessage.senders-empty`
  is now vestigial (the record has no consumer); left in place (off the
  universal-theorem path, which reaches messages via `MessageWF`).

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

- **Where** — bridge `src/Aletheia/DBC/TextParser/Properties/CharClassDisjoint.agda:76`;
  per-section discharges `src/Aletheia/DBC/TextParser/Properties/WellFormedFromValidity.agda`;
  precondition site `…/Properties/Topology/Signal.agda:88` (`SignalNameStop`).
- **Origin** — B.3.d Layer-4 owed lemmas.
- **✅ Bridge already proven; per-section discharges added 2026-06-10.** On
  re-examination the bridge `isIdentStart→¬isHSpace` was found **already
  proven** in `CharClassDisjoint.agda` (with siblings `isIdentCont→¬isHSpace`,
  `isIdentCont→¬isNewlineStart`) — the "deferred/owed" framing in the
  `Signal.agda:88` note and `memory/project_b3d_layer4_owed_lemmas.md` was
  stale.  The one-line discharge pattern likewise already existed at
  `…Attribute.Foundations.identifier-name-stop`.  The E.2 bounded slice
  generalised it: `Properties.WellFormedFromValidity` now provides
  `signalNameStop : ∀ sig → SignalNameStop sig` plus the five sibling
  `*NameStop` discharges, **unconditionally** from `Identifier`-validity.
- **Remaining** — the `SignalNameStop` (and sibling) preconditions are *still
  threaded* through the Layer-3 / `MessageWF` roundtrips; deleting the threaded
  hypotheses is the same cascade as E.2's `MessageWF` aggregation and is tracked
  there.  The discharge lemmas exist; consuming them to remove the threading is
  the deferred part.
- **Verdict** — `DONE` for the bridge + per-section discharge lemmas; threading
  removal folded into E.2's reassessment.

### E.2 — `WellFormedTextDBCAgg` runtime discharge (AGDA-D-11.2 / 19.6)

- **Where** — `src/Aletheia/DBC/TextParser/WellFormed.agda:46`; handler
  `src/Aletheia/Protocol/Handlers/FormatDBCText.agda`.
- **Origin** — R18 cluster 14 deferral.
- **Today** — the `FormatDBCText` handler emits
  `formatText (deriveNodesIfEmpty dbc)` unconditionally; `formatText : DBC →
  String` is total and takes no proof argument. `WellFormedTextDBCAgg` is the
  precondition of a *separate* theorem
  (`Substrate.Unsafe.parseText-on-formatText`) the handler never invokes at
  runtime.
- **Investigated 2026-06-10 — NOT a correctness gap.** *Structural* proof,
  independent of the handler's prose comment: the handler type-checks under
  `--safe` with no `postulate` and imports neither the round-trip theorem nor
  any axiom, so by construction it carries **zero undischarged proof
  obligations** — "can the runtime hit an undischarged case?" is definitionally
  *no*. A DBC violating the predicate yields output that is
  lossy-on-round-trip, **never wrong and never a crash** (documented
  best-effort contract). All four binding surfaces qualify the round-trip
  claim with "for any well-formed DBC" (Go/Python/C++ `format_dbc_text` +
  `FEATURE_MATRIX`); the validator backstops the two runtime-checkable fields
  (CHECK 18 `DuplicateMessageId` → `msg-ids-unique`, CHECK 23
  `UnknownValueDescriptionTarget` → `unresolved-empty`).
- **Bounded slice delivered 2026-06-10** — `WellFormedFromValidity` derives the
  **five** per-section name-stop fields of `WellFormedTextDBCAgg` (`node-stops`,
  `vt-stops`, `ev-stops`, `cm-stops`, `sg-wfs`) **unconditionally** from
  `Identifier`-validity (via the existing `isIdentStart→¬isHSpace` bridge), so
  the handler comment's "structural fields hold automatically from
  Identifier-validity" is no longer merely *asserted* — it is **proven** for
  those five.  `wellFormedFromValidity` assembles the record, collapsing the
  precondition from **9 fields to 4**: the two heavy proofs (`MessageWF`
  per-signal aggregation, `WFAttribute` BA_DEF_ typing) plus the two
  validator-backed fields (CHECK 18 `msg-ids-unique`, CHECK 23
  `unresolved-empty`) remain hypotheses.
- **Reassessment 2026-06-10 — the full guarantee is BLOCKED at the handler
  source (a wall, not a cost).** `validateDBC`-clean ⇒ `WellFormedTextDBCAgg`
  is **structurally false**: `MessageWF.senders-empty` (`DBCMessage.senders ≡
  []`) is a *lossy-text-round-trip restriction*, not a well-formedness
  property — the formatter drops `BO_TX_BU_` (item A.2), so a perfectly valid
  JSON DBC carrying message senders passes `validateDBC` clean yet fails
  `MessageWF`.  The validator neither does nor should reject senders.  One
  blocked field disproves the implication.  `WellFormedTextDBCAgg` is really
  "this DBC survives the lossy text round-trip unchanged" — and validity does
  not imply that while emission is lossy.
- **What the full guarantee actually requires** — either (a) make text emission
  lossless (the **A.1 / A.2 / A.3** text-completeness program — then the
  `*-empty` restrictions disappear), or (b) a **reject-path redesign**: the
  handler runs a `TextRoundTrippable?` decision and returns a typed refusal for
  non-round-trippable DBCs, yielding the weaker-but-honest guarantee
  "`format_dbc_text` round-trips, or tells you it can't."  Both are materially
  larger, separate decisions — E.2's strengthening is *gated on one of them*.
- **Full-closure scoping, 2026-06-10 (two-agent audit, source-ground-truthed).**
  The precondition is `errorIssues (validateDBCFull d) ≡ []` → `ValidDBC d`,
  built from **only the 8 error-class checks** (`Validity/Theorem.agda:68`);
  warning-class checks contribute nothing to the hypothesis.  Of the 4 residual
  obligations, validateDBC-clean discharges **only `msg-ids-unique`** (CHECK 1,
  error).  The other three are WALLS:
  - `unresolved-empty` — CHECK 23 is **warn-only** and only fires on
    *unknown-target*, never asserts `≡ []`.  The earlier "JSON-parser default,
    technically dischargeable" framing was **WRONG against the source** — there
    is no validateDBC-clean route to this field.
  - `attr-wfs` (WFAttribute) — BA_DEF_ value↔type matching, enum-label
    uniqueness, and name-resolution are checked **nowhere** (CHECK 18 is a
    warn-only duplicate-name check).  A **second, fully-unchecked wall** —
    distinct from A.2.
  - `msg-wfs` (`All MessageWF`) — one unenforced field collapses the record:
    `senders-empty` (lossy, A.2), `wfps`+`item-pres.presence` (mux single-value
    only, A.1), `wf-sigs` (CHECK 15/16 are warnings), `pvs` (BE `msb-ge-len`
    has no check and the predicate is *distinct* from CHECK 8's `BitsInFrame`),
    `mc` (CHECK 4/5 give mux resolvability/acyclicity, not `MasterCoherent`'s
    single-master / master-`Always` shape).
  Cleanly closeable: `msg-ids-unique` + `sig-names-unique` (CHECK 1/2, errors),
  `fb-bound` (DLC type bound), `name-pre`/`send-pre` (Identifier validity).
  Standalone reaches ~6/12 — fewer hypotheses on a helper that still cannot
  close.  Stale source mis-cites found: `WellFormed.agda` cites `msg-ids-unique`
  as "CHECK 18" (it is **CHECK 1**); `Topology/Message.agda` cites
  `sig-names-unique` as "CHECK 23" (it is **CHECK 2**) — both corrected.
- **Verdict** — `HOLD at 5/9` (bounded slice ✅).  Correctness question
  **resolved (no gap)**.  Full closure is a **multi-front program** (A.1/A.2/A.3
  text-completeness + *new* validator error-checks for attribute-typing /
  presence / master-coherence / physical-validity + proof bridges + a validator
  contract change) **or** a reject-path redesign — NOT incremental proof work.
  **A.2 is being taken standalone** (text-surface value; see A.2), not to close E.2.

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
- **Verdict** — ✅ **DONE** (2026-06-10, post-merge cleanup PR). Every
  *tracked* doc standardized on `python/.venv` (`cd python && python3 -m venv
  .venv` for setup; `source python/.venv/bin/activate` for activation from the
  repo root): `BUILDING.md` (all setup / troubleshooting / summary blocks),
  `PITCH.md`, `BENCHMARKS.md`, and `QUICKSTART.md`. The audit surfaced
  `QUICKSTART.md` beyond the prepared list above; it was fixed. `MUTATION.md`
  / `MUTATION_BENCH.yaml` / `CI_LOCAL.md` already used the correct
  `cd python && .venv/…` form and were left unchanged. `docs/presentation/index.html`
  carries the same repo-root form but is a **gitignored, untracked** local
  artifact (`.gitignore:57 docs/presentation/`) — out of scope for a committed
  fix; corrected in the working tree only.
- **Update (2026-06-14) — now gate-backed.** The 2026-06-10 doc sweep was
  necessary but not sufficient: the convention was prose-only, so it drifted.
  It is now mechanically enforced by `tools/check_venv_convention.py` (a
  `run_ci.py` source-hygiene gate; canonical rule in
  [AGENTS.md § Universal Rules](../../AGENTS.md)). Two checks: exactly one
  on-disk `pyvenv.cfg` (at `python/.venv`), and no tracked doc/script may
  create/activate a venv outside `python/.venv`. Authoring the gate surfaced
  one case the prose sweep missed — `benchmarks/run_all.sh` activated a
  **repo-root** `$PROJECT_DIR/.venv` rather than `python/.venv`, so the
  benchmark harness never used the canonical venv (fixed to
  `$PROJECT_DIR/python/.venv`). The `.gitignore` was also collapsed from the
  GitHub-template `env/`/`venv/`/`ENV/`/`.venv` set to the single canonical
  `.venv`, so a stray non-canonical venv now surfaces in `git status`.

### G.2 — `check-changelog` enforces entries only for public-API surfaces, not all changes

- **Where** — `tools/check_changelog.py` `API_PATTERNS` (`python/aletheia/`,
  `go/aletheia/*.go`, `cpp/include/aletheia/`, `haskell-shim/ffi-exports.snapshot`).
- **Origin** — surfaced 2026-06-15 during the build-incrementality PR
  (`perf/build-incremental-honest-graph`): a substantial Shakefile / `.cabal` /
  `tools/` change triggered no CHANGELOG requirement because none of those paths
  match `API_PATTERNS` — yet the project convention is that CHANGELOG.md covers
  ALL notable changes wherever they appear (user directive 2026-06-15).
- **Today** — the gate is a FLOOR (forces an entry for public-API edits) but is
  silent on build-system, tooling, CI, and doc changes; the broader convention is
  met by author discipline, not enforcement, so a notable non-API change can merge
  with no CHANGELOG line.
- **Done looks like** — the gate requires (or nudges) a CHANGELOG entry for a
  wider set of notable changes — e.g. `Shakefile.hs` / `*.cabal` / `tools/` /
  `.github/workflows/` — without becoming noisy on trivial edits (formatting,
  comments, test-only churn), likely via a widened pattern set with exclusions
  mirroring the existing `TEST_EXCLUSIONS`.
- **Cost / risk** — **Low–Medium.** Main hazard is false positives (demanding an
  entry for trivial changes) souring the gate; needs a sound notable-vs-trivial
  heuristic.
- **Blockers / deps** — none; decide the watched-path set + exclusions first.
- **Verdict** — `INVESTIGATE` (user-requested 2026-06-15; explicitly NOT in the
  build-incrementality PR). Scope the patterns + exclusions before building to
  avoid a noisy gate.

### G.3 — Documentation pass for the incremental build + new Shake targets

- **Where** — `docs/development/BUILDING.md` (the authoritative build guide);
  possibly `docs/development/CI_LOCAL.md` and `AGENTS.md` build notes.
- **Origin** — the build-incrementality PR (`perf/build-incremental-honest-graph`,
  2026-06-15) shipped with a CONCISE `CLAUDE.md` update only; the deeper build
  guide was deferred (user directive: concise update now, fuller pass tracked
  here).
- **Today** — `CLAUDE.md` documents the incremental build + `gen-ffi-modules` /
  `iwyu` targets tersely; `BUILDING.md` still describes the old build model and
  does not mention the new targets, the `other-modules` regen workflow, the
  `-Werror=missing-home-modules` drift gate, the staleness gate, or the toolchain
  oracle.
- **Done looks like** — `BUILDING.md` (and any sibling guides) explain: the honest
  dependency graph (`.agda → .agdai` / `.hs → .so`), incremental rebuild behaviour
  + timings, `gen-ffi-modules` (when/why), `cabal run shake -- iwyu`, the staleness
  gate, and the `AgdaVersion` oracle. DRY against `CLAUDE.md` (link, don't
  duplicate).
- **Cost / risk** — **Low** (doc prose), but `BUILDING.md` is the primary build
  guide so accuracy matters; harness-safe (```bash fences are not executed).
- **Blockers / deps** — none; do after the build-incrementality PR merges.
- **Verdict** — `DO` (committed follow-up; user-requested 2026-06-15).

### G.4 — `tools/run_ci.py` is at the 1000-line C0302 ceiling (999/1000)

- **✅ DONE 2026-06-16.** Split along the catalog seam: the step catalog (the
  `_run_agda_gates` / `_run_binding_tests` / `_run_lints` / `_run_gha_checks` /
  `_run_opt_in_lanes` registration helpers behind a public `register_all_steps`,
  plus `AGDA_GATES_STEP` / `AGDA_SHAKE_TARGETS` / `HEAVY_STEPS` / `build_prereq_cmd`)
  moved to a new `tools/_ci_steps.py`; `run_ci.py` keeps the orchestration core
  (`Runner`, `RunContext`, `OptInOptions`, `parse_args`, `main`). The catalog is
  the part that grows with every new gate, so the core now stays small.
  `run_ci.py` 999 → **603 lines**, `_ci_steps.py` 424 — both well clear of the
  ceiling. The e2e test imports the catalog from `tools._ci_steps` and the core
  from `tools.run_ci` (matching the `test_scheduler.py` → `tools._scheduler`
  convention); 20 tests green, pylint 10.00/10 with no C0302, basedpyright 0/0/0,
  ruff clean. No behavior change (same steps, lanes, exit codes).
- **Where** — `tools/run_ci.py` (was 999 lines); pylint `max-module-lines = 1000` (C0302).
- **Origin** — PR #37 (build-incrementality, 2026-06-15) added `build_prereq_cmd`
  + the staleness-gate wiring, leaving the file at 999 lines; surfaced by the
  post-merge advisor review.
- **Cost / risk** — **Low–Medium.** Mechanical extraction, but run_ci.py is the
  gate orchestrator: the e2e test (`python/tests/test_run_ci_runner.py`) had to stay
  green and the imported surface (`AGDA_SHAKE_TARGETS`, `HEAVY_STEPS`,
  `build_prereq_cmd`, `parse_args`, `Runner`, …) preserved (via its true module).
- **Verdict** — `DONE` (the next run_ci change would have forced it; advisor-flagged 2026-06-15).

---

## H. Binding ergonomics

### H.1 — Public, configurable C++ test mock (`aletheia/testing.hpp`)

- **Where** — `docs/FEATURE_MATRIX.yaml` `mock_backend` row (C++ cell `planned`);
  the class itself at `cpp/src/detail/mock_backend.hpp`.
- **Origin** — FEATURE_MATRIX semantics investigation, 2026-06-12 (PR #23);
  reclassified from a self-contradictory `not_applicable` (its reason named the
  conditions under which it "flips to implemented" — the tell of a `planned` item).
- **Today** — the configurable, inspectable `MockBackend` (queue responses +
  assert on captured requests) lives in the test-internal header
  `cpp/src/detail/mock_backend.hpp`, consumed by in-tree tests via direct
  `#include`. The installed surface (`cpp/include/`) ships only the fixed
  `make_mock_backend()` factory (canned acks/successes) + the `IBackend` DI seam
  for roll-your-own doubles. Python (`MockBackend(responses)` + `.inputs`) and Go
  (`NewMockBackend(...)` + `.Inputs()`) ship the configurable mock publicly.
- **Done looks like** — the configurable mock promoted to a public
  `cpp/include/aletheia/testing.hpp`, so external C++ consumers can unit-test
  their code against a pre-loadable / inspectable mock; the `mock_backend` C++
  cell flips to `implemented`.
- **Cost / risk** — **Low** (move + export an existing, working class; no
  kernel / FFI change). Risk: it adds a public API surface to maintain — worth it
  only if an external C++ consumer wants it.
- **Blockers / deps** — none technical; demand-gated (anti-YAGNI, like F.1). The
  `backend_di_seam` row (`implemented`) already lets external consumers roll
  their own `IBackend`; the pre-built configurable mock is the only delta.
- **Verdict** — `HOLD` (planned, demand-gated). Promote to `DO` when a concrete
  external C++ consumer needs it.

---

## Re-examination order (proposed)

Cheapest / highest-confidence first, so early wins de-risk the harder items:

1. **E.1** (owed bridge lemma) — self-contained proof, removes a precondition.
2. **A.2** (`BO_TX_BU_` text senders) — self-contained feature, receiver-list
   precedent.
3. **E.2** (`WellFormedTextDBCAgg`) — investigate correctness relevance first.
4. **A.1 / A.3 / B.1** — gated on a concrete consuming DBC / property.
5. **C.1 / D.1 / F.1 / F.2 / H.1** — accepted / blocked / demand-gated; no action unless constraints change (H.1: a public C++ test mock — promote on concrete external-consumer demand).

**G.1** was resolved in the post-merge cleanup PR (2026-06-10) — a docs-only
change independent of the Agda backlog above; see its ✅ DONE verdict.

> Each item graduates from this doc to a real task only after a per-item
> decision with the user. This file is the backlog + rationale, not a commitment.
