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
> of these were introduced by `ci-speed`; all pre-date it on `main`. Everything
> below is an *in-source* deferral, not a carry-over from closed review work.

## How to read this

Each item carries:

- **Where** — `file:line` anchor(s) for the in-source note.
- **Origin** — what introduced the in-source note.
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
- **Origin** — text-parser construct corpus.
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

### A.3 — Nested multiplexors `m<N>M`

- **Where** — `src/Aletheia/DBC/TextFormatter/Topology.agda:32`.
- **Origin** — flagged Phase-6-adjacent.
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

### C.1 — `lookupByKey` Bool fast path

- **Where** — `src/Aletheia/Prelude.agda:72`.
- **Origin** — Dec-allocation hot-path sweep.
- **Today** — `lookupByKey` uses `⌊ _≟ₛ_ ⌋`, allocating a `Dec` cell per
  comparison. Unlike its hot-path siblings (`findSignalInList`,
  `lookupEntries`), this lookup is **cold** — its only callers are
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

### D.1 — `NonZero` instance args on stdlib `_÷_`

- **Where** — `src/Aletheia/CAN/Encoding/Properties/Arithmetic/Rational.agda:31`;
  `src/Aletheia/Data/BitVec/Conversion.agda:14`;
  `src/Aletheia/CAN/Endianness.agda:28`.
- **Origin** — Agda cat 29 (stdlib-mandate) in-source exception path.
- **Today** — these modules use `.{{_ : NonZero q}}` on stdlib ℚ `_÷_`; every
  call site supplies the witness explicitly, so there is **no instance-search
  ambiguity**.
- **Done looks like** — n/a. "Closing" this would mean abandoning stdlib
  division and reimplementing it witness-free — a regression, not progress.
- **Verdict** — `HOLD` permanently (accepted constraint). Listed for
  completeness; not actionable work.

---

## E. Proof completeness

### E.2 — `WellFormedTextDBCAgg` runtime discharge

- **Where** — `src/Aletheia/DBC/TextParser/WellFormed.agda:46`; handler
  `src/Aletheia/Protocol/Handlers/FormatDBCText.agda`.
- **Origin** — text round-trip proof obligation (`WellFormedTextDBCAgg` precondition).
- **Today** — the `FormatDBCText` handler emits
  `formatText (deriveNodesIfEmpty dbc)` unconditionally; `formatText : DBC →
  String` is total and takes no proof argument. `WellFormedTextDBCAgg` is the
  precondition of a *separate* theorem
  (`Substrate.Unsafe.parseText-on-formatText`) the handler never invokes at
  runtime.
- **Not a correctness gap.** The handler type-checks under `--safe` with no
  `postulate` and imports neither the round-trip theorem nor any axiom, so it
  carries **zero undischarged proof obligations** — "can the runtime hit an
  undischarged case?" is definitionally *no*. A DBC violating the predicate
  yields output that is *lossy-on-round-trip*, **never wrong and never a crash**
  (documented best-effort contract; all four bindings qualify the claim with
  "for any well-formed DBC").
- **Bounded slice (done).** `WellFormedFromValidity` derives **five** of the nine
  `WellFormedTextDBCAgg` fields — the name-stop fields `node-stops`, `vt-stops`,
  `ev-stops`, `cm-stops`, `sg-wfs` — **unconditionally** from `Identifier`-validity
  (via the `isIdentStart→¬isHSpace` bridge). Four fields remain: `msg-wfs`
  (`All MessageWF`), `attr-wfs` (`All WFAttribute`), `msg-ids-unique`, and
  `unresolved-empty`.
- **`validateDBC`-clean does not discharge the remaining four.** The precondition
  `errorIssues (validateDBCFull d) ≡ []` is built from **only the 8 error-class
  checks** (`Validity/Theorem.agda`); warning-class checks contribute nothing. Of
  the four residual fields it discharges **only `msg-ids-unique`** (CHECK 1, error).
  The other three are walls:
  - `unresolved-empty` (`DBC.unresolvedValueDescs d ≡ []`) — CHECK 23 is
    **warn-only** and fires only on an unknown target; it never asserts `≡ []`.
    No validateDBC-clean route to this field.
  - `attr-wfs` (`WFAttribute`) — BA_DEF_ value↔type matching, enum-label
    uniqueness, and name resolution are checked **nowhere** (CHECK 18 is only a
    warn-only duplicate-name check). A fully-unchecked wall.
  - `msg-wfs` (`All MessageWF`) — one unenforced sub-field collapses the record:
    `wfps` / `item-pres` (require single-value mux — the formatter drops
    multi-value `SG_MUL_VAL_`, **item A.1**), `wf-sigs` (CHECK 15/16 are
    warnings), `pvs` (BE `msb-ge-len` is unchecked and *distinct* from CHECK 8's
    `BitsInFrame`), and `mc` (CHECK 4/5 give mux resolvability/acyclicity, not
    `MasterCoherent`'s single-master / master-`Always` shape). Its cleanly-closeable
    sub-fields (`fb-bound`, `name-pre`/`send-pre`, `sig-names-unique` — CHECK 2)
    don't rescue it.
- **The implication is structurally false.** `WellFormedTextDBCAgg` really means
  "this DBC survives the lossy text round-trip unchanged", and validity does not
  imply that while emission is lossy: a valid DBC using **multi-value mux** passes
  `validateDBC` clean yet fails `wfps`, because the formatter drops `SG_MUL_VAL_`
  (**A.1**). One blocked field disproves it — and the validator neither does nor
  should reject the construct.
- **What full closure requires** — either (a) make text emission lossless (the
  **A.1 / A.3** multi-value-mux + nested-mux completeness work, which removes the
  lossy-emission restrictions); (b) a **reject-path redesign** where the handler
  runs a `TextRoundTrippable?` decision and returns a typed refusal for
  non-round-trippable DBCs ("`format_dbc_text` round-trips, or tells you it can't");
  or (c) new validator **error**-class checks for attribute-typing / presence /
  master-coherence / physical-validity that strengthen the hypothesis. All three are
  materially larger, separate decisions — not incremental proof work.
- **Verdict** — `HOLD`. Correctness question **resolved (no gap)**; the bounded
  slice is done (five of nine fields). Full closure is a multi-front program per
  the above. (The `BO_TX_BU_` message-senders text round-trip, once tracked
  alongside this, shipped standalone for its own text-surface value and removed the
  former `MessageWF.senders-empty` restriction — but it did not close E.2.)

---

## F. Parked by prior user decision (re-confirm, don't re-open lightly)

### F.1 — Go `FormatDBC` → structured result

- **Where** — `go/aletheia/client.go:396` (in-source DEFERRED/TRACKED block).
- **Origin** — in-source DEFERRED/TRACKED note on `FormatDBC`.
- **Today** — `FormatDBC` returns `*DBCDefinition`; no structured wrapper.
- **User decision (2026-06-06)** — "don't do anything yet, keep the note." It's
  a **speculative** feature (rendering-options metadata no consumer needs);
  building it adds unused wire structure across all 3 bindings + the kernel.
- **Verdict** — `HOLD` (anti-YAGNI). In-source gate stands: "revisit when a
  consumer needs richer return metadata."

### F.2 — Agda atom-table `Fin`

- **Where** — `StreamState` internals.
- **Today** — atom table indexed without `Fin n`.
- **User decision** — deliberately NOT done: MAlonzo compiles `Fin n` as a unary
  Peano chain → per-frame heap allocation on the hot path. Soundness is already
  closed by Property 27.
- **Verdict** — `HOLD` permanently. Closing it **regresses** performance.

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

## I. Portability / cross-architecture

### I.1 — Go/C++ float→int overflow guard assumes amd64 conversion semantics

- **Where** — `go/aletheia/types.go` (`FloatToRational` round-trip guard + its
  in-code amd64 `NB`); `cpp/src/types.cpp:27-29` (the `from_double` post-cast
  equality check it mirrors).
- **Origin** — 2026-06-24, advisor-flagged while fixing the
  amd64 silent-wrap.
- **Today** — both guards reject an int64-overflowing integral float (e.g. 2^63)
  by casting to int64 and comparing the round-trip back to double. Correct on
  amd64, where an out-of-range float→int conversion **wraps** to MinInt64 (so the
  round-trip fails and 2^63 is rejected). On arm64 the same conversion
  **saturates** to MaxInt64, and `double(MaxInt64) == 2^63` is true, so the guard
  would **falsely accept** 2^63 — re-introducing the silent wrong-value-with-no-
  error bug the earlier fix closed. Rust/Python use range/scaling checks that don't depend on
  conversion semantics. CI builds + tests amd64 only.
- **Done looks like** — Go + C++ switch to an arch-independent bound check
  (`v >= -2^63 && v < 2^63`, both exact float64 literals) that never performs an
  out-of-range cast, so 2^63 is rejected on every architecture; Rust/Python
  re-verified for the same property.
- **Cost / risk** — **Low** (a few lines × 2 bindings + tests). Risk: it makes
  Go/C++ use a different mechanism than the round-trip mirror they share today —
  a deliberate cross-binding mechanism change, so land it as one lockstep edit.
- **Blockers / deps** — **gated on a prior, larger question**: Aletheia runs on
  non-amd64 only if the *entire* stack cross-compiles to that target — the
  GHC/MAlonzo `.so`, the C++ binding, and the Rust binding all need a
  known-complete cross-toolchain (GHC cross-compiler + clang + rustc) for the
  chosen architecture. Until a concrete embedded target with verified cross
  compilers for all three is selected, there is no architecture on which this
  guard can be wrong, so the fix is not actionable.
- **Verdict** — `HOLD` (target-gated). Promote to `DO` only once a concrete
  non-amd64 embedded target with a verified full cross-toolchain is chosen;
  revisit alongside that cross-compilation work.

---

## Re-examination order (proposed)

Cheapest / highest-confidence first, so early wins de-risk the harder items:

1. **E.2** (`WellFormedTextDBCAgg`) — investigate correctness relevance first.
2. **A.1 / A.3 / B.1** — gated on a concrete consuming DBC / property.
3. **C.1 / D.1 / F.1 / F.2 / H.1** — accepted / blocked / demand-gated; no action unless constraints change (H.1: a public C++ test mock — promote on concrete external-consumer demand).
4. **I.1** (Go/C++ arm64 overflow guard) — target-gated; no action until a concrete non-amd64 embedded target with a verified full cross-toolchain (GHC + clang + rustc) is chosen.

> Each item graduates from this doc to a real task only after a per-item
> decision with the user. This file is the backlog + rationale, not a commitment.
