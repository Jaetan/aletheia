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
- **Design-ahead plan** — [EXTENDED_MUX_DESIGN.md](EXTENDED_MUX_DESIGN.md) (rev-2, panel-reviewed):
  the Q1–Q5 decision set, the file-cumulative-span bound design, module layout +
  lemma signatures, corpus-snapshot-flip deliverables, the §12 demand-gate
  trigger/carve-out, and the §12.3 mandatory re-verification pass. Its file:line
  citations are pinned to the 2026-07-12 tree; note the always-strict
  `format_dbc_text` work has since ADDED `WellFormedTextPresence`/`wfps`
  consumers (`WellFormedCheck.agda`, `Properties/WellFormedCheck/Sound.agda`,
  `Sound/Signal.agda`) that post-date the plan's §5.6 deletion inventory — the
  §12.3 pass covers exactly this class.
- **Round-trip context (terminal state of the discharge question).** `wfps`
  (single-value presence) is the lossless-emission wall: this item (+ A.3 for
  `mc`) is the only work that shrinks `format_dbc_text`'s refusal class. The
  universal implication "validateDBC-clean ⇒ `WellFormedTextDBCAgg`" is
  structurally false today (a valid multi-value-mux DBC is the counterexample —
  the structural validator names that shape with a warning-class mirror check,
  but warnings do not affect validity) and REMAINS false even after A.1/A.3:
  `attr-wfs`, `wf-sigs`/`pvs`, and `unresolved-empty` sit behind warning-class
  checks by design (error-class rejection would break the load path and was
  rejected). The shipped state —
  the `wfTextIssues` decision procedure (sound + complete), the exact
  `roundTripsWithᵇ` check, and the typed refusal — is the terminal achievable
  form; the reasoning lives in the
  `Properties.WellFormedFromValidity` module header.
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
- **Design-ahead plan** — [EXTENDED_MUX_DESIGN.md](EXTENDED_MUX_DESIGN.md) § 9 records the A.3
  prerequisites (`MuxParentsWF`, the masters-set emitter, and why the A.1
  collection-policy choice enables A.3).
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

### C.2 — Erased-proof decidables on the hot path (replace Bool-fast-path + lemma)

- **Where** — the per-frame Bool fast paths that pair a `Bool` function with a
  separate equivalence lemma: `_≡csᵇ_` + its lemma family
  (`src/Aletheia/DBC/Identifier.agda`), the `mkBoundedBitVec` bounds dispatch
  (`src/Aletheia/CAN/Encoding.agda` — which already feeds a `Dec` yes-payload
  into an `@0` slot), and future hot-path predicates.
- **Origin** — user proposal during the 2026-07-18 reify-Bools scoping
  analysis (the closed cold-checker Dec work): proofs can be erased, so
  `Dec`-shaped APIs need not cost anything at runtime.
- **Verified facts** (empirical probes, Agda 2.8.0 + stdlib 2.3 + MAlonzo, under
  this repo's exact flags): a `Dec₀` record with `does : Bool` and an
  `@0 proof : Reflects P does` field type-checks under `--safe --without-K`
  with library `--erasure` and **compiles to a GHC `newtype` over `Bool`** —
  runtime-identical to the bare fast path. Constraints that shape the design:
  (1) building `Dec₀` by wrapping a stdlib decider (`fromDec`) silently
  re-allocates the full stock `Dec` upstream — construct from `_≡ᵇ_`-style
  primitives + `Reflects.fromEquivalence` only; (2) an erased proof cannot be
  consumed by relevant definitions (erased `Reflects` matches are rejected, and
  erased `_≡_` matches are rejected under `--without-K` even with
  `--erased-matches`), so cold verification paths that feed soundness lemmas
  must keep *relevant* `Dec` — the two uses are mutually exclusive per proof;
  (3) `recompute₀ : Dec A → @0 A → A` is definable `--safe`-clean (erased-absurd
  trick), bridging erased witnesses back to relevant ones via a relevant decider.
- **Done looks like** — the fast path and its correctness travel as one
  self-certifying value; the erasure checker mechanically enforces what is
  today a convention, plus a `check-erasure`-style Shakefile assertion pinning
  the `newtype … Bool` MAlonzo shape.
- **Cost / risk** — Medium. Runtime target is **identical**, not faster — this
  is convention-hardening, not a perf win; the standing benchmark rule applies
  (MAlonzo's `coe`-wrapped projections could plausibly shift GHC inlining, so
  only a benchmark ratifies "identical").
- **Verdict** — `INVESTIGATE`. Promote when next touching a hot-path predicate,
  or when the convention-enforcement value justifies the benchmark cycle.

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

### E.7 — Provably-dead diagnostic arms: keep as defense-in-depth, or prove-and-prune

- **Where** — the `checkSignalBounds` and `pvIssues` arms of `wfTextIssues`
  (`src/Aletheia/DBC/TextParser/WellFormedCheck.agda`; the tightness
  classification in that module's header records the full analysis).
- **Origin** — the E.3 tightness classification (2026-07-20). The `wf-sigs`
  bound codes can fire on NO public route (every parse route clamps signal
  geometry into range at entry, making the bound an invariant of kernel-resident
  DBCs), and the `pvs` arms cannot fire on the FormatDBCText route (the
  handler's own JSON ingestion gate decides the same propositions first and
  refuses with typed parse errors).
- **The decision** — keep the arms as documented defense-in-depth (the checker
  must decide every `WellFormedTextDBCAgg` field to keep the
  `wfTextIssues ≡ [] ⟺ WF` equivalence total; the header documents why they
  cannot fire), or prove the deadness (a lemma of the shape "`physicalGate`
  success ⇒ `pvIssues ≡ []`" looks within reach) and re-scope the checker.
- **Cost / risk** — the lemma route is a genuine proof (medium); the
  keep-documented route costs nothing further. Risk of pruning: the equivalence
  proof restructures around the removed arms.
- **Verdict** — `INVESTIGATE` (decide the disposition; the documented state is
  already sound).

### E.8 — Proof-surplus hypotheses in the signal-geometry round-trip lemmas

- **Where** — `unconvertStartBit-roundtrip` (binds its msb-ge-len hypothesis
  without using it) and `unconvertSB-bounded`'s BigEndian branch (discharges
  from the frame bound alone, without `startBit-bound`) — under
  `src/Aletheia/DBC/TextParser/Properties/Topology/`.
- **Origin** — the E.3 tightness classification (2026-07-20): each rides
  free in the format→parse direction.
- **Done looks like** — the unused hypotheses dropped (or a comment recording
  why they stay for statement symmetry), with the full proof gate battery green.
- **Cost / risk** — small proof-hygiene pass; the risk is signature churn in
  the lemmas' importers.
- **Verdict** — `HOLD` (land anytime; batch with the next proof-touching work).

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

## J. Entry-boundary semantics

### J.1 — Normalize-vs-refuse for out-of-range signal geometry at the JSON boundary

- **Where** — the JSON DBC ingestion path (`parseSignalFields` / `buildSignal`
  clamps: start bit and bit length are mod-reduced into range at entry).
- **Origin** — the E.3 tightness classification (2026-07-20), observed live:
  a submitted start bit of 512 becomes 0 and an oversized bit length is
  mod-reduced, with `validate_dbc` reporting no issues — so `format_dbc_text`'s
  always-strict guarantee is measured against the clamped in-kernel DBC, not
  the caller's literal input, and the caller gets back text whose numbers
  differ from what they sent with an empty issues list.
- **The decision** — keep the normalize-at-entry contract (documented), refuse
  out-of-range geometry with a typed error (matching the refuse posture the
  same path already applies to zero-length and MSB-below-length shapes), or
  surface a warning-class diagnostic when a clamp actually changed a value.
- **Cost / risk** — refusing is a behavior change on the JSON wire (breaking
  for callers relying on silent clamping — none known); warning-class surfacing
  needs a new wire code (WIRE_CODES.yaml + parity tests per binding).
- **Verdict** — `INVESTIGATE` (a contract decision; the current behavior is
  consistent but silent).

## Re-examination order (proposed)

Cheapest / highest-confidence first, so early wins de-risk the harder items:

1. **J.1 / E.7** — investigate-class contract/disposition decisions raised by
   the E.3 tightness classification; each is a discussion + a scoped change.
2. **E.8** — small proof-hygiene pass; batch with the next proof-touching work.
3. **A.1 / A.3 / B.1** — gated on a concrete consuming DBC / property.
4. **C.2** — investigate-on-trigger: revisit when next touching a hot-path
   predicate (erased-proof `Dec₀` vs the Bool-fast-path + lemma pattern).
5. **C.1 / D.1 / F.1 / F.2 / H.1** — accepted / blocked / demand-gated; no action unless constraints change (H.1: a public C++ test mock — promote on concrete external-consumer demand).
6. **I.1** (Go/C++ arm64 overflow guard) — target-gated; no action until a concrete non-amd64 embedded target with a verified full cross-toolchain (GHC + clang + rustc) is chosen.

> Each item graduates from this doc to a real task only after a per-item
> decision with the user. This file is the backlog + rationale, not a commitment.
