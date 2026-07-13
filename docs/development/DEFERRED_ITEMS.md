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

- **Where** — `src/Aletheia/DBC/TextParser/WellFormed.agda:85` (the record);
  handler `src/Aletheia/Protocol/Handlers/FormatDBCText.agda`.
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
  the four residual fields it discharges **only `msg-ids-unique`** (CHECK 1, error;
  via `checkAllDuplicateMessageIds-sound`, one routine `AllPairs`-map step from the
  field's mapped form — that bridge lemma is currently unwritten).
  The other three are walls:
  - `unresolved-empty` (`DBC.unresolvedValueDescs d ≡ []`) — CHECK 23 is
    **warn-only** (one warning per unresolved entry, `Checks.agda:604-613`;
    warnings never enter `errorIssues`), so validateDBC-clean asserts nothing
    about this field. (CHECK-23 *silence* does imply `≡ []` — but that is a
    caller-side warning inspection, not the theorem's error-clean hypothesis.)
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
- **Verdict** — `HOLD` for full closure. Correctness question **resolved (no
  gap)**; the bounded slice is done (five of nine fields). Full closure is a
  multi-front program per the above. (The `BO_TX_BU_` message-senders text
  round-trip, once tracked alongside this, shipped standalone for its own
  text-surface value and removed the former `MessageWF.senders-empty`
  restriction — but it did not close E.2.)
- **Re-examined 2026-07-12** — every claim above adversarially verified against
  source and upheld (plus one the entry missed: the Rust rustdoc lacked the
  round-trip qualifier the other three bindings carry — fixed in the same
  accuracy batch as this update). Key re-framing: the theorem's precondition is
  **unobservable** — no user-facing surface can evaluate `WellFormedTextDBCAgg`,
  so a user cannot distinguish "my export is proven-faithful" from "my export
  silently dropped multi-value mux". Routes **scheduled (b) ≫ (a) ≫ (c)**:
  - **(b) first** — a runtime checker for the predicate at the format handler,
    surfaced as a #150-style issues envelope (format-anyway default, opt-in
    strict refusal): the only route that makes the guarantee observable
    ("round-trips, or tells you it can't"), wire-additive (binding returns
    enriched in place — BREAKING, ratified 2026-07-12: no sibling methods),
    medium and self-contained. Pinned as a prerequisite of any
    text-export-bearing product surface.
  - **(a) second** — lossless emission (A.1 multi-value `SG_MUL_VAL_`, then
    A.3 nested mux): the only route that removes the `wfps` wall; stays
    corpus-gated per A.1's own gate; design-ahead plan maintained.
  - **(c) last** — stronger validator: **rejected standalone** (cannot close
    `wfps` while emission is lossy; every new error-class check breaks the load
    path); its useful checks fold into (b)'s diagnostics or an opt-in strict
    profile.

  Adversarially-reviewed proof strategies for all three routes:
  [E2_PROOF_STRATEGY.md](E2_PROOF_STRATEGY.md).

### E.3 — V1 diagnostic tightness classification (round-trip-necessary vs merely-bundled)

- **Where** — the `wfTextIssues` checker (`src/Aletheia/DBC/TextParser/WellFormedCheck.agda`)
  and the round-trip proof `parseText-on-formatText`
  (`src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda:119`).
- **Origin** — the 2026-07-13 adversarial review of E.2 route (b) slice 1. Slice 1
  proves `wfTextIssues d ≡ [] ⟺ WellFormedTextDBCAgg d`, and `WellFormedTextDBCAgg`
  is **sufficient-not-necessary** for round-tripping (it is the antecedent of
  `parseText-on-formatText`; no converse). So a non-empty `wfTextIssues` (a flag)
  does **not** prove the DBC fails to round-trip — some flagged DBCs may survive.
- **The task** — trace `parseText-on-formatText` and classify **each**
  `WellFormedTextDBCAgg` conjunct (hence each `wfTextIssues` diagnostic) as either
  **round-trip-NECESSARY** (tight — a flag always means a genuine loss) or
  **MERELY-BUNDLED** (can false-alarm — the DBC round-trips despite the flag).
  Deliverable: a per-condition table turning today's *reasoned* examples into
  *proven* statements.
- **Grounded hypotheses to confirm/refute** (from the review): the uniqueness
  conjuncts `sig-names-unique`/`msg-ids-unique` read as `VAL_`-collapse-specific
  (their field comments) ⇒ likely merely-bundled for a DBC with no value
  descriptions (`messages`/`signals` are order-preserving lists); the
  physical-validity bounds (`wf-sigs`/`pvs`) look text-irrelevant (the formatter
  prints raw numbers) ⇒ likely merely-bundled; `wfps` (multi-value mux) and
  `unresolved-empty` look **tight** (genuine formatter loss — A.1). Verify each.
- **Optional downstream** — tighten or condition the merely-bundled checks to cut
  false alarms, or mark those diagnostics "conditional" in the wire/docs.
- **NOT blocking E.2.** V2 (route-b slice 2) dissolves the over-approximation for
  the only decision that needs exactness (strict-mode refusal gates on the V2 exact
  check, never on `WellFormedTextDBCAgg` necessity); V1 diagnostics are already
  worded "round-trip not proven", never "will not" (E2_ROUTE_B.md §7.6). Land
  anytime after slice 1 — a good fit for a multi-agent proof-trace workflow.
- **Verdict** — `SCHEDULED` (quality/tightening analysis, non-blocking).

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

## G. Tooling / gate reliability

### G.1 — `iwyu` false-negative: a reduction-leaked QName is reported as a used import

> **This entry is the SINGLE SOURCE OF TRUTH for this bug. Do not describe it anywhere else —
> link here (`DEFERRED_ITEMS.md §G.1`). If a new facet is found, add it to THIS entry.**

- **Where** — `tools/agda-iwyu-reader/Main.hs` (the reader's `used` signals — `usedOf` /
  `resolveQuery`); driver `tools/_iwyu.py`; gate `tools/iwyu.py`. First observed as a missed
  dead import at `src/Aletheia/DBC/TextParser/Properties/WellFormedCheck/Sound/Attr.agda:41`
  (that symptom was fixed in PR #181; the reader gap remains).
- **Origin** — 2026-07-13, PR #181 review: Copilot flagged two dead `using` imports
  (`resolveDefIssues` / `enumDefaultIssue`) that `iwyu` reported clean; root-caused to the
  reader's canonical-QName `used` set.
- **The mechanism (full).** The reader judges a `using (n)` import USED if ANY of its signals
  fire; two matter here:
  - *syntactic* — `n` occurs in source beyond its import, via Agda **highlighting** occurrence
    counts (`resolveQuery`); comments are comment-tokens (not name refs), so a comment mention
    scores 0.
  - *semantic* — `n`'s QName ∈ `namesIn(defsOf)` (the module's **elaborated** definitions;
    `usedOf iface = namesIn (toList (defsOf iface))`).

  The **semantic signal over-fires**: a genuinely-dead import whose QName reaches `defsOf`
  **only by reduction of another imported def** is reported USED. Here `attrIssues-sound`'s
  `DBCAttrAssign` / `DBCAttrDefault` arms do `with (lookupDef …) in eq`, forcing `attrIssues`
  to reduce to `resolveDefIssues … ++ enumDefaultIssue …`, which bakes those QNames into the
  elaborated with-function's type → they land in `namesIn(defsOf)` → USED, though no source
  token ever goes through the `using` alias. This is a **false-negative**; the recompile oracle
  the reader replaced (2026-06-06) would call it DEAD. The tool has itself flagged
  "FN-completeness" as open R&D since that switch — this is a concrete, reproduced instance.
  - *Why removal isn't then flagged MISSING:* the baked-in reference is fully-qualified to the
    origin (`WellFormedCheck.resolveDefIssues`), resolvable via the **transitive** `WellFormedCheck`
    import — the direct alias was never required for it.
  - *Contrast the reader got RIGHT (`AttrDef`, correctly DEAD):* `AttrDef` reaches `Sound.agda`
    only as an *inferred* type argument (`collectDefs`'s result `List AttrDef`), which does NOT
    land in `namesIn(defsOf)` → neither signal fired. So the discriminator is exactly "does the
    QName land in `defsOf`?", and reduction-under-`with` is one way a redundant import's name gets there.
- **Verification (how we know it's the semantic signal, not comment-counting).** Keep the imports
  but mangle ONLY the comment mentions (`resolveDefZZZ`): iwyu STILL reports 0 findings → comments
  are irrelevant; the elaborated-term leak is the sole cause. Ground truth: removing the imports
  type-checks clean AND iwyu-clean, so the import is genuinely dead.
- **Scope — likely SYSTEMIC.** Any `Properties`/proof module that (i) redundantly imports a helper
  by name AND (ii) forces that helper to reduce (`with f x in eq` unfolding `f`) can trip the same
  false-USED. The fix must include a tree audit for other instances.
- **Done looks like** — `iwyu` is **100% exact** = matches the recompile oracle on every case (no
  false-DEAD, no false-USED). A new `--self-test` fixture (`tools/agda-iwyu-reader/test/`)
  reproduces the reduction-leak shape (a `using` name only reduction-introduced into `defsOf` must
  classify DEAD), every existing fixture stays green, and the tree audit is clean.
- **Cost / risk** — Medium R&D. **Risk:** any fix must NOT re-introduce false-DEAD — the semantic
  signal exists to catch the renamed / copy uses the syntactic signal legitimately misses, so
  narrowing it could regress those. Candidate approaches to evaluate:
  1. **Require the alias, not just the QName** — count semantic-USED only when the reference could
     NOT resolve without THIS `using` entry (not already reachable via a transitive module import).
     Uses scope reachability the reader already loads (`scopes` / `moduleResolve`).
  2. **Gate by import kind** — for a plain (non-renamed, non-copy) `using (n)`, trust the syntactic
     signal; let semantic rescue only the renamed/copy cases it exists for. Risk: a plain name
     genuinely used with no highlight token would need care.
  3. **Targeted recompile-confirm** — re-introduce the retired oracle ONLY for the borderline class
     (semantic-USED but syntactic-0). Cheap (few candidates), exact by construction.
  4. **Detect reduction-leaked QNames** — distinguish a QName that entered `defsOf` only via
     another Def's normal form from one the module wrote. Hard in general.
- **Notes.** (a) A tool validated against a synthetic fixture matrix is exact only up to the
  fixtures' COVERAGE — this shape wasn't in the matrix, so the reader passed `--self-test` (31/31)
  with the gap; the fix's fixture closes that hole. (b) Discovery discipline: when a reviewer
  (Copilot) and a gate (iwyu) conflict, the COMPILER (recompile) is the tiebreaker — here the gate
  was the one that was wrong.
- **Blockers / deps** — none; independent of the Agda / proof work.
- **Verdict (first pass)** — `DO` (user directive 2026-07-13: "we need to fix iwyu to be a 100%
  reliable tool").

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

1. **E.2** (`WellFormedTextDBCAgg`) — ✅ re-examined 2026-07-12: no correctness
   gap (confirmed); closure routes scheduled (b) ≫ (a) ≫ (c) with
   adversarially-reviewed proof strategies in
   [E2_PROOF_STRATEGY.md](E2_PROOF_STRATEGY.md).
2. **A.1 / A.3 / B.1** — gated on a concrete consuming DBC / property.
3. **C.1 / D.1 / F.1 / F.2 / H.1** — accepted / blocked / demand-gated; no action unless constraints change (H.1: a public C++ test mock — promote on concrete external-consumer demand).
4. **I.1** (Go/C++ arm64 overflow guard) — target-gated; no action until a concrete non-amd64 embedded target with a verified full cross-toolchain (GHC + clang + rustc) is chosen.

> Each item graduates from this doc to a real task only after a per-item
> decision with the user. This file is the backlog + rationale, not a commitment.
