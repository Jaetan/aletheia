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
  structurally false today (a valid multi-value-mux DBC is the counterexample)
  and REMAINS false even after A.1/A.3: `attr-wfs`, `wf-sigs`/`pvs`, and
  `unresolved-empty` sit behind warning-class checks by design (error-class
  rejection would break the load path and was rejected). The shipped state —
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
- **Origin** — user proposal during the E.5 scoping analysis: proofs can be
  erased, so `Dec`-shaped APIs need not cost anything at runtime.
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

### E.3 — V1 diagnostic tightness classification (round-trip-necessary vs merely-bundled)

- **Where** — the `wfTextIssues` checker (`src/Aletheia/DBC/TextParser/WellFormedCheck.agda`)
  and the round-trip proof `parseText-on-formatText`
  (`src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda:128`).
- **Origin** — the 2026-07-13 adversarial review of the `wfTextIssues` checker.
  The checker's decision procedure proves `wfTextIssues d ≡ [] ⟺
  WellFormedTextDBCAgg d`, and `WellFormedTextDBCAgg` is
  **sufficient-not-necessary** for round-tripping (it is the antecedent of
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
- **Not blocking any guarantee.** The exact check `roundTripsWithᵇ` dissolves the
  over-approximation for the only decision that needs exactness (the
  `format_dbc_text` refusal gates on the exact re-parse check, never on
  `WellFormedTextDBCAgg` necessity); the `wfTextIssues` diagnostics are already
  worded "round-trip not proven", never "will not". Land anytime — a good fit
  for a multi-agent proof-trace workflow.
- **Verdict** — `SCHEDULED` (quality/tightening analysis, non-blocking).

### E.4 — Comment-quality pass over the E.2-arc modules

- **STATUS ✅ DONE (2026-07-16)** — shipped in the tree-wide comment-quality pass
  #193 (`2597d04c`), whose scope was expanded (user directive) to cover EVERY source
  language, including these E.2-arc modules: incorrect comments fixed (incl. the
  round-trip-theorem claim that dropped its `WellFormedTextDBCAgg` hypothesis) and
  plan-scaffolding + memory-store citations stripped.
- **Where** — the E.2 route-(b) modules: `FormatDBCText.agda`,
  `Protocol/Message.agda`, `Protocol/ResponseFormat.agda`, `WellFormedCheck.agda`,
  `RoundTripCheck.agda`, their `Sound`/`Properties` siblings, and
  `TextParser/Properties/Substrate/Unsafe.agda`.
- **Origin** — user directive 2026-07-15. The slice-3 plan-label scrub was narrow
  (removed "slice N" / "§N" / "V1/V2" only); it left the dense explanatory comments
  otherwise untouched, and the modules accreted their narrative incrementally across
  three slices.
- **Guiding principle** (user 2026-07-15): every comment must be useful to a
  *reader* of the file — it describes the code's **goals** (why it is shaped this
  way) and **rules / invariants** (what a maintainer must preserve). **Nothing
  about the past** (how it evolved, what it used to be, which slice added it, why a
  prior approach failed) and **nothing redundant** with what the code already says.
  History lives in git.
- **Do** — a dedicated pass to (a) fix **incorrect** comments — stale claims that
  drifted from the code (arities, field counts, behaviour that changed across the
  slices, references to a design shape that was later unwound, e.g. the `strict`
  flag); and (b) delete **unnecessary** comments — redundant with the code,
  over-verbose, or historical/plan-scaffolding narrative that outlived its purpose.
  Keep only build-validated code cross-refs (module / function names); comments must
  be self-contained (no CI gate scans `.agda` comment cross-refs).
- **Sequencing** — was gated on the whole E.2 arc landing (slice 3 merged); once it had,
  the pass shipped folded into the tree-wide comment-quality PR #193 (same close, broader
  scope) rather than as the originally-planned standalone PR.
- **Verdict** — ✅ **DONE** (2026-07-16, #193); see STATUS above.

### E.5 — Reify Bool-valued checker leaves into `Dec`/`Reflects`

- **STATUS ✅ DONE (2026-07-18)** — all 8 Bool leaves reified into stock relevant
  `Dec` deciders consumed via the shared `requireDec` combinator (`isAlways?` /
  `masterOk?` / `whenOk?` / `mcGo?` / `masterCoherent?` in the master cluster;
  `vmt?` / `enumOk?` / `wfAttrType?` in the attribute cluster); `Sound/Master.agda`
  (125 L of hand-written Bool-reflection pairing) deleted outright and
  `Sound/Attr.agda` cut 193→77 L, the shared `requireDec-sound/-complete` replacing
  every deleted pairing lemma. Wire-frozen (same issues, codes, order — verified by
  real-`.so` probes on both branches of every decider) and theorem-frozen
  (`wfTextIssues-sound/-complete` statements byte-identical). Predicates that the
  runtime checker now decides moved to closure-light non-`Properties` homes
  (`Formatter.WellFormedText.Foundations`, `TextParser.WellFormedAttr`) with
  `open … public` re-exports keeping every proof-side consumer unchanged.
- **Where** — the Bool-valued leaves of the `wfTextIssues` checker tree:
  `isAlwaysᵇ`, `masterOkᵇ`, `whenOkᵇ`, `mcGo`, `masterCoherentᵇ`, `vmtᵇ`,
  `enumOkᵇ`, … (`src/Aletheia/DBC/TextParser/WellFormedCheck.agda` and its
  `Properties/WellFormedCheck/Sound*` lemma tree).
- **Origin** — user directive 2026-07-13, gated on the always-strict
  `format_dbc_text` arc landing (it has).
- **Today** — each leaf is a plain `Bool` with a separate hand-written
  soundness lemma in the `Sound*` tree pairing it back to the predicate.
- **Done looks like** — leaves return `Dec`/`Reflects` (or proof-carrying
  results), so the pairing lemmas shrink or vanish; checker behavior
  unchanged (proof-hygiene refactor only).
- **Cost / risk** — Medium; touches the `WellFormedCheck` proof tree; keep the
  hot path Bool-valued where MAlonzo allocation matters (the checker runs
  per-`format_dbc_text` call, not per-frame — `Dec` cost is acceptable here).
- **Verdict** — ✅ **DONE** (2026-07-18); see STATUS above.

### E.6 — Consolidate the two `lookupDef` clones (SSOT)

- **STATUS ✅ DONE (2026-07-18)** — the single definition lives in the new
  `Aletheia.DBC.AttrLookup` module (depends only on `DBC.Types` + stdlib); both
  attributes modules re-export it (`open … public`) so every consumer's import
  path still works, the two clones are deleted, and the
  `parser-eq-formatter-lookupDef` bridging lemma vanished with them (the two
  sides are now definitionally one symbol).
- **Where** — `src/Aletheia/DBC/TextFormatter/Attributes.agda:92` and
  `src/Aletheia/DBC/TextParser/Attributes.agda:576` — two textually identical
  `lookupDef : List Char → List AttrDef → Maybe AttrDef` definitions.
- **Today** — the formatter and parser each carry their own copy; a change to
  one can silently diverge from the other.
- **Done looks like** — one shared definition (natural home: a common
  attributes module both import), clones deleted; any proof mentioning either
  re-pointed.
- **Cost / risk** — Low; watch the import graph for cycles (the cycle-break
  pattern applies if one arises).
- **Verdict** — ✅ **DONE** (2026-07-18, folded in alongside E.5 as planned);
  see STATUS above.

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

- **STATUS ✅ DONE (2026-07-16)** — fixed in the reader, validated against the recompile oracle
  on every case, and the tree audit found **20 dead imports** (across 7 modules) that the gate had
  been reporting clean; all 20 are removed. `--self-test` passes (`tools/iwyu.py --self-test`
  reports the tally; it totals `manifest.tsv` + `wildcard_manifest.tsv`). The rows added are two
  GUARDS, each verified to fail when the rule it pins is removed — `ConsumerLeak`'s `inner` (DEAD;
  read USED before this fix) and `ConsumerAmbigTerm` (USED; DEAD without the overloaded-name rule)
  — plus the controls `ConsumerLeak`'s `outer`, `ConsumerAmbigPat` and `ConsumerAmbigDead`, which
  pass either way and pin surrounding behaviour rather than guard a rule.
  The fix is two rules in `Main.hs`:
  1. *Ambiguity decides how far the semantic signal may be overruled.* Highlighting attributes a
     token to the one QName it resolved to, so the per-QName counts only add up for a name with a
     SINGLE value resolution. Measured on `Data.List`'s `[]` (ambiguous with
     `Data.List.Base.InitLast.[]`): `Aletheia/DBC/Validity/ErrorChecks.agda` uses `[]` 3× in term
     position and its highlight map holds **no `Agda.Builtin.List` entry at all**, while `length`
     in the same file counts a clean 3. So for an ambiguous name a 0 count means "unreadable", not
     "unused", and the semantic signal is taken at face value.
  2. *For a legible name, a hit in the used-set counts only if elaboration had to SEARCH THE SCOPE
     for it* — i.e. the name is an **instance** (`defInstance`), or it is reached by copy
     delegation. Every other token-less occurrence is reduction debris: fully qualified, resolvable
     through the transitive import, keeping no scope entry alive.
- **Findings that correct the diagnosis below** (kept because they cost real measurement):
  - The leak is **not confined to with-function TYPES**. Restricting the semantic set to clause
    bodies/patterns found only 9 of the 19 known-dead; the other 10 (e.g. `clearVds`, named
    nowhere but in comments) reach clause **bodies** too. Where the QName lands is not the
    discriminator; *why* it is there is.
  - **Candidate 2 as written is wrong**: "for a plain `using (n)`, trust the syntactic signal"
    regresses INSTANCE uses to false-DEAD (`ConsumerInstUsed` catches it immediately) — an
    instance never has a source token yet always needs its import.
  - **Candidate 3 buys nothing here**: every genuinely-dead import in the tree is unambiguous, so
    recompile-confirm would spend ~8 s/module covering a class with no instances. No oracle exists
    in the driver to reuse either (the header comment claiming one was stale; corrected).
  - **The recompile oracle is unsound as stated** ("removing the imports type-checks clean … so
    the import is genuinely dead"). Dropping a constructor from a `using` list turns its PATTERN
    occurrences into fresh pattern VARIABLES: it type-checks clean and silently changes semantics.
    Proven on `Parser/Position.agda` — removing `[]` made `advancePositions pos [] = pos` match
    every list and orphaned the `_∷_` clause, exit 0, betrayed only by an `UnreachableClauses`
    warning. **A sound oracle must treat any new warning as USED.**
- **Residual (accepted, safe direction)** — an AMBIGUOUS name whose QName reached the signature
  only by reduction still reads USED: the syntactic signal cannot see it and the semantic one
  cannot tell it from a real use. That errs toward KEEPING an import (a missed cleanup, never a
  bad removal). Zero instances in the tree today. Closing it needs the recompile-confirm of
  candidate 3, scoped to ambiguous borderline names only.
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
- **Verdict** — ✅ **DONE** (2026-07-16); see STATUS above. Raised by the user directive
  2026-07-13: "we need to fix iwyu to be a 100% reliable tool".

### G.2 — Reserve the `.Properties` namespace for proofs; move decision procedures to `.Decidable`; make `check-no-properties-in-runtime` an exact closure gate

> **This entry is the SINGLE SOURCE OF TRUTH for this refactor. Do not describe it elsewhere —
> link here (`DEFERRED_ITEMS.md §G.2`).**

- **STATUS ✅ DONE (2026-07-15)** — shipped as its own PR off `main`. `DBC.Decidable.*`
  holds the deciders (the equality tower, the disjointness/well-formedness data + `?`
  procedures, the Bool overlap check); `DBC.Properties.*` holds only the proofs
  (symmetry, soundness/completeness, proof extraction). The cabal `other-modules`
  closure lists 441 MAlonzo modules with **zero** `DBC.Properties.*`; the rewritten
  `check-no-properties-in-runtime` gate asserts exactly that against the closure.
  Module count 287→290. The plan below is retained for reference.
- **Origin** — the E.2 route-(b) slice-3 adversarial review, finding D: `check-no-properties-in-runtime`'s
  comment claimed it keeps proofs out of the runtime `.so`, but the gate only greps the 4 handwritten
  runtime ROOTS (Main / Main.JSON / Main.Binary / Handlers.agda) for DIRECT `.Properties` imports — a
  narrow, mis-targeted proxy. Re-examination (2026-07-15) rejected two dead ends before landing here:
  a closure-level ALLOWLIST (name-matching can't classify lemma-vs-Dec; duplicates cabal `other-modules`;
  fires on every legit new Format module), and papering over via a comment. The user chose to fix the
  underlying **failure F3**: *a computational decision procedure is misfiled under a proof namespace.*
- **What we want** — the `Aletheia.DBC.Properties.*` namespace RESERVED for proofs (standalone lemmas),
  so "no `Aletheia.DBC.Properties.*` module in the `.so` closure" is an invariant that is both TRUE and
  exactly enforceable. Runtime consumes decision procedures from a new computational namespace `DBC.Decidable.*`.
- **Out of scope (documented exception, NOT a leak)** — the Format-DSL proofs under
  `TextParser.*.Properties.*` (`Primitives`, `Preamble.Newline`, `Attributes.Assign.Common`,
  `DecRatParse.Properties`) are genuine proofs that ride in the runtime `.so` closure BY DESIGN: the
  proof-carrying Format DSL (`iso`/`refined`) bundles a printer+parser with its round-trip proof
  (`@0`-erased in the binary, but the module is in the import graph via `Format.agda`, which Main reaches
  through `parseText`). No naming scheme removes these without gutting the verified-by-construction DSL.
  So the gate is scoped to `DBC.Properties.*` — the namespace we actually disambiguate — NOT all `.Properties`.
- **Plan (scoped; advisor-reviewed 2026-07-15).** Naming: computational modules → `DBC.Decidable.*`.
  - **Pure renames** (all-computational): `DBC.Properties.Equality` → `DBC.Decidable.Equality`;
    `DBC.Properties.Equality.Full` → `DBC.Decidable.Equality.Full` (`dlc-code-inj` is an internal helper
    for `_≟-DLC_`, travels with the tower). Preserve `Equality`'s `private` block and keep `_≟-vd_` **public**.
  - **Splits** (mixed → Dec part + residual proof part): `Disjointness` and `WellFormedness` each split
    into `DBC.Decidable.X` (data + `Dec`s + Bool helpers) and residual `DBC.Properties.X` (the
    `-sym`/`-false-absent` lemmas — confirmed imported ONLY by `CAN/Batch/Properties/{Capstone,Roundtrip}`
    proofs, never by runtime, so they genuinely leave the closure).
  - **Facade split**: `DBC.Properties` (today re-exports both, and is BOTH a runtime import AND a
    proofModules root) → `DBC.Decidable` (re-exports Decs, runtime) + residual `DBC.Properties`
    (re-exports lemmas, proof root).
  - **Route ~12 importers by `using`-clause name** (grep each up front; dual-users get both imports):
    runtime (`RoundTripCheck`, `Validator/Checks`, `BatchFrameBuilding`, `Validity/*`) → `.Decidable`;
    proof (`Capstone`, `Roundtrip`, `Substrate/Unsafe`) → `.Properties` for lemmas.
  - **`proofModules`** (Shakefile.hs): `.Decidable.*` leave (build-checked in Main's closure); residual
    `.Properties.*` + the `.Properties` facade become/stay proof roots; keep `check-proof-coverage` green.
  - **`gen-ffi-modules` + `aletheia.cabal`** regenerated; **gate rewrite**: `check-no-properties-in-runtime`
    → assert cabal `other-modules` contains zero `MAlonzo.Code.Aletheia.DBC.Properties.*`; document in the
    gate WHY it is scoped to `DBC.Properties.*` (the Format-DSL exception above).
- **Acceptance test (done ≠ type-checks)** — after `gen-ffi-modules`, `aletheia.cabal` `other-modules`
  lists **zero** `Aletheia.DBC.Properties.*`, and the new gate passes against it. Any residual `.Properties.*`
  still in the closure = a runtime path still reaches it = the split is incomplete (this is also the honest
  self-test that it was a real split, not relabeling).
- **Watch** — renamed modules get new MAlonzo mangled names (build's drift detector prints `sed` fixes; run
  them); `check-fidelity` stays green; `check-ffi-exports` holds at 47 (export SET unchanged — verify).
- **Blockers / deps / SEQUENCING** — **must land AFTER E.2 route (b) (slice 3), as its own PR off `main`
  (user decision 2026-07-15, "Option 1").** F3 and the uncommitted slice-3 work both edit `Shakefile.hs`
  (`proofModules`) and `aletheia.cabal` (`other-modules`), which this env can only stage per-file → they
  cannot be un-bundled after interleaving; and F3 renames `Equality.Full`, which slice-3's `RoundTripCheck`
  imports. So finish slice-3, land it, then F3 rebases cleanly on top.
- **Verdict** — ✅ **DONE** (2026-07-15); see STATUS above.

### G.3 — Cross-binding `IssueCode` completeness parity test

- **Where** — the per-binding issue-code enumerations (`python/aletheia/codes/_issue.py`,
  Go/C++/Rust counterparts) vs the kernel's `formatIssueCode` arms
  (`src/Aletheia/Protocol/ResponseFormat.agda`).
- **Today** — per-binding parity tests check the codes each binding *uses*;
  no gate asserts every kernel-emittable issue-code string is *known* to every
  binding, so a new kernel code can reach a binding as an unknown string
  without failing CI.
- **Done looks like** — a completeness gate (per binding, or one matrix-style
  test) that enumerates the kernel's emittable issue codes and fails when any
  binding's enum lacks one. Follows the gate-teeth rule: inject a fake code
  and assert the gate fails.
- **Cost / risk** — Low-medium; needs a machine-readable SSOT for the kernel's
  code list (generate from `ResponseFormat.agda`, or a checked snapshot like
  `ffi-exports.snapshot`).
- **Verdict** — `SCHEDULED` (test-gap candidate; pairs naturally with H.2's
  enum-growth decision).

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

### H.2 — Rust `IssueCode` enum-growth policy (`#[non_exhaustive]`?)

- **Where** — `rust/src/response.rs:156` (`pub enum IssueCode`).
- **Today** — the enum is **not** `#[non_exhaustive]`, so every future
  issue-code addition is a source-breaking change for downstream crates doing
  exhaustive matches (each addition forces a major-version signal under the
  project's SemVer pledge).
- **The decision** — adopt `#[non_exhaustive]` (one breaking change now;
  future additions become non-breaking, downstream must carry a `_` arm) vs
  keep exhaustive matching (maximal compile-time coverage for consumers, at
  the price of a breaking release per new code). Same question applies to
  `ErrorCode` if it shares the shape.
- **Cost / risk** — Trivial mechanically; the cost is the API-policy choice.
  Decide before the next Rust-facing release that adds a code.
- **Verdict** — `SCHEDULED` (decision item; pairs with G.3).

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

1. **G.3 / H.2** — scheduled, cheap, self-contained (the pair remaining in this
   tier now that E.5 / E.6 are ✅ done — see their entries).
2. **E.3** — scheduled, non-blocking tightness analysis; land anytime.
3. **A.1 / A.3 / B.1** — gated on a concrete consuming DBC / property.
4. **C.1 / D.1 / F.1 / F.2 / H.1** — accepted / blocked / demand-gated; no action unless constraints change (H.1: a public C++ test mock — promote on concrete external-consumer demand).
5. **I.1** (Go/C++ arm64 overflow guard) — target-gated; no action until a concrete non-amd64 embedded target with a verified full cross-toolchain (GHC + clang + rustc) is chosen.

> Each item graduates from this doc to a real task only after a per-item
> decision with the user. This file is the backlog + rationale, not a commitment.
