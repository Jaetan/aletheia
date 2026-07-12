# E.2 proof strategies — index & synthesis (2026-07-12)

**What this is.** The adversarially-reviewed proof strategies for the three closure
routes of backlog item E.2 (`WellFormedTextDBCAgg` runtime discharge — see
[DEFERRED_ITEMS.md](DEFERRED_ITEMS.md) § E.2 for the item itself and the schedule).
Scheduled order: **(b) ≫ (a) ≫ (c)**.

**Method / provenance.** Multi-agent deep-dive, 2026-07-12: per route, lemma-level
landscape readers → a strategy author → an adversarial review panel (2–3 independent
lenses: Agda proof mechanics; repo invariants & build/runtime discipline; contract
completeness & cross-binding product) → a revision pass in which the author had to
accept-or-rebut every criticism with file:line evidence. The route documents are
**rev. 2 (post-panel)**. Panel outcome across the three routes: **zero fatal
findings; 10 major and 41 minor criticisms**, each either absorbed into rev. 2 or
parked below as an explicit user decision. The load-bearing architectural claims of
route (b) (gate scope, `Properties.Equality` already in the runtime `.so`, the
`_≟-DBCSignal_` ceiling) were additionally re-verified first-hand outside the
agent fleet.

## The three routes

| Route | Document | Strategy in one line | Status |
|---|---|---|---|
| **(b)** decision procedure at the format handler | [E2_ROUTE_B.md](E2_ROUTE_B.md) | **Hybrid**: V2 exact check (`roundTripsᵇ` = evaluate `parseText (formatText d)`, deep-compare with `_≟-DBC_`) is the verdict authority — its soundness lemma is **axiom-free**; V1 per-field checker (`wfTextIssues`) is the diagnostics layer; a stitching theorem `wfTextIssues d ≡ [] → roundTripsᵇ d ≡ true` (Substrate trust base) guarantees every divergence ships ≥ 1 diagnostic. Default = format-anyway + issues envelope (non-breaking); opt-in `strict` refusal gates on V2 only, so the sufficient-not-necessary over-refusal caveat dissolves. 3 slices, ~3,000–4,500 LOC. | **Scheduled first** — prerequisite of any text-export-bearing product surface |
| **(a)** lossless extended-mux emission (A.1 → A.3) | [E2_ROUTE_A.md](E2_ROUTE_A.md) | Emit `SG_MUL_VAL_` as a ninth synthesized section on the A.2 `BO_TX_BU_` template (payload parser + `TSMulVal` + `attachMulVal` inverse + Refine compose bridge), with a raw-range carry + finalize gate + typed `input_bound_exceeded` for the range/materialization bound. Removes the `wfps` wall — the one Agg field no other route can touch. Slice A.1 ≈ 2,050–2,750 new + 750–950 restated lines (~1.7–2.1× the A.2 arc); A.3 (nested mux) a separate later slice that rewrites the `MasterCoherent` projection layer. | **Demand-gated design-ahead** — gate fires on *external* `SG_MUL_VAL_` demand only (the in-tree fixture corpus is a coverage instrument, explicitly carved out) |
| **(c)** stronger validator | [E2_ROUTE_C.md](E2_ROUTE_C.md) | **Never standalone** (confirmed: the `wfps` construct is model-legal, wire-legal, engine-honored — an error-class rejection would be wrong; and error-class additions break the load path). Salvage sharpened by the panel round: the repo's sound-lemma shape `check … ≡ [] → P` is severity-independent, so the missing checks ship as **warning-class advisories** whose emptiness carries proof content, yielding **full conditional closure**: `errorIssues (validateDBCFull d) ≡ [] → textRoundTripAdvisories d ≡ [] → WellFormedTextDBCAgg d`, composed in `Substrate/Unsafe.agda` to the round-trip — with zero acceptance change. | **Folded into (b)** — the advisories *are* (b)'s V1 diagnostics |

## How the routes converge

- **(c)-salvage ≡ (b)-V1.** The advisory checks route (c) recommends are the same
  artifact as route (b)'s per-field diagnostics layer; building (b) slice 1 delivers
  (c)'s conditional-closure theorem as a corollary. There is no scenario where (c)
  is built separately.
- **(a) is the only route that shrinks the predicate itself.** (b) makes the
  precondition *observable*; (a) removes its hardest field (`wfps`). After (a),
  (b)'s diagnostics simply stop firing on multi-value-mux DBCs — no rework.
- **E.2's "full closure" remains a composition**: (b) for observability now,
  (a) when external demand fires, never (c) standalone.

## Decisions the user must make

**Route (b) — blocking, decide before slice 1:**
1. Success-envelope severity convention: keep `severity:"error"` on the divergence
   issue inside a `status:"success"` response (severity = finding class), or demote
   to warning on the success path (E2_ROUTE_B.md § 13-3).
2. Naming of the runtime-reachable Dec-equality module:
   `Aletheia.DBC.Properties.Equality.Full` (precedented) vs `Aletheia.DBC.Equality`
   (avoids a Properties name in the runtime closure). Zero content difference.
3. Binding sibling-method naming (`format_dbc_text_result` et al., § 13-2).
4. *(Conditional, low likelihood)* if the S2.1 `dlc-code-inj` spike fails:
   F1 observational setoid vs F2 `.()` migration vs V1-only fallback (§ 7.6).

**Route (a) — decide at gate-fire kickoff (§ 12.3):**
Q1–Q5 (recommendations recorded: a / iii / A-then-B / A.1-alone), the
`max-mux-total-span` constant (suggested 65536), the raw-range-carry (b′)
architecture ratification, BREAKING vs Changed CHANGELOG framing, and the corpus
snapshot flip sign-off.

**Route (c) — decide when (b) slice 1 lands:**
Rust `IssueCode` enum growth policy (`#[non_exhaustive]` vs ratified growth policy
vs BREAKING(Rust)) and `checkMasterCoherence-complete` ship-vs-defer.

## Standing limitations (accepted, documented — not fixable by these plans)

- **Diagnostics are envelope-level, not cause-attributed**: on a V2 divergence the
  non-empty V1 issue set may consist of warnings orthogonal to the actual loss
  mechanism. Wording discipline (E2_ROUTE_B.md acceptance (f)) prevents overselling.
- **The hybrid stitching theorem shares the Substrate trust base** (the two
  String ↔ `List Char` bridging axioms). Only `roundTripsᵇ-sound` — the strict-mode
  verdict authority — is genuinely axiom-free.
- **A.1 without A.3** leaves nested-mux text value-faithful but not
  Vector-canonical, and `SG_MUL_VAL_`-uncovered nested children keep the interim
  parent (E2_ROUTE_A.md § 1.4, § 11).
