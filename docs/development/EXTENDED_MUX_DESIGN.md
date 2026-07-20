> **Provenance** — rev. 2 (post-adversarial-panel) design-ahead plan for
> lossless extended-mux text emission, produced 2026-07-12 by a multi-agent
> deep-dive. This is the maintained design plan for
> [DEFERRED_ITEMS.md](DEFERRED_ITEMS.md) **§ A.1 / § A.3** (its lifecycle
> follows those items; internal "E.2 route (a)" labels in section prose are
> historical — they name the closed backlog item this plan originated under).
> File:line references are pinned to the 2026-07-12 tree; the always-strict
> `format_dbc_text` work has since added `WellFormedTextPresence`/`wfps`
> consumers (`WellFormedCheck.agda`, `Properties/WellFormedCheck/Sound.agda`,
> `Sound/Signal.agda`) that post-date §5.6's deletion inventory — run the §12.3
> re-verification pass against the current tree before executing.

# Lossless Extended-Mux Text Emission (A.1 → A.3)
## Design-ahead plan, demand-gated (rev 2, post-panel)

**Status**: DESIGN-AHEAD. Not to be executed until the trigger (§12) fires. All file/line citations verified against the working tree 2026-07-12 (`main`, post-#176); rev 2 incorporates the adversarial-panel findings (bound-design rework, fixture-flip obligations, cascade completions). Re-run the §12.3 re-verification pass before execution — the proof layer has parallel doc-comment edits in flight (WellFormed.agda, FormatDBCText.agda, WellFormedFromValidity.agda).

**Goal**: make `formatText` emit `SG_MUL_VAL_` lines so multi-value `When` selectors survive the text round-trip, deleting the `wfps` field from `MessageWF` and the `presence-wf` field from `SignalLineWF` — the one `WellFormedTextDBCAgg` wall no other E.2 route can touch. Slice A.1 (multi-value, single-master) is fully planned; slice A.3 (nested `m<N>M`) is sketched with its architectural prerequisites (§9).

**Headline theorem after slice A.1** (statement TEXT unchanged, predicate strictly weaker):

```agda
parseText-on-formatText :
    ∀ (d : DBC) → WellFormedTextDBCAgg d
  → parseText (formatText d) ≡ inj₂ d
```
(`src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda` — the only allowlisted Unsafe module; untouched by this arc except re-type-checking.)

---

## 1. Verified ground truth (deltas vs. the landscape inventory; rev-2 additions marked ★)

1. **`SendersCompose.agda` needs ZERO edits** (landscape budgeted ~40–80 diff lines). If `attachMuxVals` is nested **innermost** in `buildDBC`, the new `MuxCompose` module proves `attachMuxVals (collectMuxVals msgs) (map clearAllMsg msgs) ≡ map clearBothMsg msgs` and then *chains the existing* `attachSenders-attachValueDescs-on-clearBothMsgs-collected` (SendersCompose:149-160) verbatim. Its opaque-`MessageWF` design (:40-44) survives the `wfps` removal untouched.
2. **`mc-mux` is already values-independent**: its all-When clause (`WellFormedText.agda:150-153`) quantifies over arbitrary `vs : List⁺ ℕ`. Slice A.1 does not touch `MasterCoherent` at all.
3. **The `'S'∷'G'` head bucket is a single parser** (`TopLevel.agda:204-205, 219`): `parseTopStmt-SG = parseSigMulVal *> pure TSSigMulVal`. The new dispatcher slim needs **no** `alt-left-just` arbitration — strictly cheaper than the TBO slim.
4. **★ Nested third-party files: A.1 fixes parent-binding at runtime for `SG_MUL_VAL_`-COVERED `When` signals only** (unproven, but behaviorally right for those): the attach *overwrites* a matched signal's presence with the true `(parent, values)` pair, erasing `resolvePresence`'s interim first-master binding. A nested child that carries only an `m<v>` marker and NO `SG_MUL_VAL_` line keeps the interim (possibly wrong-parent) binding — no regression vs today, and such a line-less nested child is ambiguous in the wire format itself (the `m<v>` marker names no parent), but "parses correctly" must not be claimed for it. Additionally, A.1's formatter emits no `m<N>M` markers (emitMuxMarker-chars has no such arm — `TextFormatter/Topology.agda:145-148`): nested DBCs round-trip **value-faithfully through aletheia** (verified by hand on the `multiplexing.dbc` shape — the emitted `SG_MUL_VAL_` lines carry all parent/value truth) but the emitted text is **not Vector-canonical** for third-party consumers until A.3. Both caveats are §7 doc obligations and §11 non-goals.
5. **Definitional-reduction traps in the degenerate-range path**: on open `v`, `v ∸ v` and `v ≤ᵇ v` are both **stuck** (each recurses on a constructor of the open variable). Every degenerate-case lemma (§5.5) discharges them via `n∸n≡0` (`Data.Nat.Properties`) and `≤⇒≤ᵇ ≤-refl` + Reflects/`T`-conversion — **never by `refl`, including the head case of `expandRanges⁺-degenerate`** (rev 2 fix: the rev-1 text wrongly called that head case definitional), and never by `rewrite` inside a parser-bearing goal (`feedback_no_rewrite_over_parser_goal`). `0 ≤ᵇ k ≡ true` IS definitional (`0 ≤ᵇ k = 0 <ᵇ suc k`, second `<ᵇ` clause), which the §5.8 finalize-gate reduction exploits.
6. `IdentHeadNonHSpace` (used by `name-pre`/`send-pre`) is the right per-line stop carrier for the two identifiers on the `SG_MUL_VAL_` line; it derives **unconditionally** from intrinsic `Identifier` validity (`identNameStop`, WellFormedFromValidity.agda) — so the new typed-shadow WF arm costs **zero new `WellFormedTextDBCAgg` fields**.
7. **★ The typed-bound envelope already exists on this exact path, twice**: (i) `Protocol/Handlers/ParseDBCText.agda:64-72` rejects oversize input with `InputBoundExceeded InputLengthBytes …` before invoking `parseText`; (ii) the **post-parse adversarial bound cascade** lives in `Protocol/Handlers/LoadDBC.agda:60-121` (array-cardinality + string-length walks over the parsed DBC), emitting the double-`WithContext` envelope `WithContext cmdCtx (WithContext fieldCtx (InputBoundExceeded kind obs lim))` (`boundErrorResponse`, :117-121) that all four bindings already lift (#107/#152). The revised Q4 reuses this exact wire shape. Note the LoadDBC cascade has **no walk over `multiplex_values` today** — a defense-in-depth walk there is proof-free (handlers are outside the `parseTextChars` round-trip) and is queued as an optional §7 item.
8. **★ Error-envelope facts** (grounding Q4): `DBCTextParseError` = `ParseFailure | TrailingInput | AttributeRefinementFailed` (`Error.agda:382-395`); per-ctor wire codes via `dbcTextParseErrorCode` (:416-418); top-level `Error.InputBoundExceeded : BoundKind → ℕ → ℕ` with code `"input_bound_exceeded"` (:441, :464). `bound_kind` is a **passthrough string** in the bindings (Python `types.py:542` `NotRequired[str]`; Rust `error.rs` lifts it as `String`; C++ `limits.hpp` keeps named `bound_kind_*` string constants — a new kind is one additive constant), so a new `BoundKind` is wire-additive, not breaking.
9. **★ The self-authored corpus already exercises this surface with drop-semantics pinned**: `python/tests/fixtures/dbc_corpus/multiplexing.dbc:20` has `SG_ SecondaryMux m0M` (nested marker) and `:24-25` have `SG_MUL_VAL_ 200 LeafSignalX SecondaryMux 0-2;` / `… LeafSignalY SecondaryMux 3-5, 10-12;`; `kitchen_sink.dbc:90-91` has degenerate lines `0-0`/`1-1`. `parity_snapshots/multiplexing.json:148-205` pins today's interim binding (`SecondaryMux`/`LeafSignalX`: `PrimaryMux`,`[0]`; `LeafSignalY`: `PrimaryMux`,`[1]`), consumed by three binding suites (`python/tests/test_dbc_corpus_parity.py`, `go/aletheia/dbc_corpus_parity_test.go`, `cpp/tests/dbc_corpus_parity_tests.cpp`). A.1 flips the two leaf rows — a planned §7 deliverable, mirroring A.2's kitchen_sink regen. `examples/example.dbc` is NOT on this surface (its only `SG_MUL_VAL_` occurrence is the tab-indented `NS_` keyword-list entry at :29; no statements, no `m<N>M` markers). The corpus README's known-divergences section (`README.md:52+`) does not currently document the SG_MUL_VAL_ drop — a pre-existing doc gap noted in §7.
10. **★ `check-no-properties-in-runtime` is narrower than rev 1 claimed**: the gate (`Shakefile.hs:581-599`) greps exactly four root files (`Main.agda`, `Main/JSON.agda`, `Main/Binary.agda`, `Protocol/Handlers.agda`) for direct `^open import .*\.Properties` lines — no transitive closure, no other modules. The no-Properties-in-MAlonzo discipline for other runtime-reachable modules is **convention, not machine-checked**; `Format/MessageSenders.agda` (runtime-reachable) imports both `DecRatParse.Properties` (:53-54) and `Properties.Attributes.Assign.Common` (:60-61). `Format/MuxVals.agda` may import the analogous stop/`SuffixStops` lemmas, and should keep the set minimal by convention (the MAlonzo-bloat cost is real even though ungated).

---

## 2. Decisions required BEFORE execution (user calls — complete set, annotated)

Per `feedback_advisor_not_user_proxy` / `feedback_dont_prefilter_decision_scope`: all options listed; recommendations marked, nothing pruned.

### Q1 — Range data model
`SG_MUL_VAL_` carries inclusive value **ranges** (`3-5,10-12`); the model carries discrete values (`SignalPresence.When : Identifier → List⁺ ℕ`).

| Option | Wire impact | Proof cost | Verdict |
|---|---|---|---|
| **(a) Keep `List⁺ ℕ` in the model; `RawMuxVal` carries raw ranges; canonical emit = degenerate per-value ranges `v-v` in model order** | **Zero.** JSON `{"multiplexor", "multiplex_values": [ℕ…]}` untouched; all 4 bindings + CLIs untouched | Codec inverse (`expandRanges⁺-degenerate`, ~30 lines incl. the stuck-`∸` discharge) consumed at the attach-recover layer; no sortedness invariant | **RECOMMENDED** |
| (b) Keep `List⁺ ℕ`; emit merged ranges (`3-5` for `3,4,5`) | Zero wire, but `expand ∘ compress ≡ id` needs a sorted/dedup refinement invariant `List⁺ ℕ` does not carry (G-A21 / `CanonicalReceivers`-class new refinement) | ~400+ lines + a new Agg-visible precondition — an E.2 **anti-goal** | Reject unless byte-pretty output is demanded |
| (c) Model-level ranges (`When : Identifier → List⁺ (ℕ × ℕ)`) | **BREAKING 4-binding wire change** (Go `json.go`, Rust `dbc.rs`, C++ `types.hpp`/serialize, Python TypedDict, both CLIs, FEATURE_MATRIX gates) for zero semantic gain — the JSON path is already faithful | Massive | Reject |

Byte-identity of emitted text is explicitly not a target (`TextParser.agda:12-13` stance); `v-v,v-v` is uglier wire but is what the proof wants — and degenerate ranges have **span 0**, the load-bearing fact for Q4.

### Q2 — Collection policy (which `When` signals get an `SG_MUL_VAL_` line)
| Option | Consequence |
|---|---|
| **(iii) Uniform: one line per `When` signal, every message** | Attach = total overwrite of every `When` presence. The head-`m<v>`-marker/`SG_MUL_VAL_` double-emission coherence obligation **dissolves** (replace semantics); the cleared form is the uniform `truncPresence`; Layer-A lookup discipline identical to VAL_. Extra lines on legacy single-value DBCs (semantically inert on reparse; cantools parses them). **This is also the property that makes A.3 cheap later** (§9) and covered-signal nested runtime-correctness free now (§1.4). **RECOMMENDED** |
| (i) Minimal: only `values` tail ≠ `[]` | Byte-stable output for legacy single-value DBCs, but attach becomes conditional per signal, the cleared-form projection piecewise, and A.3 must revisit (nested children with singleton values NEED lines) — significant extra proof surface |
| (ii) Per-message all-or-nothing | Intermediate; inherits (i)'s conditional collect at message granularity |

### Q3 — Unresolved `SG_MUL_VAL_` entries (line names a nonexistent (canId, signal))
| Option | Consequence |
|---|---|
| **(A) Slice-1: silent no-op at attach** (the `attachSenders` precedent — BO_TX_BU_ has no unresolved surface either) | No new DBC field, no wire audit, no new validator check. Data on a dangling line is dropped without diagnostic |
| (B) Full VAL_ mirror: `DBC.unresolvedMuxVals : List RawMuxVal` + a new warn-class validator check `UnknownMuxAssignTarget` (next number in the append-only CHECK sequence — 24/25 are taken by the round-trip mirror checks) + Agg field `unresolved-mux-empty` + JSON `parseOptionalArray` default-`[]` + 4-binding typed field + FEATURE_MATRIX row + parity tests + PROTOCOL.md error table (G-A23 full wire-boundary audit; `RawMuxVal` must then live in `Types.agda` like `RawValueDesc`). **Additionally (rev 2): a new `DBC` record field changes the MAlonzo constructor arity — re-verify the Haskell shim's Agda-value construction/consumption (`haskell-shim/src/AletheiaFFI/Marshal.hs`) and re-run `check-fidelity` (constructor-drift smoke test) + `check-erasure`; budget for updating their expectations. The gates exist precisely to catch this drift class** | The single biggest scope multiplier in the arc. The round-trip proof itself never needs it (collect-side entries always resolve) |

**Recommended**: (A) for the proof slice, (B) as an explicitly queued follow-on slice in the same arc (validate-strict / refine-permissive philosophy argues for (B) eventually; demand gating means we will have real files to test it against).

### Q4 — Bound design for range materialization (AGENTS cat 32, mandatory) — REWRITTEN rev 2

**The threat is the product, not the single range.** `max-dbc-text-bytes = 67108864` (64 MiB, `Limits.agda:92-93`). A max-span range under rev 1's per-range cap (`0-1024,` ≈ 7 bytes) costs 1025 materialized ℕ per ~7 input bytes: an *accepted* adversarial file materializes ≈ (64 MiB / 7) × 1025 ≈ 10¹⁰ values — hundreds of GB of MAlonzo heap on the 62 GiB host. Any per-range or per-line constant multiplies an input-linear count by that constant; only a **file-cumulative** bound caps the amplification. This is exactly the AGENTS.md:46 failure mode ("a verified-terminating parser … will still produce a 10⁷-element list that exhausts heap downstream").

**Two independent checks, split by kind** (this split is what reconciles the CAN-ID precedent with the cat-32 letter):

1. **Wire validity — `lo ≤ hi` per range**: parser-internal `fail` in the promotion wrapper (`buildMuxValResult`), positioned `ParseFailure` at the line. This is the exact `parseBOTxBu`/`buildCANId` precedent (`TopLevel.agda:124-133`) — a malformed-data rejection, not a resource bound, so the typed-`InputBoundExceeded` rule does not apply to it. Out-of-range CAN IDs reject the same way (via `buildCANId`).
2. **Resource bound — cumulative span per file**: `totalMuxSpan ≤ max-mux-total-span`, where `totalMuxSpan = Σ over all SG_MUL_VAL_ ranges of (hi ∸ lo)`, checked **pre-expansion**. Rejection is the **typed** `InputBoundExceeded` (AGENTS.md:46 letter), surfaced through the existing double-`WithContext` envelope (§1.7) so the four bindings' existing lifts fire — see mechanism below.

**Mechanism (the architecture change that makes pre-expansion checking possible)**: `RawMuxVal` carries **raw ranges** (`(ℕ×ℕ) × List (ℕ×ℕ)` — exactly the `muxRangeListFmt` value shape); expansion to `List⁺ ℕ` moves from the parser to the **attach** inside `buildDBC`. `finalizeParse` gates on `totalMuxSpan (CollectedTop.rawMuxVals collected) ≤ᵇ max-mux-total-span` between `partitionTopStmts` and the refine/build tail (helper-split per `feedback_expose_scrutinee_for_external_rewrite`; a plain `if`, not `with … in` — avoiding `feedback_with_in_eq_outer_abstraction_barrier`), returning a new typed arm `MuxSpanBoundExceeded : ℕ → ℕ → DBCTextParseError` on violation; `handleParseDBCTextResult` unwraps that arm to `WithContext "ParseDBCText" (WithContext "multiplex value ranges" (InputBoundExceeded MuxRangeSpanTotal obs lim))` — byte-identical wire shape to the LoadDBC cascade's `boundErrorResponse` (§1.7), so **zero binding code changes** beyond one additive C++ `bound_kind_*` constant + parity tests. New `BoundKind` ctor `MuxRangeSpanTotal` (code `"mux_range_span_total"`) in `Limits.agda`.

Placement rationale vs `feedback_handler_vs_parser_bound_placement`: the memory's default is handler-boundary because parser-internal checks shatter *existing* roundtrip proofs. Here the handler cannot see raw ranges (post-parse = post-expansion — too late; MAlonzo laziness is not a bound guarantee since the stored DBC retains the forced lists), so the check sits at the **finalize** layer — outside every parser-combinator body (no combinator roundtrip lemma is touched; the finalize-stage proof gains one rewrite, §5.8), which preserves the memory's actual rationale.

**Why the round-trip stays Agg-field-free (the key trick, unchanged in spirit)**: canonical emission is degenerate `v-v` ranges (Q1a), so `totalMuxSpan (collectMuxVals msgs) ≡ 0` for EVERY model DBC (`totalMuxSpan-collect`, §5.5), and `0 ≤ᵇ limit` is definitional — the gate can never trip on formatter output regardless of the constant. A total-**values**-count bound would NOT have this property (collected count = Σ|values| ≠ 0) and would cost a new Agg wall — rejected as an E.2 anti-goal; listed for completeness.

**Memory-budget derivation for the constant** (the derivation rev 1 lacked): pre-gate, a hostile file holds only raw `(lo,hi)` pairs — input-linear. Post-gate, an accepted file materializes ≤ `#ranges + totalMuxSpan` values ≤ `(max-dbc-text-bytes / 4) + max-mux-total-span` ≈ 16.8M + constant (each range costs ≥ ~4 wire bytes). At ~40-80 bytes per MAlonzo cons+Integer, the input-linear term is ~0.7–1.4 GB transient — the same resource class as the parser's own 64 MiB `List Char` materialization (~1.5–2.5 GB), i.e. **no amplification beyond input-linear**; the amplification term is capped at `max-mux-total-span` values (**~3–5 MB at the suggested 65536**). Suggested `max-mux-total-span = 65536` (2¹⁶ — generous for real extended-mux files, whose spans are mode-selector-sized; **user call**). PROTOCOL.md § Limits row + error-table row required.

| Option | Verdict |
|---|---|
| **(b′) As above: raw-range carry + finalize cumulative-span gate + typed `InputBoundExceeded`; per-range `lo≤hi` stays parser-internal** | **RECOMMENDED** — satisfies AGENTS.md:46's letter (typed error, offending field, limit) AND its substance (bounded heap), zero Agg field, zero binding logic changes |
| (a) rev-1 shape: per-range span cap, parser-internal `fail` for both checks | Violates AGENTS.md:46's letter for a resource bound (positioned `ParseFailure` carries no field/limit) AND its substance (product amplification, above). Choosing it anyway requires BOTH a documented exception in PROTOCOL.md § Limits AND a budget-derived tiny constant (≈4–16, which rejects legitimate `0-255` ranges) — present only as a documented-exception request needing explicit user sign-off; **not recommended** |
| (c) File-total expanded-**values** bound | Bounds memory but trips on formatter output → new Agg field (`total-values-bounded`) = a new E.2 wall the validator doesn't check. Anti-goal; reject unless the user prefers count-semantics on the wire |
| Optional add-on (either way): LoadDBC cascade walk over `multiplex_values` cardinality | Defense-in-depth covering the JSON route too; proof-free (handlers are outside `parseTextChars`); pairs with a cross-route symmetry check of the JSON array-cardinality bound at execution |

**Positioning trade-off to flag**: the typed bound error carries no line position (matches the input-length gate precedent, and the bound is a whole-file property); the validity rejects (inverted range, bad CAN ID) DO carry byte-exact positions.

### Q5 — Slicing
**Recommended**: ship A.1 alone (this document's §§3–8), A.3 as a separate later slice (§9). A.3 invalidates the single-master Resolve architecture; entangling it would blow the reviewable-unit size past the `feedback_step_back_when_proofs_balloon` threshold by design.

---

## 3. Slice A.1 — canonical wire form and semantics

**Grammar** (already in `TextParser.agda:150-152` §F — unchanged):
```
sig-mul-val ::= "SG_MUL_VAL_" ws nat ws identifier ws identifier ws
                mux-range ("," ws? mux-range)* ws? ";" newline
mux-range   ::= nat "-" nat
```
**Canonical emission** (one line per `When` signal, policy iii; degenerate ranges, Q1a):
```
SG_MUL_VAL_ <rawCanId> <signalName> <multiplexorName> v1-v1,v2-v2,…,vk-vk ;\n
```
WS discipline per `feedback_format_dsl_ws_family_discipline`, audited slot-by-slot: mandatory `ws` between tokens (parser one-or-more, canonical single space — matches today's drop-parser `parseWS`); **`wsOpt` after each comma** (parser zero-or-more, canonical emit empty — today's drop-parser accepts `", "`, so the capturing DSL must not regress accepted inputs; the corpus fixture `multiplexing.dbc:25` uses `", "` and is the live regression test); `wsCanonOne` before `;` (canonical ` ;`, parser zero-or-more — matches `parseWSOpt` today and the VAL_/BO_TX_BU_ house style).

**Section order**: new section **6c** in `TextFormatter/TopLevel.agda:formatChars`, immediately after `emitMessageSenders-chars` (6a/A.2), before `emitValueDescriptions-chars` (7). The parser's `many parseTopStmt` is order-agnostic; adjacency to the other message-derived section mirrors A.2. `toTopStmtsTyped` chunk order must mirror this exactly (chunk 4 of 9: TVT, TM, TBO, **TMV**, TVD, TEV, TCM, TAT, TSG).

**Attach semantics**: replace-whole-selector with **expansion at attach** (`presence := When multiplexor (expandRanges⁺ r rs)`), keyed `(canId, signalName)` — the VAL_ two-level shape. Runs **innermost** of the three attaches in `buildDBC` (order is semantically free — disjoint fields — but innermost is what lets `MuxCompose` chain `SendersCompose` unmodified). Expansion runs only AFTER the finalize span gate has passed (Q4b′).

---

## 4. Module layout

`--safe --without-K` on every module (no exceptions; nothing here needs the Unsafe substrate — all pure structure). Gate reality check (rev 2): `check-no-properties-in-runtime` greps only the four root files for direct Properties imports (§1.10) — keeping `Format/MuxVals.agda`'s Properties imports to the stop-lemma minimum is **convention** (MAlonzo-bloat discipline), not machine-enforced; follow the `Format/MessageSenders.agda` import set (:53-54, :60-61) as the ceiling.

### New modules
| Path | Tree | Contents | Est. LOC |
|---|---|---|---|
| `src/Aletheia/DBC/TextParser/MuxVals.agda` | runtime | `RawMuxVal` (raw ranges), `rangeValidᵇ`/`rangesValidᵇ`, `rangeSpan`/`rangesSpan`/`totalMuxSpan`, `expandRange⁺`/`expandRanges⁺`, `degenerateRanges`, `lookup-mv`, `attachMuxWithMaybe` (expands), `attachToSignalMux`, `attachToMessageMux`, `attachMuxVals`, `prependMuxVal`, `collectFromSignalsMux`, `collectMuxVals` (+ `resolvesᵇ`/`unresolvedRMVs` mirror iff Q3=B) | 200–250 |
| `src/Aletheia/DBC/TextFormatter/MuxVals.agda` | runtime | `emitMuxRange-chars : ℕ×ℕ → List Char`, `emitMuxRanges-chars`, `emitMuxVal-line-chars`, `emitMuxVals-rmvs-chars`, `emitMuxVals-chars` — DSL-free hand emitters over the SAME range list `RawMuxVal.ranges` the DSL emits (MessageSenders.agda template, read in full §5.3) | 90–120 |
| `src/Aletheia/DBC/TextParser/Format/MuxVals.agda` | runtime-adjacent (Format DSL + roundtrip witness, like Format/MessageSenders) | `muxRangeFmt`, `muxRangeListFmt`, `MuxVals-format`, comma-list EmitsOK helpers (local copies), `build-emits-ok-mv`, `parseMuxVals-format-roundtrip` | 300–380 |
| `src/…/TextParser/Properties/Aggregator/Dispatcher/Simple/MuxVals.agda` | proof | `RawMuxValStop` (idents + `T (rangesValidᵇ …)`), `rawMuxValStop` derivations, degenerate dischargers (`rangesValidᵇ-degenerate`, `rangesSpan-degenerate`, `totalMuxSpan-collect`, `expandRanges⁺-degenerate`), `emit-MuxVals-format-eq-emitMuxVal-line-chars` (refl-class — shared list), `parseSigMulVal-roundtrip(-explicit)`, `parseTopStmt-on-emit-TMV-eq`, `prependMuxVal-stops`, `collectMuxVals-stops` | 240–300 |
| `src/…/TextParser/Properties/Aggregator/Refine/MuxVals.agda` | proof | The inverse bridge (VAL_ cost class): Layer A + Layer 1 + `++`-prefix lemmas + record-η (consumes `expandRanges⁺-degenerate`); split a `MuxVals/` submodule if it passes ~700 LOC (`feedback_properties_facade_split`) | 620–800 |
| `src/…/TextParser/Properties/Aggregator/Refine/MuxCompose.agda` | proof | Triple-attach composition + trunc-invariances; chains SendersCompose unmodified | 220–300 |

### Changed modules
| Path | Change | Est. diff |
|---|---|---|
| `src/Aletheia/DBC/Types.agda` | `truncPresence`, `truncSig`, `clearMuxMsg`, `clearAllMsg` (+ `RawMuxVal` relocation + `DBC.unresolvedMuxVals` iff Q3=B — then also Marshal.hs/check-fidelity/check-erasure re-verification, Q3 table) | +30 |
| `src/Aletheia/Limits.agda` | `max-mux-total-span : ℕ`; `MuxRangeSpanTotal : BoundKind` + `boundKindCode`/`boundKindLabel` clauses | +12 |
| `src/Aletheia/Error.agda` | `MuxSpanBoundExceeded : ℕ → ℕ → DBCTextParseError` + `formatDBCTextParseError`/`dbcTextParseErrorCode` (code `"input_bound_exceeded"`) clauses | +10 |
| `src/Aletheia/Protocol/Handlers/ParseDBCText.agda` | one unwrap arm in `handleParseDBCTextResult` (double-`WithContext` bound envelope, §1.7 shape) + docstring caveat rewrite (:100-115 cites `wfps` as the worked example — coordinate with the parallel doc-edit session) | +8 |
| `src/Aletheia/DBC/TextParser/ExtendedMux.agda` | Rewrite: drop-parsers → `buildMuxValResult` (CAN-ID + `rangesValidᵇ` only — no span check) + `parseSigMulVal : Parser RawMuxVal` over `parse MuxVals-format` (header rewritten; stale `_converter.py` note removed) | ~80 net |
| `src/Aletheia/DBC/TextParser/TopLevel.agda` | `TSSigMulVal : RawMuxVal → TopStmt` (payload promotion), `CollectedTop.rawMuxVals` (9th bucket), `consTop` arm, `parseTopStmt-SG` bind-form | ~40 |
| `src/Aletheia/DBC/TextParser.agda` | `buildDBC`: innermost `attachMuxVals`; `finalizeParse`: helper-split refine tail + the span `if`-gate + `MuxSpanBoundExceeded` arm | ~30 |
| `src/Aletheia/DBC/TextFormatter/TopLevel.agda` | insert `emitMuxVals-chars (DBC.messages d)` as section 6c | +3 |
| `src/Aletheia/DBC/Formatter/WellFormedText.agda` | **delete** `WellFormedTextPresence`; `WellFormedTextSignal` loses `presence-wf` (audit `WellFormedTextSignal`/`WellFormedTextMessage` consumers — likely prunable entirely); header §2 rewritten | −30 |
| `src/…/Properties/Topology/Resolve.agda` | §5.6 restatement (trunc target, `wfps` removal) | ~120–160 |
| `src/…/Properties/Topology/SignalList.agda` | **Full wftp-drop set (rev 2)**: hypothesis dropped from ALL FOUR bridges — `emit-muxMarkerFmt-eq-for` (:134-150; When clauses generalize `(_ ∷ [])` → `(_ ∷ _)`, still refl per master case — both sides head-only), `emit-muxMarkerFmt-eq` (:152-161), `emit-signalLineFmt-eq-DBCSignal` (:167-177), `emit-many-signalLineFmt-eq-foldr` (:186-199, All-hypothesis dropped); `SignalLineWF` (:204-208) loses `presence-wf`; `SignalLineWF→PresenceWF` (:211-218) deleted. All hypothesis DROPS — `expectedMuxFor` is already tail-general (`When _ (v ∷ _) = SelBy v`, :108) | ~60–90 |
| `src/…/Properties/Topology/Message.agda` | `MessageWF` loses `wfps`; claims at `clearAllMsg`; `parseMessages-roundtrip` at `L = clearAllMsg`; every caller threading the wftp All-list into the four SignalList bridges updated | ~80–100 |
| `src/…/Properties/Aggregator/Foundations.agda` | `TMV` ctor, lift/emit arms, **`liftTopStmt (TM m) = TSMessage (clearAllMsg m)`**, 9th chunk in `toTopStmtsTyped` | ~45 |
| `src/…/Properties/Aggregator/Dispatcher.agda` | `wfTMV` ctor, dispatch/nonzero/head arms; **TM dispatch arm re-forwarded at the `clearAllMsg` statement** (rev 2) | ~20 |
| `src/…/Properties/Aggregator/Dispatcher/Simple/Message.agda` | **rev 2 — was missing**: `parseTopStmt-on-emit-TM-eq` pins `TSMessage (clearBothMsg msg)` (:54-59) and forwards `parseMessage-roundtrip-bundled`'s `clearBothMsg` mkResult through `p-msg-eq`/`alt-msg-eq` (:77-84) — restate all three at `clearAllMsg` in wave 7 | ~12 |
| `src/…/Properties/Aggregator/BodyBridge.agda` | `emit-map-TMV-eq`, `step-TMV`, cong-nest re-enumeration (9 chunks) | ~100–120 |
| `src/…/Properties/Aggregator/Partition.agda` | `partition-onto-acc-TMV`, TM rung at `clearAllMsg`, `foldr`-ladder rungs below insertion, `cong-mkCollectedTop` 9-ary, `partitionTopStmts-bridge` `rawMuxVals` bucket equation | ~160–180 |
| `src/…/Properties/Aggregator/Universal.agda` | `tmv-wf` arm; finalize stage: `totalMuxSpan-collect` rewrite + gate reduction + witnesses → MuxCompose lemmas | ~70–90 |
| `src/…/Properties/WellFormedFromValidity.agda` | nothing mandatory (stops live in Simple/MuxVals; `identNameStop` reused via import) — possibly a re-export | 0–20 |
| `Shakefile.hs` | walk roots for the three new proof modules; then `check-proof-coverage` must pass (`feedback_check_properties_aggregator_walks`) | ~15 |
| `src/…/Properties/Aggregator/ManyTopStmts.agda`, `Refine/Senders.agda`, `Refine/SendersCompose.agda`, `Refine/ValueDescriptions.agda` | **ZERO edits** (polymorphic / reused as-is) | 0 |

`feedback_chunk_structure_cascade`: before costing is finalized at execution, grep every consumer of `toTopStmtsTyped` / `CollectedTop` / `formatChars-body` for chunk-count enumeration (`rg -n "TBO|toTopStmtsTyped|mkCollectedTop" src/Aletheia/DBC/TextParser/Properties/`) — the table above reflects the A.2-measured cascade plus the rev-2 additions but must be re-confirmed; the Simple/Message omission (caught by the panel) shows a name-anchored grep for `clearBothMsg` consumers is also required.

---

## 5. New definitions and lemmas — signatures and proof approaches

Import conventions throughout: `renaming (_++_ to _++ₗ_)` on `Data.List`, `List⁺` cons written `_∷_` from `Data.List.NonEmpty`, `⌊_⌋` from `Relation.Nullary`.

### 5.1 Runtime — `Aletheia.DBC.TextParser.MuxVals`

```agda
record RawMuxVal : Set where
  constructor mkRawMuxVal
  field
    canId       : CANId
    signalName  : Identifier                -- the multiplexed child
    multiplexor : Identifier                -- the parent
    ranges      : (ℕ × ℕ) × List (ℕ × ℕ)   -- RAW inclusive ranges, non-empty by shape
                                             -- (= the muxRangeListFmt value type, no iso)
```
(Lives here under Q3=A; moves to `Types.agda` under Q3=B, `RawValueDesc` precedent.)

```agda
rangeValidᵇ : ℕ × ℕ → Bool
rangeValidᵇ (lo , hi) = lo ≤ᵇ hi

rangesValidᵇ : (ℕ × ℕ) × List (ℕ × ℕ) → Bool
rangesValidᵇ (r , rs) = rangeValidᵇ r ∧ all rangeValidᵇ rs   -- Data.Bool.ListAction.all

rangeSpan : ℕ × ℕ → ℕ
rangeSpan (lo , hi) = hi ∸ lo

rangesSpan : (ℕ × ℕ) × List (ℕ × ℕ) → ℕ
rangesSpan (r , rs) = rangeSpan r + foldr (λ q acc → rangeSpan q + acc) 0 rs

totalMuxSpan : List RawMuxVal → ℕ
totalMuxSpan = foldr (λ rmv acc → rangesSpan (RawMuxVal.ranges rmv) + acc) 0

-- lo ∷ lo+1 ∷ … ∷ hi
expandRange⁺ : ℕ → ℕ → List⁺ ℕ
expandRange⁺ lo hi = lo ∷ map (λ k → suc k + lo) (upTo (hi ∸ lo))

expandRanges⁺ : (ℕ × ℕ) → List (ℕ × ℕ) → List⁺ ℕ
expandRanges⁺ (lo , hi) []       = expandRange⁺ lo hi
expandRanges⁺ (lo , hi) (q ∷ qs) = expandRange⁺ lo hi ⁺++⁺ expandRanges⁺ q qs

degenerateRanges : List⁺ ℕ → (ℕ × ℕ) × List (ℕ × ℕ)
degenerateRanges (v ∷ vs) = (v , v) , map (λ w → w , w) vs
```
Design note (pre-planned traps — rev 2 corrected): on open `v`, both `v ∸ v` and `v ≤ᵇ v` are **stuck** (each recursion needs the open variable's constructor). Consequently `expandRange⁺ v v` does NOT reduce to `v ∷ []` on open `v` — `upTo (v ∸ v)` is stuck. **Every** degenerate lemma (§5.5), including the HEAD case of `expandRanges⁺-degenerate`, discharges via `cong` on `n∸n≡0`/`≤⇒≤ᵇ ≤-refl`, never by `refl`, and never by `rewrite` inside a parser-bearing goal (`feedback_no_rewrite_over_parser_goal`). `0 ≤ᵇ k ≡ true` IS definitional — the §5.8 finalize-gate reduction relies on it (which is why the gate compares `totalMuxSpan ≤ᵇ limit` with the span on the left).

```agda
matchesMV : CANId → Identifier → RawMuxVal → Bool
matchesMV cid name (mkRawMuxVal rcid rname _ _) = ⌊ cid ≟-CANId rcid ⌋ ∧ ⌊ name ≟ᴵ rname ⌋

lookup-mv : CANId → Identifier → List RawMuxVal → Maybe RawMuxVal
lookup-mv _   _    []          = nothing
lookup-mv cid name (rmv ∷ rs)  = if matchesMV cid name rmv then just rmv else lookup-mv cid name rs

-- EXPANSION HAPPENS HERE (post-gate; Q4b′):
attachMuxWithMaybe : DBCSignal → Maybe RawMuxVal → DBCSignal
attachMuxWithMaybe s nothing = s
attachMuxWithMaybe s (just (mkRawMuxVal _ _ mx (r , rs))) =
  record s { presence = When mx (expandRanges⁺ r rs) }

attachToSignalMux : List RawMuxVal → CANId → DBCSignal → DBCSignal
attachToSignalMux rmvs cid s = attachMuxWithMaybe s (lookup-mv cid (DBCSignal.name s) rmvs)

attachToMessageMux : List RawMuxVal → DBCMessage → DBCMessage
attachToMessageMux rmvs m =
  record m { signals = map (attachToSignalMux rmvs (DBCMessage.id m)) (DBCMessage.signals m) }

attachMuxVals : List RawMuxVal → List DBCMessage → List DBCMessage
attachMuxVals rmvs = map (attachToMessageMux rmvs)

prependMuxVal : CANId → Identifier → SignalPresence → List RawMuxVal → List RawMuxVal
prependMuxVal _   _  Always        rest = rest
prependMuxVal cid sn (When mx vs)  rest = mkRawMuxVal cid sn mx (degenerateRanges vs) ∷ rest

collectFromSignalsMux : CANId → List DBCSignal → List RawMuxVal
collectFromSignalsMux _   []       = []
collectFromSignalsMux cid (s ∷ ss) =
  prependMuxVal cid (DBCSignal.name s) (DBCSignal.presence s) (collectFromSignalsMux cid ss)

collectMuxVals : List DBCMessage → List RawMuxVal
collectMuxVals []       = []
collectMuxVals (m ∷ ms) =
  collectFromSignalsMux (DBCMessage.id m) (DBCMessage.signals m) ++ₗ collectMuxVals ms
```
Every case-split at function level, constructor patterns on `mkRawMuxVal` — the `ValueDescriptions.agda` API discipline verbatim (`feedback_expose_scrutinee_for_external_rewrite`, `feedback_with_abstraction_traps`, `feedback_k_elim_constructor_records`). Replace-semantics `attachMuxWithMaybe` is what dissolves the head-marker/line double-emission coherence obligation.

### 5.2 Runtime — `Aletheia.DBC.Types` additions

```agda
truncPresence : SignalPresence → SignalPresence
truncPresence Always           = Always
truncPresence (When m (v ∷ _)) = When m (v ∷ [])

truncSig : DBCSignal → DBCSignal
truncSig s = record s { presence = truncPresence (DBCSignal.presence s) }

clearMuxMsg : DBCMessage → DBCMessage
clearMuxMsg m = record m { signals = map truncSig (DBCMessage.signals m) }

-- What parseMessage actually reconstructs: senders=[], vds=[] per signal,
-- presence truncated to the head singleton.  clearBothMsg ∘ clearMuxMsg so the
-- MuxCompose factorization is definitional per cons (map-map reduces per element).
clearAllMsg : DBCMessage → DBCMessage
clearAllMsg m = clearBothMsg (clearMuxMsg m)
```

### 5.3 Runtime — emitters, parser promotion, finalize gate, error plumbing

`Aletheia.DBC.TextFormatter.MuxVals` (clone of `MessageSenders.agda`, read in full before writing — its four design moves are all load-bearing: eta-matching comma tail, unconditional keyword prefix, `foldr` section shape, collector-never-empty):
```agda
emitMuxRange-chars : ℕ × ℕ → List Char        -- "lo-hi" (degenerate collect gives "v-v")
emitMuxRange-chars (lo , hi) = showℕ-dec-chars lo ++ₗ '-' ∷ showℕ-dec-chars hi

emitMuxRanges-chars : (ℕ × ℕ) × List (ℕ × ℕ) → List Char
emitMuxRanges-chars (r , rs) =
  emitMuxRange-chars r ++ₗ concatMap (λ q → ',' ∷ emitMuxRange-chars q) rs

emitMuxVal-line-chars : RawMuxVal → List Char   -- 'S'-headed, non-empty for ALL inputs
emitMuxVal-line-chars rmv =
  toList "SG_MUL_VAL_ " ++ₗ showℕ-dec-chars (rawCanIdℕ (RawMuxVal.canId rmv))
    ++ₗ ' ' ∷ Identifier.name (RawMuxVal.signalName rmv)
    ++ₗ ' ' ∷ Identifier.name (RawMuxVal.multiplexor rmv)
    ++ₗ ' ' ∷ emitMuxRanges-chars (RawMuxVal.ranges rmv)
    ++ₗ ' ' ∷ ';' ∷ '\n' ∷ []

emitMuxVals-rmvs-chars : List RawMuxVal → List Char
emitMuxVals-rmvs-chars = foldr (λ rmv acc → emitMuxVal-line-chars rmv ++ₗ acc) []

emitMuxVals-chars : List DBCMessage → List Char
emitMuxVals-chars msgs = emitMuxVals-rmvs-chars (collectMuxVals msgs)
```
Rev-2 note: hand emitter and DSL emit now traverse the **same** `RawMuxVal.ranges` list (no `map dup` injection between them — `degenerateRanges` is applied once, at collect). This restores the MsgSenders refl-precedent shape (`Simple/MsgSenders.agda:83-87`, both sides share `(rawCanIdℕ cid , h , t)`). `feedback_concatmap_foldr_bridge` caveat still applies to the comma tail: it deliberately uses `concatMap` (NOT `foldr`) so the DSL bridge is eta; do not "simplify" it. (If Q4 were resolved to rev-1's Design A instead — values-carrying `RawMuxVal` — the bridge is NOT refl: `emit (many …) (map dup vs)` = `concat (map g (map dup vs))` vs `concat (map (g ∘ dup) vs)`, needing a ~15–30-line `map-∘` + cong-concat induction. Budgeted only under that fallback.)

`Aletheia.DBC.TextParser.ExtendedMux` promotion (`parseBOTxBu` template, TopLevel.agda:124-133) — validity checks only, no resource bound here:
```agda
buildMuxValResult : Maybe CANId → Identifier → Identifier
                  → (ℕ × ℕ) × List (ℕ × ℕ) → Parser RawMuxVal
buildMuxValResult nothing    _  _  _   = fail
buildMuxValResult (just cid) sn mx prs =
  if rangesValidᵇ prs then pure (mkRawMuxVal cid sn mx prs) else fail

parseSigMulVal : Parser RawMuxVal
parseSigMulVal = do
  q ← parse MuxVals-format
  _ ← many parseNewline
  buildMuxValResult (buildCANId (proj₁ q)) (proj₁ (proj₂ q)) (proj₁ (proj₂ (proj₂ q)))
                    (proj₂ (proj₂ (proj₂ q)))
```
Out-of-range CAN ID and inverted range reject the file with a positioned `ParseFailure` (wire validity — the `buildCANId` precedent). `TopLevel.agda`: `parseTopStmt-SG = parseSigMulVal >>= λ rmv → pure (TSSigMulVal rmv)` — the head-dispatch table (G-A24) is untouched.

**Finalize gate + error plumbing** (Q4b′; `TextParser.agda` / `Error.agda` / `Limits.agda` / `ParseDBCText.agda`):
```agda
-- Error.agda (DBCTextParseError gains one arm; wire code "input_bound_exceeded"):
MuxSpanBoundExceeded : ℕ → ℕ → DBCTextParseError    -- observed total span, limit

-- Limits.agda:
MuxRangeSpanTotal : BoundKind    -- code "mux_range_span_total"
max-mux-total-span : ℕ           -- suggested 65536 (user call; §2 Q4 derivation)

-- TextParser.agda — refine tail helper-split so the gate is a plain `if`
-- (expose-scrutinee; NOT `with … in` — feedback_with_in_eq_outer_abstraction_barrier):
finalizeCollected : List Char → List Node → CollectedTop → DBCTextParseError ⊎ DBC
finalizeCollected ver nodes collected with refineAttributes (CollectedTop.rawAttributes collected)
... | inj₁ (cause , bad) = inj₁ (AttributeRefinementFailed cause (fromList bad))
... | inj₂ attrs         = inj₂ (buildDBC ver nodes collected attrs)

-- inside finalizeParse, replacing the refine/build tail:
...  | collected =
  let spanTotal = totalMuxSpan (CollectedTop.rawMuxVals collected)
  in if spanTotal ≤ᵇ max-mux-total-span
     then finalizeCollected ver nodes collected
     else inj₁ (MuxSpanBoundExceeded spanTotal max-mux-total-span)

-- ParseDBCText.agda — unwrap to the LoadDBC boundErrorResponse wire shape (§1.7),
-- one arm BEFORE the generic inj₁ catch-all:
handleParseDBCTextResult (inj₁ (MuxSpanBoundExceeded obs lim)) state =
  (state , Response.Error (WithContext "ParseDBCText"
     (WithContext "multiplex value ranges" (InputBoundExceeded MuxRangeSpanTotal obs lim))))
```
The gate sits between `partitionTopStmts` and refine/build — pre-expansion (raw ranges only have been materialized: input-linear), outside every parser-combinator body (no combinator roundtrip lemma is touched).

### 5.4 Format DSL — `Aletheia.DBC.TextParser.Format.MuxVals`

```agda
muxRangeFmt : Format (ℕ × ℕ)
muxRangeFmt = pair nat (withPrefix ('-' ∷ []) nat)

muxRangeListFmt : Format ((ℕ × ℕ) × List (ℕ × ℕ))
muxRangeListFmt = pair muxRangeFmt (many (withPrefix (',' ∷ []) (withWSOpt muxRangeFmt)))

MuxVals-format : Format (ℕ × (Identifier × (Identifier × ((ℕ × ℕ) × List (ℕ × ℕ)))))
MuxVals-format =
  withPrefix (toList "SG_MUL_VAL_") (
    pair (withWS nat) (
      pair (withWS ident) (
        pair (withWS ident) (
          iso proj₁ (λ p → p , tt) (λ _ → refl)
              (pair (withWS muxRangeListFmt)
                    (withWSCanonOne (withPrefix (';' ∷ []) newlineFmt)))))))
```
(`withWS`/`withWSCanonOne`/`newlineFmt` local sugar copied from Format/MessageSenders :67-82; `withWSOpt` from the Format WS family — parser zero-or-more, canonical emit empty, preserving today's `", "` acceptance, live in `multiplexing.dbc:25`.)

```agda
build-emits-ok-mv :
    ∀ (rawId : ℕ) (sn mx : Identifier) (r : ℕ × ℕ) (rs : List (ℕ × ℕ)) (outer : List Char)
  → IdentHeadNonHSpace sn → IdentHeadNonHSpace mx
  → EmitsOK MuxVals-format (rawId , sn , mx , r , rs) outer
```
Approach: structural descent exactly like `build-emits-ok-mss` (:194-217). The stops are EASIER than senders: every `nat` run ends at a concrete separator (`'-'`, `','`, `' '`), so most `SuffixStops` witnesses are `∷-stop refl`; the two ident slots use the `IdentHeadNonHSpace` Σ via `subst … (∷-stop c-non-hs)`; `showNat-chars-head-stop-isHSpace` covers the nat-after-ws slots. The comma-list `EmitsOKMany` helpers are local copies with a combined digit/`,`/`-` stop class (per-site local-copy pattern, MessageSenders :90-150). If elaboration balloons on the `altSum`-nested `newlineFmt`, apply the head-class-witness specialization (`feedback_emitsok_inj2_deep_pattern`).

```agda
parseMuxVals-format-roundtrip :
    ∀ (pos : Position) (rawId : ℕ) (sn mx : Identifier)
      (r : ℕ × ℕ) (rs : List (ℕ × ℕ)) (outer : List Char)
  → IdentHeadNonHSpace sn → IdentHeadNonHSpace mx
  → proj₂ (parse MuxVals-format pos (emit MuxVals-format (rawId , sn , mx , r , rs) ++ₗ outer))
    ≡ just (mkResult (rawId , sn , mx , r , rs)
             (advancePositions pos (emit MuxVals-format (rawId , sn , mx , r , rs))) outer)
```
Approach: one `roundtrip MuxVals-format …` call + `build-emits-ok-mv` — the DSL's generic roundtrip does all the work (MsgSenders :226-237 template).

### 5.5 Per-section slim — `…Dispatcher/Simple/MuxVals.agda`

```agda
RawMuxValStop : RawMuxVal → Set
RawMuxValStop rmv = IdentHeadNonHSpace (RawMuxVal.signalName rmv)
                  × IdentHeadNonHSpace (RawMuxVal.multiplexor rmv)
                  × T (rangesValidᵇ (RawMuxVal.ranges rmv))   -- rev 2: the roundtrip
                        -- needs validity (buildMuxValResult's if); collected rmvs
                        -- carry it unconditionally via rangesValidᵇ-degenerate

rawMuxValStop-idents : ∀ (rmv : RawMuxVal) → …   -- identNameStop ×2, unconditional
```
The ident components come from `identNameStop` (WellFormedFromValidity :78-90) — intrinsic `Identifier` validity, free. The validity component is NOT free for arbitrary `rmv` but IS unconditional for every **collected** `rmv` (degenerate shape) — so `collectMuxVals-stops` still needs no `WellFormedTextDBCAgg` input → **no new Agg field**.

```agda
-- The stuck-reduction dischargers (§5.1 traps — proof notes corrected rev 2):
rangesValidᵇ-degenerate : ∀ (v : ℕ) (vs : List ℕ)
  → rangesValidᵇ (degenerateRanges (v ∷ vs)) ≡ true
-- induction on vs; per element (v ≤ᵇ v) ≡ true via T→true (≤⇒≤ᵇ ≤-refl) — NOT refl.

rangesSpan-degenerate : ∀ (v : ℕ) (vs : List ℕ)
  → rangesSpan (degenerateRanges (v ∷ vs)) ≡ 0
-- induction; per element cong via n∸n≡0, then +-identity chains.

totalMuxSpan-collect : ∀ (msgs : List DBCMessage) → totalMuxSpan (collectMuxVals msgs) ≡ 0
-- message/signal induction over collectMuxVals; per element rangesSpan-degenerate;
-- the §5.8 finalize gate reduces via this + definitional 0 ≤ᵇ k.

expandRanges⁺-degenerate : ∀ (v : ℕ) (vs : List ℕ)
  → expandRanges⁺ (v , v) (map (λ w → w , w) vs) ≡ v ∷ vs
-- induction on vs.  HEAD CASE IS NOT refl (rev 2 correction): expandRange⁺ v v =
-- v ∷ map _ (upTo (v ∸ v)) is stuck on open v; discharge with
-- cong (λ n → v ∷ map _ (upTo n)) (n∸n≡0 v), THEN upTo 0 = [] reduces.
-- Cons case: discharge the head the same way, then (v ∷ []) ⁺++⁺ rec reduces;
-- close with cong.  trans/cong only — never rewrite (§5.1).

emit-MuxVals-format-eq-emitMuxVal-line-chars :
    ∀ (rmv : RawMuxVal)
  → emit MuxVals-format
      ( rawCanIdℕ (RawMuxVal.canId rmv)
      , RawMuxVal.signalName rmv
      , RawMuxVal.multiplexor rmv
      , RawMuxVal.ranges rmv )
    ≡ emitMuxVal-line-chars rmv
-- refl-class: both sides traverse the SAME ranges list (the MsgSenders :83-87
-- shared-value precedent); at worst a ++ₗ-assoc cong chain.  (The rev-1 shape,
-- with degenerateRanges applied INSIDE this statement, was NOT refl — map-∘
-- mismatch; dissolved by carrying ranges in RawMuxVal.)

parseSigMulVal-roundtrip :
    ∀ (pos : Position) (rmv : RawMuxVal) (suffix : List Char)
  → RawMuxValStop rmv
  → SuffixStops isNewlineStart suffix
  → proj₂ (parseSigMulVal pos (emitMuxVal-line-chars rmv ++ₗ suffix))
    ≡ just (mkResult rmv (advancePositions pos (emitMuxVal-line-chars rmv)) suffix)
```
Approach: MANDATORY `-explicit`/cong-only wrapper pattern (MsgSenders :92-183; `feedback_no_rewrite_over_parser_goal` — one A.2 dispatcher hit 15.7 GB under the naive form). The explicit form takes the destructured fields (`cid`, `sn`, `mx`, `r`, `rs`) and chains: the emit-bridge → `parseMuxVals-format-roundtrip` → `many parseNewline` no-op on non-newline suffix → `bind-just-step` into `buildMuxValResult` → `buildCANId-rawCanIdℕ cid` → the `if` reduces via the `T (rangesValidᵇ …)` witness converted through `T→true` and `cong`-applied on a helper equality over `buildMuxValResult (just cid) sn mx …` (outside any parser-stuck context) → record-η on `mkRawMuxVal`. Note (rev 2): the roundtrip holds for ANY valid-ranges `rmv`, not only degenerate ones — degeneracy is consumed later, at the attach-recover layer (§5.7). The public form destructures `rmv` once and `cong`s.

```agda
parseTopStmt-on-emit-TMV-eq :
    ∀ (pos : Position) (rmv : RawMuxVal) (outer : List Char)
  → RawMuxValStop rmv
  → SuffixStops isNewlineStart outer
  → proj₂ (parseTopStmt pos (emitMuxVal-line-chars rmv ++ₗ outer))
    ≡ just (mkResult (TSSigMulVal rmv)
             (advancePositions pos (emitMuxVal-line-chars rmv)) outer)
```
Approach: the emitted line is `'S' ∷ 'G' ∷ …`, so `parseTopStmt` reduces in ONE pattern-match step to `parseTopStmt-SG` (head-dispatch, `feedback_chain_dispatch_at_concrete_input`); the bucket is a single parser — plain `bind-just-step` + `cong` over `parseSigMulVal-roundtrip`. **No `alt-left-just`** (cheaper than the TBO arm).

```agda
prependMuxVal-stops :
    ∀ (cid : CANId) (sn : Identifier) (p : SignalPresence) (rest : List RawMuxVal)
  → All RawMuxValStop rest → All RawMuxValStop (prependMuxVal cid sn p rest)
collectMuxVals-stops : ∀ (msgs : List DBCMessage) → All RawMuxValStop (collectMuxVals msgs)
```
Approach: case on `p` (function-level split already exposed); `All`-induction; `++⁺` (`Data.List.Relation.Unary.All.Properties`) for the message-level `++ₗ`; ident components by `identNameStop`, validity component by `rangesValidᵇ-degenerate` (+ `true→T`). Unconditional — no WF input.

### 5.6 The wfps/item-pres removal — exact statement changes (Topology layer)

**Statements that DISAPPEAR** (no replacement needed — hypotheses drop):
- `MessageWF.wfps : All (λ s → WellFormedTextPresence (DBCSignal.presence s)) (DBCMessage.signals msg)` (Message.agda:565-566) — **deleted field**.
- `SignalLineWF.presence-wf : WellFormedTextPresence (DBCSignal.presence sig)` (SignalList.agda:208) — **deleted field**; `item-pres` (Message.agda:570) keeps its type `All SignalLineWF …` but the record now carries only `name-stop` + `recv-head-stop`.
- `SignalLineWF→PresenceWF` (SignalList.agda:211-218) — **deleted** (no consumer remains).
- `data WellFormedTextPresence` (`wftp-always`/`wftp-when-single`, WellFormedText.agda:88-90) — **deleted type**; `WellFormedTextSignal.presence-wf` deleted with it.
- **The full SignalList wftp-threading set (rev 2 — all four bridges, not one)**: `emit-muxMarkerFmt-eq-for` (:134-150) drops its `WellFormedTextPresence p` hypothesis — When clauses generalize `(_ ∷ [])` → `(_ ∷ _)` and stay refl per master case (both `expectedMuxFor` at :108 and `emitMuxMarker-chars` at Topology.agda:147-148 are head-only); `emit-muxMarkerFmt-eq` (:152-161), `emit-signalLineFmt-eq-DBCSignal` (:167-177), `emit-many-signalLineFmt-eq-foldr` (:186-199) each drop the wfp/All parameter; **every Message.agda caller threading the All-list into these updates in the same wave**.
- `resolveSignalList-roundtrip`'s 4th hypothesis `All (λ s → WellFormedTextPresence (DBCSignal.presence s)) sigs` (Resolve.agda:612) and its threading through `buildMessage-roundtrip`/`parseMessage-roundtrip` (Message.agda:242/394/539 region) — **dropped parameters**.
- `all-sigOK-mc-mux`'s wftp parameter (Resolve.agda:538) — **dropped**; `sigOK-from-wfp` renamed `sigOK-from-presence`, casing on `DBCSignal.presence sig` directly (the `helper` :574-588 loses its `WellFormedTextPresence p` argument; the `When sm (v ∷ vs)` clause is now total over any tail — coverage comes from the presence case split itself, not from wftp constructors). **Net: this proof gets SIMPLER.**

**Statements RESTATED at the truncated value** (value-of-claim changes, not structural rewrites — the A.2 `clearVdsMsg → clearBothMsg` precedent, `741ad77b` class):

```agda
-- Resolve.agda
buildSignal-fields-recover :          -- hypothesis + target change
    ∀ (sig : DBCSignal) (fb : ℕ) (presence-result : SignalPresence)
  → fb ≤ 64 → WellFormedSignal sig → PhysicallyValid fb sig
  → presence-result ≡ truncPresence (DBCSignal.presence sig)
  → (if 1 ≤ᵇ … then just (record { … ; presence = presence-result ; valueDescriptions = [] }) else nothing)
    ≡ just (clearVds (truncSig sig))

buildSignal-roundtrip-Always :        -- target only
  … → DBCSignal.presence sig ≡ Always → …
  → buildSignal fb m (expectedRawOfDBC master fb sig) ≡ just (clearVds (truncSig sig))

buildSignal-roundtrip-When :          -- hypothesis generalized to any tail; target truncated
    ∀ (master : Maybe (List Char)) (fb : ℕ) (sig : DBCSignal)
      (m sig-master : Identifier) (v : ℕ) (vs : List ℕ)
  → DBCSignal.presence sig ≡ When sig-master (v ∷ vs)
  → m ≡ sig-master → fb ≤ 64 → WellFormedSignal sig → PhysicallyValid fb sig
  → buildSignal fb (just m) (expectedRawOfDBC master fb sig) ≡ just (clearVds (truncSig sig))
-- proof: rewrite presence-eq | m-eq; resolvePresence (just sig-master) (SelBy v)
-- = just (When sig-master (v ∷ [])) = truncPresence (When sig-master (v ∷ vs));
-- close with buildSignal-fields-recover.  This repairs the ONE equation that was
-- false for multi-value originals (presence-eq at :230/:265).

data SigOK (m : Maybe Identifier) (fb : ℕ) : DBCSignal → Set where
  sigok-always : … (unchanged)
  sigok-when   : ∀ {sig sig-master v vs}
               → DBCSignal.presence sig ≡ When sig-master (v ∷ vs)   -- ← tail freed
               → m ≡ just sig-master
               → WellFormedSignal sig → PhysicallyValid fb sig
               → SigOK m fb sig

buildAllRaw-roundtrip :               -- target: map clearVds (map truncSig sigs)
  … → buildAllRaw fb m (map (expectedRawOfDBC master fb) sigs)
      ≡ just (map clearVds (map truncSig sigs))
-- the double map reduces per cons definitionally — no fusion lemma needed.

resolveSignalList-roundtrip :
    ∀ (fb : ℕ) (sigs : List DBCSignal)
  → fb ≤ 64 → All WellFormedSignal sigs → All (PhysicallyValid fb) sigs
  → MasterCoherent sigs                                              -- wfps GONE
  → resolveSignalList fb (map (expectedRawOfDBC (findMuxMaster sigs) fb) sigs)
    ≡ just (map clearVds (map truncSig sigs))
```
`MasterCoherent`, `findMuxMaster-nothing→all-Always`, `findMuxName-on-no-mux`, `findMuxName-finds-master` — **all unchanged** (values-independent; verified). A small contingency family `findMuxMaster-trunc-stable : ∀ sigs → findMuxMaster (map truncSig sigs) ≡ findMuxMaster sigs` (+ `findMuxName` mirror) is budgeted (~30 lines) but expected UNUSED in slice A.1 (the roundtrip direction never scans truncated lists); write it only if a goal actually demands it.

```agda
-- Message.agda
record MessageWF (msg : DBCMessage) : Set where
  field
    fb-bound … wf-sigs … pvs … mc … name-pre … send-pre … item-pres … sig-names-unique …
    -- wfps DELETED; everything else verbatim

parseMessage-roundtrip-bundled :
  … → MessageWF msg → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseMessage pos (emitMessage-chars msg ++ₗ outer-suffix))
    ≡ just (mkResult (clearAllMsg msg) (advancePositions pos (emitMessage-chars msg)) outer-suffix)

parseMessages-roundtrip : … ≡ just (mkResult (map clearAllMsg msgs) … )
-- via many-η-roundtrip-with-lift with L = clearAllMsg (ManyTopStmts: ZERO edits, fully polymorphic)
```
**Rev 2 — downstream pin (was missing from the inventory)**: `Dispatcher/Simple/Message.agda`'s `parseTopStmt-on-emit-TM-eq` pins `TSMessage (clearBothMsg msg)` in its statement (:54-59) and forwards the `clearBothMsg` mkResult through `p-msg-eq`/`alt-msg-eq` (:77-84) — restate all three at `clearAllMsg` in the same atomic wave (the `alt-right-nothing` arbitration and `botxbu-fail = refl` survive unchanged); `Dispatcher.agda`'s TM dispatch arm re-forwards the new statement.

Consequence for the Agg: `WellFormedTextDBCAgg` keeps its **9 fields textually**, but `msg-wfs : All MessageWF …` is strictly weaker → the record is strictly weaker → the universal theorem covers strictly more DBCs. Remaining E.2 walls after this slice: `attr-wfs`, `unresolved-empty`, `pvs.msb-ge-len`, warning-class `wf-sigs`, and `mc` (until A.3).

### 5.7 Inverse bridge — `…Refine/MuxVals.agda` (the VAL_ cost class)

Clone the layer structure of `Refine/ValueDescriptions.agda` (707 lines) with the presence field in place of `valueDescriptions` and `truncSig` in place of `clearVds`. Load-bearing lemmas (names mirror the VAL_ module's conventions):

```agda
-- Layer A (within one message, under sig-names-unique):
lookup-mv-collectFromSignalsMux-hit :
    ∀ (cid : CANId) (sigs : List DBCSignal) (s : DBCSignal) (mx : Identifier) (vs : List⁺ ℕ)
  → s ∈ sigs → DBCSignal.presence s ≡ When mx vs
  → AllPairs _≢_ (map DBCSignal.name sigs)
  → lookup-mv cid (DBCSignal.name s) (collectFromSignalsMux cid sigs)
    ≡ just (mkRawMuxVal cid (DBCSignal.name s) mx (degenerateRanges vs))

lookup-mv-collectFromSignalsMux-miss-always :
    ∀ (cid : CANId) (sigs : List DBCSignal) (s : DBCSignal)
  → s ∈ sigs → DBCSignal.presence s ≡ Always
  → AllPairs _≢_ (map DBCSignal.name sigs)
  → lookup-mv cid (DBCSignal.name s) (collectFromSignalsMux cid sigs) ≡ nothing

-- per-signal record-η inverse (the crux equation; consumes the codec lemma here —
-- attach expands, so recovery needs expandRanges⁺ ∘ degenerateRanges ≡ id; needs the
-- record-builder cong pattern, `feedback_rewrite_through_record_builder`):
attachToSignalMux-trunc-recover :
    ∀ (rmvs : List RawMuxVal) (cid : CANId) (s : DBCSignal) (mx : Identifier) (vs : List⁺ ℕ)
  → DBCSignal.presence s ≡ When mx vs
  → lookup-mv cid (DBCSignal.name s) rmvs ≡ just (mkRawMuxVal cid (DBCSignal.name s) mx (degenerateRanges vs))
  → attachToSignalMux rmvs cid (truncSig s) ≡ s
-- attach gives presence = When mx (expandRanges⁺ (degenerateRanges vs));
-- expandRanges⁺-degenerate (cong through the record builder) lands presence = When mx vs;
-- record (truncSig s) { presence = When mx vs } η-collapses to s.

-- Layer 1 (cross-message, under msg-ids-unique): the ++-shaped collect returns the
-- append-splitting prefix lemmas — clone lookup-skip/lookup-++ discipline from the
-- VAL_ module (entries of OTHER messages fail matchesMV on the canId conjunct;
-- AllPairs ¬-propagation exactly as Refine/Senders :159-180 Layer 1).

-- Module theorems:
attachMuxVals-on-collected :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs) → All MessageWF msgs
  → attachMuxVals (collectMuxVals msgs) msgs ≡ msgs

map-attachToMessageMux-on-clearMuxMsgs-collected :          -- the lifted, load-bearing form
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs) → All MessageWF msgs
  → map (attachToMessageMux (collectMuxVals msgs)) (map clearMuxMsg msgs) ≡ msgs
```
`MessageWF` is consumed ONLY for `sig-names-unique` (project it; forward the rest opaquely — the SendersCompose :40-44 stability discipline). Approach for both: message-level induction; per message, signal-level `All`-induction pairing hit/miss lemmas with `attachToSignalMux-trunc-recover`/no-op; `map-≡-id`-style closing. G-A22 checkpoint: if any sub-lemma family exceeds ~500 LOC beyond the VAL_ analogue's shape, STOP and surface (`feedback_step_back_when_proofs_balloon`).

### 5.8 Composition — `…Refine/MuxCompose.agda` + finalize gate discharge

```agda
map-clearAll :
    ∀ (msgs : List DBCMessage)
  → map clearAllMsg msgs ≡ map clearBothMsg (map clearMuxMsg msgs)
-- per-cons cong; heads coincide definitionally (clearAllMsg = clearBothMsg ∘ clearMuxMsg).

-- attachMuxVals commutes past both clear passes.  vs clearSenders: message-level
-- disjoint fields — refl-style cong₂ per element (SendersCompose :91-97 mold).
-- vs clearVds: BOTH act on the same per-signal list → needs a per-signal Maybe-elim
-- helper (attachMuxWithMaybe (clearVds s) r ≡ clearVds (attachMuxWithMaybe s r), case r)
-- plus per-message map-compose reduction; ~60–90 lines, the only commute that is
-- not literally refl.
attachToSignalMux-clearVds-commute :
    ∀ (rmvs : List RawMuxVal) (cid : CANId) (s : DBCSignal)
  → attachToSignalMux rmvs cid (clearVds s) ≡ clearVds (attachToSignalMux rmvs cid s)
map-attachToMessageMux-clearBoth-commute :
    ∀ (rmvs : List RawMuxVal) (ms : List DBCMessage)
  → map (attachToMessageMux rmvs) (map clearBothMsg ms)
    ≡ map clearBothMsg (map (attachToMessageMux rmvs) ms)

-- Step 1′ — attachMuxVals over the triple clear recovers the double clear:
attachMuxVals-on-clearAllMsgs-collected :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs) → All MessageWF msgs
  → attachMuxVals (collectMuxVals msgs) (map clearAllMsg msgs) ≡ map clearBothMsg msgs
-- trans (cong … map-clearAll) (trans commute (cong (map clearBothMsg) (lifted bridge from §5.7)))

-- The exact form buildDBC presents (consumed by Universal):
attachSenders-attachValueDescs-attachMuxVals-on-clearAllMsgs-collected :
    ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs) → All MessageWF msgs
  → attachSenders (collectSenders msgs)
      (attachValueDescs (collectFromMessages msgs)
        (attachMuxVals (collectMuxVals msgs) (map clearAllMsg msgs)))
    ≡ msgs
-- Step 1′ then the EXISTING SendersCompose composed lemma, verbatim — zero
-- SendersCompose edits (the innermost-attach design decision pays here).

-- unresolvedValueDescs field over the triple clear:
resolvesᵇ-msgs-clearMux :
    ∀ (rvd : RawValueDesc) (ms : List DBCMessage)
  → resolvesᵇ-msgs rvd (map clearMuxMsg ms) ≡ resolvesᵇ-msgs rvd ms
-- truncSig preserves name/id — refl-style cong₂ _∨_ chain (SendersCompose :107-112 mold).
unresolvedRVDs-on-clearAllMsgs-collectFromMessages :
    ∀ (msgs : List DBCMessage)
  → unresolvedRVDs (collectFromMessages msgs) (map clearAllMsg msgs) ≡ []
-- map-clearAll, clearMux-invariance, then the existing clearBoth lift (SendersCompose :164-173).
```

**Finalize gate discharge (rev 2)**: `finalizeParse-on-mkResult-clean` (Universal.agda:535-556 region) gains one rewrite before the `refineAttributes-on-rawOf` step: after `partitionTopStmts-bridge` lands `rawMuxVals = collectMuxVals (DBC.messages d)`, rewrite `totalMuxSpan-collect (DBC.messages d)` — the gate condition becomes `0 ≤ᵇ max-mux-total-span`, which reduces to `true` **definitionally** (§5.1), and the `if` steps into `finalizeCollected`, whose with-chain the existing stage-2 rewrites walk exactly as today. The two-stage `outcome-subst` heap discipline (:519-533) is untouched — the gate lives entirely inside stage 2's finalize walk.

### 5.9 Aggregator ladder edits (all mechanical, A.2-template)

- **Foundations.agda**: `TMV : RawMuxVal → TopStmtTyped` (after `TBO` :191); `liftTopStmt _ (TMV rmv) = TSSigMulVal rmv`; **`liftTopStmt _ (TM m) = TSMessage (clearAllMsg m)`** (the clear-form widening, exactly as A.2 widened `clearVdsMsg → clearBothMsg` at :209); `emitTopStmt-chars _ (TMV rmv) = emitMuxVal-line-chars rmv`; `toTopStmtsTyped` chunk 4: `map TMV (collectMuxVals (DBC.messages d))` between the TBO and TVD chunks (mirrors formatChars section 6c position).
- **Dispatcher.agda**: `wfTMV : ∀ rmv → RawMuxValStop rmv → TopStmtTypedWF defs (TMV rmv)`; dispatch arm → `parseTopStmt-on-emit-TMV-eq`; nonzero arm `s≤s z≤n`; head-not-newline arm `∷-stop refl` (`'S'`); TM dispatch arm re-forwarded at `clearAllMsg` (per §5.6's Simple/Message restatement).
- **BodyBridge.agda**: `emit-map-TMV-eq` (8-line clone of `emit-map-TBO-eq` :128-133), `step-TMV`, and re-enumeration of the `distrib`/`convert` cong-nests to 9 chunks (:308-360 region).
- **Partition.agda**: `partition-onto-acc-TMV` (6-line clone; `cong (consTop (TSSigMulVal rmv))`); `partition-onto-acc-TM` re-anchored at `clearAllMsg`; the positional `foldr-*-eq` ladder re-run for every rung below the TMV insertion (:236-397); `cong-mkCollectedTop` grows to 9-ary; `partitionTopStmts-bridge` gains the `rawMuxVals = collectMuxVals (DBC.messages d)` bucket equation.
- **Universal.agda**: `tmv-wf : All (TopStmtTypedWF defs) (map TMV (collectMuxVals (DBC.messages d)))` from `collectMuxVals-stops` + `All.map⁺`-style tabulate (clone `tbo-wf` :183-188); one more `++⁺` in `toTopStmtsTyped-wf`; in `finalizeParse-on-mkResult-clean` swap the messages witness to `attachSenders-attachValueDescs-attachMuxVals-on-clearAllMsgs-collected`, the unresolved witness to `unresolvedRVDs-on-clearAllMsgs-collectFromMessages`, and add the `totalMuxSpan-collect` gate rewrite (§5.8).
- **Substrate/Unsafe.agda**: zero edits; re-type-checks with the weaker Agg.

---

## 6. Proof order (what unblocks what) + per-step verification

`AGDA="agda +RTS -N32 -M16G -RTS"` from `src/`. The `-M16G` cap is the runaway-elaboration tripwire — if a step OOMs, fix the proof shape (cong-only/helper), never raise the cap first.

| # | Step | Depends on | Verify |
|---|---|---|---|
| 0 | Decisions Q1–Q5 ratified (incl. the Q4 constant + the compat framing §7); §12.3 re-verification pass | — | — |
| 1 | `Limits` (`max-mux-total-span`, `MuxRangeSpanTotal`) + `Error.agda` arm + `Types.agda` helpers (`truncPresence`…`clearAllMsg`) | — | `$AGDA Aletheia/Error.agda`, `$AGDA Aletheia/DBC/Types.agda` |
| 2 | `TextParser/MuxVals.agda` (runtime attach/collect/expand/span) | 1 | `$AGDA Aletheia/DBC/TextParser/MuxVals.agda` |
| 3 | `TextFormatter/MuxVals.agda` (emitters; NOT yet wired) | 2 | module check |
| 4 | `Format/MuxVals.agda` (DSL + EmitsOK + roundtrip) | — | module check (watch heap; EmitsOK specialization if needed) |
| 5 | `Refine/MuxVals.agda` (inverse bridge — the crux; provable against step 2 alone, BEFORE any wiring breaks the tree) | 2 | module check; G-A22 balloon checkpoint |
| 6 | `Refine/MuxCompose.agda` | 5 | module check |
| 7 | **Atomic wiring + restatement wave** (the tree is broken between 7a and 7f — do as one push): 7a `ExtendedMux` promotion + `TopLevel` payload/bucket + `buildDBC` + **`finalizeParse` gate/helper-split + `ParseDBCText` unwrap arm** + `formatChars` 6c; 7b `Resolve.agda` restatement (§5.6); 7c `SignalList.agda` (all four bridges) + `Formatter/WellFormedText.agda` (wftp deletion); 7d `Message.agda` (`MessageWF` − wfps, `clearAllMsg` claims) + **`Dispatcher/Simple/Message.agda` restatement**; 7e `Dispatcher/Simple/MuxVals.agda` slim; 7f Foundations → Dispatcher → BodyBridge → Partition → Universal | 2–6 | after 7f: `$AGDA Aletheia/DBC/TextParser/Properties/Aggregator/Universal.agda`, then `$AGDA Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda` |
| 8 | Shake walk roots + coverage | 7 | `cabal run shake -- check-proof-coverage && cabal run shake -- check-properties` |
| 9 | Full Agda gate battery | 8 | `cabal run shake -- gen-ffi-modules && cabal run shake -- build && cabal run shake -- check-invariants && cabal run shake -- check-no-properties-in-runtime && cabal run shake -- check-erasure && cabal run shake -- check-fidelity && cabal run shake -- check-ffi-exports` |
| 10 | Bindings/tests/matrix/docs (§7) **incl. corpus snapshot regen + README + CHANGELOG compat entry** | 9 | binding suites + lint per AGENTS § Step 4; `tools/run_ci.py` full sweep pre-merge |
| 11 | Benchmarks (§8) | 10 | `bash benchmarks/run_all.sh …` |

Incremental-commit discipline mirrors A.2 (`8c24c14d → e1afc71c`): steps 1–6 are individually green commits; step 7 is the one necessarily-large commit; single-slot dribble, signed commits, pipeline-PR rules all apply.

---

## 7. Integration obligations (established patterns; rev 2 additions marked ★)

- **Kernel handlers**: `handleParseDBCText` gains ONE unwrap arm (§5.3; the double-`WithContext` bound envelope — LoadDBC `boundErrorResponse` shape) — no longer "zero code changes" but zero *logic* beyond the arm. `handleFormatDBCText` stays total/unconditional. **Docstring updates required**: FormatDBCText's caveat list (:100-115) cites "a multi-value mux selector fails `MessageWF.wfps`" as its worked example — rewrite (coordinate with the parallel doc-edit session touching this file). `TextFormatter/Topology.agda:28-37` and `ExtendedMux.agda:12-38` deferral headers deleted/rewritten.
- **JSON wire**: unchanged (Q1a). `multiplex_values` now survives text round-trips too.
- **★ CHANGELOG — explicit compat framing (Changed/BREAKING-candidate, Go-#61/A.2-senders precedent)**: A.1 changes the load semantics of every `SG_MUL_VAL_`-bearing text file accepted today (multiplexor/values flip from marker-interim/head-truncated to line-truth) and introduces reject classes on a previously drop-parsed line (today's parser accepts and discards any nat CAN ID and any lo/hi ordering — `ExtendedMux.agda:113-129`): inverted range / out-of-range CAN ID → positioned parse error; over-span file → typed `input_bound_exceeded`. These are the right semantics but MUST be written up as explicit `### Changed` entries with migration notes (one header per category — `feedback_changelog_one_header_per_category`), and the reject classes named as user-visible behavior changes, not buried in acceptance criterion 3. Whether the flip is labeled BREAKING is a user call at execution (§ unresolved).
- **★ Existing-fixture flip deliverables** (the A.2 `kitchen_sink.json` regen precedent): regenerate `python/tests/fixtures/dbc_corpus/parity_snapshots/multiplexing.json` — `LeafSignalX` → `SecondaryMux`/`[0,1,2]`, `LeafSignalY` → `SecondaryMux`/`[3,4,5,10,11,12]` (from `multiplexing.dbc:24-25`); `SecondaryMux` itself stays `PrimaryMux`/`[0]` (it has no `SG_MUL_VAL_` line; its `m0M` marker's interim binding is also its true binding). All three snapshot consumers (`python/tests/test_dbc_corpus_parity.py`, `go/aletheia/dbc_corpus_parity_test.go`, `cpp/tests/dbc_corpus_parity_tests.cpp`) re-run green. `kitchen_sink.json` expected UNCHANGED (its lines `0-0`/`1-1` at `kitchen_sink.dbc:90-91` match the marker-interim values `m0`/`m1` under master `Mode`, :42-45) — but re-run, don't assume. `examples/example.dbc` is NOT affected (§1.9 — NS_ keyword entry only). Corpus `README.md`: update the `multiplexing.dbc` feature row (drop-semantics note gone) and the known-divergences section. **★ Also sweep for any golden pinning `format_dbc_text` output of corpus fixtures** (`rg -l "SG_MUL_VAL_\|format_dbc_text" python/tests go cpp rust` at execution) — section 6c adds lines to every formatted mux-bearing DBC. The byte-exact position pin (`midfile_bad` L40 C22) is NOT on this surface (its only `SG_MUL_VAL_` occurrence is the NS_ entry at :29; the pin is on the bad DLC) — verify pins stay green in step 10.
- **★ Pre-existing doc gap (independent of this arc)**: the corpus README's known-divergences section (:52+) documents SIG_VALTYPE_/EV_DATA_ but NOT that `SG_MUL_VAL_` data is currently dropped and nested parents mis-bound. Worth a one-line fix whenever docs are next touched — before or with A.1.
- **Bindings**: zero logic changes (shape already supported in all four); ★ one additive C++ `bound_kind_*` constant (`cpp/include/aletheia/limits.hpp`) for `mux_range_span_total` (Python/Rust/Go lift `bound_kind` as a passthrough string — §1.8). **New parity tests**: fixture `extended_mux.dbc` (multi-value `3-3,5-5,7-7` + a `", "`-separated variant + an inverted-range reject case + an over-span-file reject case); each binding asserts `multiplex_values == [3,5,7]` after text load, that `format_dbc_text` output contains the `SG_MUL_VAL_` line and re-parses to the same DBC, and that the over-span reject surfaces as typed `input_bound_exceeded` with `bound_kind == "mux_range_span_total"`. Placement per `feedback_cross_binding_test_placement` (Py/C++ real FFI; Go mock+real; Rust via `.so`).
- **FEATURE_MATRIX.yaml**: new row `dbc_extended_mux_text` ×4 bindings (`feedback_matrix_row_or_invisible`); update `dbc_text_format` row description. Structural gates pick the row up automatically.
- **Docs**: PROTOCOL.md § Limits — `max-mux-total-span` row + § Error table `mux_range_span_total` note; the validity-reject note (inverted range / CAN ID = positioned parse error, CAN-ID-range precedent); ★ the two A.1 product caveats from §1.4 (uncovered nested children keep interim binding; emitted nested text not Vector-canonical until A.3) documented in PROTOCOL.md/FormatDBCText docstring; DEFERRED_ITEMS.md — A.1 → DONE, A.3 rescoped to §9 of this plan, E.2 wall list updated; CHANGELOG per the compat item above; CLI_SCENARIOS.yaml — optional validate/format scenario on the new fixture.
- **Mutation surface**: new runtime branches (`rangesValidᵇ`, the finalize span gate, `lookup-mv` miss/hit, `attachMuxWithMaybe`, `prependMuxVal`) need killing tests — the reject-case fixtures above are designed to kill the `≤ᵇ`/`∧` mutants; run a clean local `mutmut` (erase `python/mutants/` first, `feedback_mutation_cache_hygiene`).
- **★ Optional defense-in-depth (proof-free)**: a `multiplex values` cardinality walk in the LoadDBC cascade (`Handlers/LoadDBC.agda:75-93` pattern) — covers the JSON route too and closes the cross-route symmetry question (JSON-route array bounds vs text-route expansion); handlers are outside `parseTextChars`, so no Agg impact. Surface at execution with the JSON bound's value.
- **Q3=B addendum (if chosen)**: `DBC.unresolvedMuxVals` triggers the full G-A23 audit — JSON parse (`parseOptionalArray`, absent-key `[]`), JSON emit, 4 binding typed fields, new warn-class check + `IssueCode` mirror ×4, PROTOCOL.md error table, FEATURE_MATRIX row, Agg field `unresolved-mux-empty` + its `finalizeParse` witness (`unresolvedRMVs-on-collected ≡ []`), **★ plus the MAlonzo constructor-arity fallout: Marshal.hs re-verification + `check-fidelity`/`check-erasure` expectation updates (§2 Q3)**.

---

## 8. Performance discipline

- **Cold path only.** `parseText`/`formatText` run at DBC-load/format time, never per frame. `Dec`-valued lookups (`⌊ ≟-CANId ⌋`, `⌊ ≟ᴵ ⌋`) in attach/collect are fine here (the `lookup-vd`/`lookup-senders` precedent). The finalize span gate is one fold over the rawMuxVals bucket — noise. **No file under `CAN/`, `Protocol/FrameProcessor`, or the signal-extraction path is touched** — the frame hot path is provably unaffected (verify with `git diff --stat`).
- Expected cold-path deltas: DBC-text parse +1–3% (9th top-level section + attach-time expansion), format +O(#When-signals) line emission. Multi-value presence at *runtime extraction* already works today via the JSON path — no new runtime cost class.
- **Adversarial memory (Q4b′)**: hostile pre-gate = raw ranges only (input-linear); accepted post-gate ≤ input-linear + `max-mux-total-span` values (§2 Q4 derivation) — same resource class as the parser's own `List Char` materialization.
- Post-arc benchmark run per standing policy (`feedback_hot_path_refactor_benchmark`): rebuild `.so` first, verify `CMAKE_BUILD_TYPE=Release`, WSL2 bands (±5% back-to-back, ±10% session-distant), report raw/baseline/delta/stddev.
- Type-check heap: Partition/BodyBridge/Universal stay the heavy modules; all new heavy elaboration is confined to the slim (head-dispatch single-step reduction) and the DSL roundtrip (generic `roundtrip` call); the finalize gate adds one rewrite to stage 2. `-M16G` cap is the tripwire.

---

## 9. Slice A.3 (nested `m<N>M`) — sketch and architectural prerequisites

**Scoped OUT of A.1.** What A.1 already buys: nested third-party files bind covered `When` signals to their true parents at runtime (attach overwrites the interim binding, §1.4 — covered signals only), and the SG_-line DSL already round-trips `BothMux` (`Format/SignalLine.agda:109-114` `bothMuxFmt`, priority `IsMux > BothMux > SelBy > NotMux`) — so A.3's syntax costs nothing at the `RawSignal` level.

What A.3 must change:

1. **Emitter** — `emitMuxMarker-chars : Maybe (List Char) → …` becomes masters-set-based:
   ```agda
   collectMasters : List DBCSignal → List (List Char)   -- names referenced by any When
   emitMuxMarker-chars : (masters : List (List Char)) → (thisName : List Char) → SignalPresence → List Char
   -- Always ∧ self ∈ masters → " M";  When _ (v ∷ _) ∧ self ∈ masters → " m<v>M";
   -- When _ (v ∷ _) → " m<v>";  Always → ""
   ```
   Signature cascade into `emitSignalLine-chars`/`emitMessage-chars` + every β-prefix lemma over them (`feedback_beta_prefix_lemma_pattern`) — mechanical but wide.
2. **`MasterCoherent` is deleted, replaced by a mux-forest predicate** (all four pillars break: master-presence-Always, single-name, first-hit agreement, one-master):
   ```agda
   record MuxParentsWF (sigs : List DBCSignal) : Set where
     field
       parents-exist : All (λ s → ∀ (m : Identifier) (vs : List⁺ ℕ)
                          → DBCSignal.presence s ≡ When m vs
                          → Σ[ p ∈ DBCSignal ] (p ∈ sigs
                              × Identifier.name (DBCSignal.name p) ≡ Identifier.name m)) sigs
   ```
   Acyclicity is NOT needed for the round-trip (attach is a value-level overwrite); it remains a validator concern (CHECK 5 `MultiplexorCycle`), keeping the proof-side predicate minimal.
3. **The per-message claim's projection becomes message-level**, not per-signal: `parseMessage ∘ emit ≡ just (interimMuxMsg msg)` where `interimMuxMsg` rebinds every `When` signal to the block's scan-master (`findMuxName` over the emitted markers — the first signal whose name ∈ masters) with the head singleton. Collection policy (iii) guarantees an `SG_MUL_VAL_` line per `When` signal, so the attach bridge (`attachMuxVals … (map interimMuxMsg …) ≡ …`) erases the interim parent choice entirely — the Layer-A/Layer-1 lookup machinery from A.1 is reused unchanged; only the "cleared form" changes shape. This is why (iii) is the A.3-enabling choice.
4. **Resolve-layer rewrite** (~660-line module): `SigOK`/`all-sigOK-*`/`resolveSignalList-roundtrip` restated against the interim projection; `findMuxName-finds-master` generalizes to "finds the first master-marked signal". `resolvePresence`/`findMuxName` runtime functions stay as-is.
5. `WellFormedTextDBCAgg` net effect: `mc` replaced by the strictly-weaker `MuxParentsWF` — the last mux-shaped wall reduces to "every referenced parent exists in-message" (which validator CHECK 4 `MultiplexorNotFound` already enforces error-class → this wall becomes dischargeable from validity, closing another E.2 gap).

Estimated A.3 delta: ~1,000–1,500 new/restated lines, dominated by the Resolve rewrite; runtime delta is tiny.

---

## 10. Risk register

| # | Risk | Likelihood | Mitigation / fallback |
|---|---|---|---|
| 1 | `Refine/MuxVals` Layer-1 balloons past the VAL_ analogue | Medium | Copy-adapt VAL_'s exact lemma skeleton (the repo pattern); G-A22/`feedback_step_back_when_proofs_balloon` checkpoint at ~500 LOC per construct; facade-split at ~700 LOC. Do NOT attempt a lens-generic refactor of the three attach bridges |
| 2 | Stuck `v ∸ v` / `v ≤ᵇ v` discovered inside a parser goal | Pre-empted | §5.1/§5.5 discharge lemmas (incl. the corrected non-refl head case) written BEFORE the slim; cong-only explicit wrapper throughout |
| 3 | `emit`-bridge not eta-refl | Low (rev 2: dissolved by the shared-`ranges` design — both sides traverse `RawMuxVal.ranges`, the MsgSenders :83-87 precedent) | If Q4 reverts to the values-carrying Design A, budget the ~15–30-line `map-∘` + cong-concat bridge (§5.3 note); fix the emitter shape, never the proof (`feedback_concatmap_foldr_bridge`) |
| 4 | Partition/BodyBridge/Universal heap blow-up on 9th chunk **or the finalize gate rewrite** | Low-Med | Two-stage `outcome-subst` already isolates finalize; the gate is a plain `if` on a `let`-bound fold reduced by `totalMuxSpan-collect` + definitional `0 ≤ᵇ k`; keep every new equation `trans`/`cong`-chained; -M16G tripwire → reshape, don't bump |
| 5 | `attachToSignalMux-clearVds-commute` not refl-style (both passes touch the same signal list — unlike senders×vds) | Certain (planned) | Budgeted Maybe-elim helper (~60–90 lines, §5.8); NOT a surprise |
| 6 | Hidden `WellFormedTextPresence`/`WellFormedTextSignal` consumers beyond the enumerated sites (§5.6 now lists the full SignalList four-bridge set) | Low | `rg -n "WellFormedTextPresence\|presence-wf\|wftp-" src/` before step 7c; prune or restate |
| 7 | `expectedMuxFor`/`expectedRawOfDBC` pattern-match the singleton tail somewhere | Very low (rev 2: `expectedMuxFor` verified tail-general at SignalList.agda:108) | Grep + read at execution (7b) for any OTHER consumer |
| 8 | Format-DSL `withWSOpt`-after-comma slot interacts badly with `many` termination (comma-list stop must reject `,` AND accept the ws-emit-empty canonical form) | Medium | Slot-by-slot WS audit per `feedback_format_dsl_ws_family_discipline` in step 4, with the live `", "` fixture (`multiplexing.dbc:25`) in the parity tests; fallback: strict no-ws-after-comma DSL (canonical), documenting the acceptance regression — surface to user if hit |
| 9 | The corpus/parity flip (§7) surfaces disagreement about the NEW expected values | Low-Med | The new `multiplexing.json` values are derivable by hand from the fixture (§7); put them in the execution-kickoff decision list so the user ratifies the semantic flip before the snapshot regen lands |
| 10 | A demand-trigger file uses nested mux (A.3 shapes) on day one | Medium | A.1 binds its covered signals correctly at runtime (§1.4); the proof and `m<N>M` emission follow in the A.3 slice — set that expectation in the trigger conversation, incl. the not-Vector-canonical output caveat |
| 11 | The finalize gate's helper-split restructuring perturbs the existing `TrailingInput`/`AttributeRefinementFailed` arm proofs | Low-Med | The split preserves the with-chain shape inside `finalizeCollected`; the stage-2 rewrites walk it as before; if the elaborator balks, fall back to gating INSIDE `finalizeCollected` before its `with` (same reductions) |
| 12 | Drift between this document and the tree at execution time | Certain over months | §12.3 re-verification pass is a mandatory step 0; lemma NAMES (not line numbers) are the anchors |

---

## 11. Acceptance criteria (slice A.1 "done")

**Theorems that must exist** (exact names):
- `parseText-on-formatText` (Substrate/Unsafe — unchanged statement) and `parseTextChars-on-formatChars` (Universal) type-check with `MessageWF` containing **no** `wfps` field and `WellFormedTextPresence` **absent from the codebase** (`rg WellFormedTextPresence src/` → 0 hits).
- `parseMessage-roundtrip-bundled` / `parseMessages-roundtrip` at `clearAllMsg` / `map clearAllMsg`; `parseTopStmt-on-emit-TM-eq` at `TSMessage (clearAllMsg msg)`.
- `resolveSignalList-roundtrip` with no presence-shape hypothesis, target `just (map clearVds (map truncSig sigs))`.
- `parseMuxVals-format-roundtrip`, `parseSigMulVal-roundtrip`, `parseTopStmt-on-emit-TMV-eq`, `rangesValidᵇ-degenerate`, `expandRanges⁺-degenerate`, `totalMuxSpan-collect`, `collectMuxVals-stops`.
- `map-attachToMessageMux-on-clearMuxMsgs-collected` (Refine/MuxVals) and `attachSenders-attachValueDescs-attachMuxVals-on-clearAllMsgs-collected` (MuxCompose).

**Gates**: all of `build`, `check-properties`, `check-proof-coverage`, `check-invariants`, `check-no-properties-in-runtime`, `check-erasure`, `check-fidelity`, `check-ffi-exports` green at head SHA (`feedback_gate_claim_integrity`); binding suites + tree-wide lint green; `tools/run_ci.py` full sweep pre-merge.

**User-visible behavior**:
1. A DBC text file with `SG_MUL_VAL_ 291 SigX Mode 3-3,5-5,7-7 ;` loads with `SigX.multiplex_values == [3,5,7]` in all four bindings; `… Mode 3-5, 10-12;` (the corpus shape) loads `[3,4,5,10,11,12]` bound to the line's named parent (today: head-marker value bound to the interim first master).
2. `format_dbc_text` on a JSON-built DBC with multi-value presence emits `SG_MUL_VAL_` lines; text→parse→format→parse is a fixpoint on the fixture set.
3. **Resource bound (typed)**: a file whose ranges sum to span > `max-mux-total-span` (e.g. one `0-4294967295` line) is rejected with `input_bound_exceeded` / `bound_kind == "mux_range_span_total"` carrying observed+limit, at bounded memory (nothing expanded pre-gate). **Wire validity (positioned)**: `5-3` (inverted) or an out-of-range CAN ID rejects with a byte-positioned parse error at that line. Both are NEW rejects on a previously drop-parsed line — CHANGELOG'd per §7.
4. Nested third-party files: every `When` signal covered by an `SG_MUL_VAL_` line attaches to its TRUE parent (the latent first-master mis-assignment is gone for covered signals) — runtime test on `multiplexing.dbc`; proof + `m<N>M` emission deferred to A.3; uncovered nested children unchanged (wire-ambiguous — §1.4).
5. **Existing-corpus flip shipped**: `parity_snapshots/multiplexing.json` regenerated (values per §7) with all three binding consumers green; kitchen_sink re-verified; corpus README updated.
6. FEATURE_MATRIX row `dbc_extended_mux_text` present ×4 with parity tests; CHANGELOG (incl. the compat/Changed framing)/PROTOCOL/DEFERRED_ITEMS updated in the same arc.

**Non-goals of A.1** (explicit): `m<N>M` emission (emitted nested text is value-faithful but not Vector-canonical), `MasterCoherent` replacement, correct parent-binding for `SG_MUL_VAL_`-uncovered nested children, `attr-wfs`/`pvs`/`unresolved-empty` walls, byte-stability of formatter output.

---

## 12. Do-nothing-yet trigger (rev 2 — reworded; the rev-1 letter had already fired on the in-tree corpus)

**Carve-out**: the repo's own coverage corpus (`python/tests/fixtures/dbc_corpus/` — self-authored, drop-semantics deliberately pinned in the parity snapshots, README-documented) and the `NS_` keyword-list occurrences in `examples/`/fixtures do NOT constitute demand; they are the coverage instrument this plan will flip when executed (§7).

**12.1 The gate fires when any of**:
- **external demand**: a user/third-party DBC (support request, real integration, or a newly *contributed* fixture from outside) containing `SG_MUL_VAL_` with multi-value ranges or nested selectors, or a user reports head-only truncation / wrong-parent binding after a text round-trip;
- a binding consumer needs `format_dbc_text` fidelity for multi-value presence built via the JSON path (e.g., a JSON→text export pipeline);
- E.2 closure is re-prioritized and route (a) is chosen over the alternatives (the `wfps` wall has no other route).

**12.2 Detection**: `rg -l "SG_MUL_VAL_"` over *incoming* files/issues (NOT the carve-out paths); validator/CLI complaints referencing multiplex values; DEFERRED_ITEMS A.1 stands at INVESTIGATE until then.

**12.3 On firing, before any code**: (1) re-verify §1's facts against the then-current tree (`git log --oneline -- src/Aletheia/DBC/` since 2026-07-12; re-read the six template modules, the four wfps consumption sites, and `finalizeParse`/`ParseDBCText`); (2) put Q1–Q5 + the `max-mux-total-span` value + the §7 compat/snapshot-flip framing to the user with this document attached; (3) confirm the A.2 lesson set (`proof_tactics_index`) for new entries added since; (4) execute §6.

---

## 13. Size estimate

- **Slice A.1**: ≈ **2,050–2,750 new lines** (runtime ~380–470 incl. the gate/error plumbing; Format DSL ~300–380; proof ~1,350–1,900) **+ ~750–950 restated lines** across ~27 files — roughly **1.7–2.1× the A.2 arc** (+1,865/−271, 28 files), the delta concentrated in `Refine/MuxVals` (VAL_ class), the range codec + span plumbing, the SignalList/Message wftp-drop set, and the Partition/BodyBridge 9-chunk cascade; the `SendersCompose`-reuse, no-alt-dispatcher, and shared-list emit-bridge savings pull the low end down. Estimated **9–14 focused sessions** at the A.2 pace, +1–2 for bindings/matrix/snapshot-regen/docs/benchmarks. Q3=B adds ~2–3 sessions (wire audit across 4 bindings + the Marshal/check-fidelity/check-erasure fallout).
- **Slice A.3**: additional ~1,000–1,500 lines (Resolve-layer projection rewrite + marker emitter cascade + `MuxParentsWF`), **5–8 sessions**, contingent on A.1's collection policy (iii).
