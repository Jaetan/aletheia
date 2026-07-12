> **Provenance** — rev. 2 (post-adversarial-panel) proof strategy for E.2 route (c),
> produced 2026-07-12 by the multi-agent deep-dive indexed in
> [E2_PROOF_STRATEGY.md](E2_PROOF_STRATEGY.md) (method, panel record, scheduling).
> Route ranking and the E.2 schedule live in [DEFERRED_ITEMS.md](DEFERRED_ITEMS.md) § E.2.
> File:line references are pinned to the 2026-07-12 tree (post-#176 `e9d609f9` plus the
> E.2 accuracy batch); re-verify them against the current tree before executing.

# E.2 closure, route (c) salvage — proof strategy: validator-backed advisory closure of `WellFormedTextDBCAgg` (rev. 2, post-panel)

**Status**: strategy document (no code written). Every file:line cited below was re-verified against the working tree on 2026-07-12, including all lines cited by the adversarial panel. Changes from rev. 1 are integrated in place; the wire-code bridge (§4.7) is new and closes the panel's major proof-gap finding; the Rust enum-growth question (§12.1) is the one genuinely open maintainer decision.

---

## 0. Verdict on the reframe — DEFENDED, and sharpened

The re-examination's claim — *standalone route (c) cannot close E.2* — is *confirmed* by the code, link by link:

1. `When m (v ∷ v' ∷ vs)` is a well-typed `SignalPresence` (model-legal).
2. The JSON wire round-trips the full selector array (`JSONParser.agda` `multiplex_values`).
3. The runtime engine *honors* it: `matchMuxValue` folds over `List⁺.toList muxValues` (`src/Aletheia/CAN/SignalExtraction.agda:45-56`), and `checkPresenceP` walks arbitrary *nested* mux chains (:83-91) — multi-value and chained mux are first-class extraction semantics.
4. Text emission is lossy: `emitMuxMarker-chars _ _ (When _ (v ∷ _)) = " m" ++ showℕ v` — head only (`src/Aletheia/DBC/TextFormatter/Topology.agda:147-148`); no `SG_MUL_VAL_` emitter exists; the parser drops `SG_MUL_VAL_` as `Parser ⊤` (`src/Aletheia/DBC/TextParser/ExtendedMux.agda`, `parseSigMulVal`).

Hence for any `d` containing a multi-value selector, `parseText (formatText d) ≢ inj₂ d`, so `errorIssues ≡ [] → Agg` is unprovable unless an error-class check *refuses* a construct that is model-legal, wire-legal, and engine-honored. A standalone (c) is also maximally breaking: every new error-class check narrows what `parse_dbc` / `parse_dbc_text` accept across 4 bindings + 3 CLIs (`loadValidatedEpilogue`, `src/Aletheia/Protocol/Handlers/LoadDBC.agda:125-130`).

**The sharpening the landscape missed**: the repo's sound-lemma shape `check … ≡ [] → P` (`Validity/ErrorChecks.agda` throughout) is *severity-independent*. Nothing forces a check to be error-class for its emptiness to carry proof content. Therefore the salvage is:

> **Ship the missing checks as WARNING-class advisories, and state E.2's closure as a conditional theorem over two decidable, runtime-checkable hypotheses**:
>
> `errorIssues (validateDBCFull d) ≡ []  →  textRoundTripAdvisories d ≡ []  →  WellFormedTextDBCAgg d`
>
> composed in `Substrate/Unsafe.agda` with the existing universal theorem into
>
> `parseText (formatText d) ≡ inj₂ d`
>
> **and formally bridged to the wire observable** (§4.7): the second hypothesis is proven equivalent-in-the-needed-direction to "no advisory-profile `code` appears anywhere in `validateDBCFull d`'s output" — the exact criterion the CLI flag / binding helper will test. The severity analogue of this bridge already exists in-repo (`errorIssues-allW` and the `ei-*` kit, `Validity/Composition.agda:61-90`); the code-level mirror is ~120-160 LOC of the same shapes.

This achieves **full conditional closure of E.2** (not the 2-residue partial closure the landscape projected), with **zero acceptance change** — no load-path narrowing, no severity flips, no new error codes. An advisory does not refuse; it reports "this DBC is outside the verified text round-trip envelope, because of field X". That is simultaneously route (b)'s V1 diagnostics.

---

## 1. Candidate dispositions

| # | Candidate | Disposition | Form |
|---|---|---|---|
| 0 | `msg-ids-unique` / `sig-names-unique` bridges | **BUILD** (pure proof) | `AllPairs.map⁺` bridges off CHECK 1/2 soundness; no wire change |
| v | CHECK 15/16 promotion | **DROP** — verdict-neutral (any violator already trips error CHECK 8 or 10: `s ≥ 512 ∧ s+l ≤ dlc·8 ≤ 512 ⟹ l = 0` → CHECK 10; `l > 512 ⟹ s+l > 512 ≥ dlc·8` → CHECK 8). Derive `wf-sigs` instead (pure proof) |
| iii | BE `msb-ge-len` | **BUILD as CHECK 24, IsWarning** (`big_endian_start_bit_underflow`) | required for `pvs`; prerequisite for (b) V1 |
| — | multi-value mux selector (`wfps`) | **BUILD as CHECK 25, IsWarning** (`multi_value_mux_selector`) | the wall, converted to an honest advisory — new vs. the landscape, which left wfps as an unclosable residue |
| ii | `MasterCoherent` | **BUILD as CHECK 26, IsWarning** (`mux_master_incoherent`) | prerequisite for (b) V1; error-class rejected (engine supports nested mux) |
| i | attribute typing | **BUILD as CHECK 27, IsWarning** (`attribute_type_mismatch`) | Bool body + Properties-side reflection; leaf-module extraction for the Handlers heap wall |
| iv | CHECK 23 promotion (`unresolved-empty`) | **NO promotion.** CHECK 23 fires unconditionally per entry (`Checks.agda:604-613`), so `checkAllUnknownValueDescriptionTargets urvds ≡ [] → urvds ≡ []` is a 6-line induction. The conditional-theorem design consumes the existing warning as-is — the landscape's "highest real-world impact" breaking change evaporates |

### Spec-defensibility & ecosystem verdicts (per candidate)

**Evidentiary discipline (revised per panel)**: each verdict below rests on two kinds of grounds, now kept separate. *(in-repo, verified)* grounds cite this repository's code and are load-bearing. *(external, believed-unverified)* grounds concern other tools' behavior (cantools, canmatrix) and OEM-file prevalence; the repo contains no source for them (no DBC_SUPPORT.md; the module headers / PROTOCOL / DEFERRED_ITEMS corroborate only the format-level claims — single-selector `m<N>` base grammar, `SG_MUL_VAL_` extension parsed-and-discarded, single-`M` master). They are stated as belief, add color only, and **no verdict depends on them** — every warning-only verdict is already forced by the in-repo grounds (the engine honors the construct, and/or the predicate over-approximates the defect class).

- **CHECK 24 (BE msb-ge-len)** — *(in-repo, verified)* Not a wire-validity mandate: `pv-BE.msb-ge-len` (`src/Aletheia/DBC/Formatter/WellFormed.agda:75-81`) constrains the *internal* (post-`convertStartBit`) representation and is strictly stronger than wire validity: e.g. frameBytes=1, internal `s=2, l=4` fails `3 ≤ 2` yet `convert ∘ unconvert` round-trips it exactly. It is the *sufficient envelope* of the BE unconvert→convert proof. A genuine sub-class (Motorola positions whose extraction underflows the frame, silently truncated by `convertStartBit`'s `∸`, `src/Aletheia/CAN/Endianness.agda:358-360`) *is* defective, but the predicate cannot separate the two without re-deriving. *(external, believed-unverified)* Likely checked by no mainstream tool. **Verdict: warning only, phrased "outside the verified BE round-trip envelope"; error-class would over-refuse valid files.**
- **CHECK 25 (multi-value selector)** — *(in-repo, verified)* Base DBC grammar's `m<N>` marker carries exactly one selector; multi-value selection exists only via the `SG_MUL_VAL_` extended-multiplexing extension, which the formatter does not emit and the parser discards (`TextParser/ExtendedMux.agda`); Aletheia's own engine honors multi-value selection (`SignalExtraction.agda:45-56`). *(external, believed-unverified)* Extended mux is believed common in OEM body/infotainment DBCs and supported by cantools/canmatrix. **Verdict: warning only — "not expressible in the emitted base-grammar text; will not round-trip until SG_MUL_VAL_ emission lands".**
- **CHECK 26 (master coherence)** — *(in-repo, verified)* Base grammar admits one `M` master per message; chained/multi-group mux is extended-mux territory; Aletheia's engine walks nested chains (`SignalExtraction.agda:83-91`). **Verdict: warning only; error-class contradicts the engine's documented semantics.**
- **CHECK 27 (attribute typing)** — *(spec-based, externally sourced)* The DBC format is understood to mandate that `BA_`/`BA_DEF_DEF_` reference a declared `BA_DEF_` with a type-conformant value; a dangling or ill-typed attribute is spec-invalid. *(external, believed-unverified)* cantools believed lenient by default (strict mode raises), canmatrix believed to warn. *(in-repo, verified)* Attributes are inert metadata for decode. **Verdict: warning now; the single defensible candidate for error-class under a future opt-in strict profile. Do not hard-fail loads on it.**
- **CHECK 23 (dangling VAL_)** — *(in-repo, verified)* the check's own docstring: "user-written DBC slop". **Verdict: keep warning, unchanged.**

### The strict profile — how (ii) rides the wire

Three options, evaluated:

1. **Kernel wire flag** — optional `"profile": "strict_roundtrip"` on `validateDBC`, read in `Routing.tryValidateDBC` (`src/Aletheia/Protocol/Routing.agda:46-49`) via `lookupString`, absent ⇒ default; `ValidateDBC : JSON → StreamCommand` gains a profile argument. **Rejected for V1**: dynamic severity breaks the fixed-severity lemma architecture — every `-allW` lemma (`WarningChecks.agda`) and both Theorem chains assume each check's severity is a constant; severity-parametric checks would double the lemma set for zero proof benefit.
2. **CLI/binding-side code-set interpretation** — **RECOMMENDED**. The advisory codes are already on the wire in `issues[].code`. Define the code-set once in PROTOCOL.md ("text round-trip advisory profile" = the 5 codes in §11), and let `aletheia validate --strict-roundtrip` (×3 CLIs) / a binding helper (`result.roundtrip_clean()`) exit 1 / return false when any is present. Zero kernel change, zero *runtime* proof change, full parity via CLI_SCENARIOS + parity tests. Ship-when-wanted. **Formal backing (new, §4.7)**: the kernel-side observable this interprets — "no advisory code in `validateDBCFull d`'s output" — is *proven* to imply the theorem hypothesis (`advisoryWireClean⇒advisoriesEmpty`). The residual, explicitly documented trust step is binding-side only: the CLI/helper matches wire *strings*, and the string↔`IssueCode` mapping (`formatIssueCode`) is pinned by parity tests + CLI scenarios rather than proven — the identical treatment every existing wire surface gets (severity strings, `has_errors`, error codes). An optional closed-term reflection lemma can shrink even that (§12.5).
3. **Load-path strict mode** (`parse_dbc(strict=...)`) — deferred; buildable later on the same code-set; maintainer decision.

A fourth option surfaced during revision (recorded for completeness, not recommended for V1): the kernel could compute and emit a `roundtrip_clean` boolean on `validateDBC` responses (mirroring `has_errors`, which is kernel-computed via `hasAnyError`, `Validator/Formatting.agda`). This would move the membership test kernel-side at the cost of a wire-shape addition; it composes with option 2 later. See §12.5.

---

## 2. Module layout

Legend: **[R]** runtime-legal (reachable from Main's closure, compiled by MAlonzo), **[P]** proof tree (reached by `check-properties`, never by `build`). All modules: `{-# OPTIONS --safe --without-K #-}` except the one existing allowlisted Unsafe module.

### New modules

| Path | Tree | Purpose |
|---|---|---|
| `src/Aletheia/DBC/MuxTopology.agda` | [R] leaf | `findMuxMaster`, **moved verbatim** from `TextFormatter/Topology.agda:127-131`; imports only `Data.List`, `Data.Maybe`, `Aletheia.DBC.Types`, `Aletheia.DBC.Identifier`. `TextFormatter.Topology` then does `open import Aletheia.DBC.MuxTopology public` so `Formatter.WellFormedText`'s `MasterCoherent` (indexed over `findMuxMaster`) and all existing proofs are untouched (same definition, re-exported). |
| `src/Aletheia/DBC/AttrLookup.agda` | [R] leaf | `collectDefs`, `lookupDef`, `nthLabel` moved from `TextFormatter/Attributes.agda:84-104`; `findLabel` moved from `TextParser/Attributes.agda:519-524`. The two existing `lookupDef`s are **textual clones** (verified: both `if ⌊ ListProps.≡-dec _≟ᶜ_ name (AttrDef.name d) ⌋ then just d else …`), so the leaf hosts ONE and both former hosts re-export it publicly (`open import Aletheia.DBC.AttrLookup public using (…)`) — `WFAttribute`'s references to `ParserAttrs.lookupDef` keep meaning definitionally; any existing agreement lemma becomes refl-provable and still checks. |
| `src/Aletheia/DBC/Validity/AdvisoryChecks.agda` | [P] facade + **proofModules root** | `BEStartBitOK` predicate; CHECK 24 + 25 + CHECK 23 sound/complete; the advisory-code filter kit and the wire bridge (§4.7); re-exports the two submodules (which the walk therefore covers transitively). |
| `src/Aletheia/DBC/Validity/AdvisoryChecks/MasterCoherence.agda` | [P] | CHECK 26 sound (+ conditional complete); `findSignalInList-∈`; presence-Bool reflection lemmas; CHECK 26 `-allC` lemma. |
| `src/Aletheia/DBC/Validity/AdvisoryChecks/Attributes.agda` | [P] | CHECK 27 sound/complete; the three Bool-reflection lemmas onto `WfAttrType` / `ValueMatchesType` / `DefaultEnumOK`; CHECK 27 `-allC` lemma. |
| `src/Aletheia/DBC/TextParser/Properties/AggFromValidator.agda` | [P] + **proofModules root** | The assembly: signal/message/DBC-level derivations, the bridges, and `aggFromValidatorClean`. |

**Why a new `AdvisoryChecks` family instead of `WarningChecks` (explicit rationale, per panel — this is a deliberate, necessary deviation to be ratified, not drift).** The existing convention co-locates each warning check's severity + soundness/completeness in `Validity/WarningChecks.agda` (its header commits to exactly that, `WarningChecks.agda:5-11`). The four new checks **cannot** follow it: their soundness targets are `WellFormedTextPresence` / `MasterCoherent` (defined in `Formatter/WellFormedText.agda`) and `WFAttribute` (defined in `Properties/Aggregator/Foundations.agda`). `Theorem.agda` imports `WarningChecks` (`Theorem.agda:50-59`) and is a warm proof root (`Shakefile.hs:408`); hosting those sound lemmas in `WarningChecks` would drag the Formatter/TextParser proof closures into every warm `check-properties` run of the Theorem root — precisely the closure-weight coupling the repo's heavy-import lessons forbid. The split is therefore: **`-allW` severity lemmas** (which need only the check bodies + `IsWarning`) stay in `WarningChecks` per convention and feed `Theorem.completeness`; **sound/complete/`-allC` lemmas** live in the `AdvisoryChecks` subtree, whose closure joins the Formatter/Foundations trees only under its own root. `WarningChecks.agda`'s header gets a two-line note recording this (its "all 8 warning checks" count is already stale — there are 13 pre-change — and will be restated as a formula-free pointer per the numbers-in-prose rule).

### Changed modules

| Path | Tree | Change |
|---|---|---|
| `src/Aletheia/DBC/Types.agda` | [R] | +4 `IssueCode` constructors (after `UnknownValueDescriptionTarget`, `Types.agda:355-376`) |
| `src/Aletheia/Protocol/ResponseFormat.agda` | [R] | +4 `formatIssueCode` clauses |
| `src/Aletheia/DBC/Validator/Checks.agda` | [R] | +4 check bodies + Bool helpers (~150 LOC); new imports: `Aletheia.DBC.MuxTopology`, `Aletheia.DBC.AttrLookup`, `Aletheia.CAN.Endianness using (LittleEndian; BigEndian)`, `Aletheia.DBC.DecRat.Refinement using (natDecRatToℕ)`, `Data.List.NonEmpty using (_∷_)`, `Data.Maybe.Properties renaming (≡-dec to ≡-decᴹ)`, `Data.String using (fromList)`, `Relation.Nullary.Decidable using (⌊_⌋)`, `Data.List using (all)` |
| `src/Aletheia/DBC/Validator.agda` | [R] | `validateDBCFull` (currently 22 arms, `Validator.agda:30-58`) gains 4 trailing `++ₗ` arms (strictly APPENDED after CHECK 23 — see §7 ordering rule); new `textRoundTripAdvisories` |
| `src/Aletheia/DBC/Validity/WarningChecks.agda` | [P] | +8 `-allW` lemmas (per-element + lifted, 4 checks); header note on the AdvisoryChecks split (above) |
| `src/Aletheia/DBC/Validity/Theorem.agda` | [P] | `completeness` gains 4 `ei-combine` nesting levels. **Precise diff shape (revised per panel)**: the current innermost arm at `Theorem.agda:149` — `(errorIssues-allW _ (checkAllUnknownValueDescriptionTargets-allW urvds))` — is itself REWRITTEN: it becomes the first component of the first new `ei-combine` (the appended arms extend the right-associated `++ₗ` tail *inside* the CHECK-23 level), with the 4 new levels nested after it, each closed by `errorIssues-allW _ (checkAll*-allW …)`; the closing-paren chain at :150 grows by 4. The import blocks also grow by 8 names: +4 `checkAll*` in the `Validator using` block (:15-28) and +4 `-allW` in the `WarningChecks using` block (:50-59). **`soundness` is textually UNCHANGED** (panel-verified): its `where`-chain peels prefixes in concatenation order with inferred `_` tails and stops at `s₁₀` (`Theorem.agda:99`, CHECK 10 at position 11 of 22); arms appended at the tail are absorbed by the inferred tails. The landscape's "~11 extra ei-splits" cost applied only to the now-dropped promotion variant. ~20 LOC total. |
| `src/Aletheia/DBC/JSONParser/MessageWF.agda` | [P] | `dlcBytes-bounded : ∀ (d : DLC) → dlcBytes d ≤ 64` (**currently inside the `private` block at :50-67 — the landscape missed this**) lifted out of `private`, in place. 5-line diff. |
| `src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda` | allowlisted | +`parseText-on-formatText-validated` corollary and +`parseText-on-formatText-advisory-wire` corollary (§4.6). Must live here: they consume `parseText-on-formatText`, and importing a non-`--safe` module forfeits `--safe`; single-Unsafe-module policy. |
| `src/Aletheia/Protocol/Handlers/FormatDBCText.agda` | [R] | docstring rewrite only (its "MessageWF / WFAttribute are NOT discharged" caveat, :100-113, is superseded by the new theorem; the best-effort contract note at :115-120 stays) |
| `Shakefile.hs` | — | **+2 explicit `proofModules` roots, added in the same commit that creates each module** (revised per panel — this is required, not "only if needed"): `Validity/AdvisoryChecks.agda` at step 4 and `TextParser/Properties/AggFromValidator.agda` at step 5. Rationale: `check-proof-coverage` (`Shakefile.hs:600-611`) requires every `src/` module to be reachable from `build` or the proofModules walk; until the step-6 Unsafe capstone imports them, the new [P] modules would otherwise be uncovered — failing any intermediate full `run_ci` / pre-push (which scans the working tree), and, worse, making step-4's `check-properties` a **false green** (it would not type-check the new modules at all). Explicit roots for not-yet-imported proof modules are the established pattern (`WellFormedFromValidity` root with exactly this justification, `Shakefile.hs:437`; A.2 interim roots :442-462). The roots stay after step 6 — redundant coverage alongside the `Substrate/Unsafe` root (:470) is harmless and precedented (`TextParser/Properties` root :411 coexists with it). |

`check-no-properties-in-runtime` (`Shakefile.hs:581-598`) is respected by construction: no runtime module gains a `.Properties` import; the check bodies are Bool/Dec-valued with all Set-level predicates (`WellFormedTextPresence`, `MasterCoherent`, `WFAttribute`, `ValueMatchesType`) referenced only from [P] modules.

---

## 3. Wire additions (frozen once shipped — see §12)

```agda
-- Aletheia.DBC.Types (append to IssueCode, after UnknownValueDescriptionTarget)
  BigEndianStartBitUnderflow : IssueCode
  MultiValueMuxSelector      : IssueCode
  MuxMasterIncoherent        : IssueCode
  AttributeTypeMismatch      : IssueCode
```

```agda
-- Aletheia.Protocol.ResponseFormat
formatIssueCode BigEndianStartBitUnderflow = "big_endian_start_bit_underflow"
formatIssueCode MultiValueMuxSelector      = "multi_value_mux_selector"
formatIssueCode MuxMasterIncoherent        = "mux_master_incoherent"
formatIssueCode AttributeTypeMismatch      = "attribute_type_mismatch"
```

`AttributeTypeMismatch` is ONE code with detail-string variants (unknown def / ill-typed value / enum-index bridge / empty ENUM), matching `UnknownCommentTarget`'s one-code-many-details style and echoing #150's `AttrRefineCause` vocabulary (`UnknownAttrDef` / `IllTypedValue`, `src/Aletheia/Error.agda:395`). Splitting into two codes is an open question (§12.3).

**Binding-surface consequence (revised per panel — maintainer decision, §12.1).** "Wire-additive" is NOT automatically "API-additive" in every binding:

- **Rust**: `pub enum IssueCode` (`rust/src/response.rs:155-201`) carries `#[derive(Debug, Clone, PartialEq, Eq)]` and is **not** `#[non_exhaustive]` (verified: no occurrence in the file). Adding 4 variants is a source-level breaking change for any downstream exhaustive `match` — cargo-semver-checks classifies `enum_variant_added` as major. The `Unknown(String)` fallback (:200) gives wire/runtime forward-compatibility only; notably, the enum's own docstring already anticipates growth ("the code set may grow", :151-154), but anticipation is not a ratified policy.
- **C++**: `enum class IssueCode` (`cpp/include/aletheia/validation_issue.hpp:16`, `Unknown` enumerator :38) — a weaker analogue: new enumerators can surface downstream `-Wswitch`-exhaustiveness warnings (errors under `-Werror`). Same policy question, softer teeth.
- **Go**: `type IssueCode string` with const values (`go/aletheia/result.go:175`, :219) — purely additive-safe.
- **Python**: str-valued enum members (`python/aletheia/codes/_issue.py:46`) — additive-safe (no enforced exhaustiveness).

The options are presented complete in §12.1; **this document does not pre-decide**. Until decided, the CHANGELOG entry (§6) must not claim "Not BREAKING" unqualified.

---

## 4. New definitions and lemmas — signatures + proof approach

### 4.1 Runtime check bodies (`Aletheia.DBC.Validator.Checks`, cold path, Dec/Bool acceptable per the cat-26 header `Checks.agda:13-21`)

**CHECK 24 — BE start-bit underflow** (fits the CHECK-4 `with` shape; `requireDec` on the BE arm):

```agda
checkBEStartBitUnderflow : String → DBCSignal → List ValidationIssue
checkBEStartBitUnderflow msgName sig with DBCSignal.byteOrder sig
... | LittleEndian = []
... | BigEndian    =
  requireDec (SignalDef.bitLength (DBCSignal.signalDef sig) ∸ 1
              ≤? SignalDef.startBit (DBCSignal.signalDef sig))
             (mkIssue IsWarning BigEndianStartBitUnderflow
               ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
                ++ₛ "': big-endian signal outside the verified round-trip envelope (bitLength - 1 > startBit)"))

checkAllBEStartBitUnderflow : List DBCMessage → List ValidationIssue
checkAllBEStartBitUnderflow = liftPerSignal checkBEStartBitUnderflow
```

**CHECK 25 — multi-value mux selector** (direct `List⁺` pattern split; no Dec needed):

```agda
checkMultiValueMuxSig : String → DBCSignal → List ValidationIssue
checkMultiValueMuxSig msgName sig with DBCSignal.presence sig
... | Always              = []
... | When _ (_ ∷ [])     = []
... | When muxName (_ ∷ _ ∷ _) =
      mkIssue IsWarning MultiValueMuxSelector
        ("Message '" ++ₛ msgName ++ₛ "', signal '" ++ₛ signalNameStr sig
         ++ₛ "': multi-value mux selector requires SG_MUL_VAL_ (not emitted by the text formatter); text round-trip not covered") ∷ []

checkAllMultiValueMux : List DBCMessage → List ValidationIssue
checkAllMultiValueMux = concatMap λ msg →
  concatMap (checkMultiValueMuxSig (messageNameStr msg)) (DBCMessage.signals msg)
```

**CHECK 26 — master coherence.** Bool helpers take `SignalPresence` directly — the exact `MuxUnitScaling` precedent (`Validity.agda:185-189`: "Takes SignalPresence directly (not DBCSignal) to allow pattern matching without where-blocks, which are opaque to external proofs"):

```agda
presenceIsAlwaysᵇ : SignalPresence → Bool
presenceIsAlwaysᵇ Always     = true
presenceIsAlwaysᵇ (When _ _) = false

muxRefsMasterᵇ : List Char → SignalPresence → Bool
muxRefsMasterᵇ _      Always     = true
muxRefsMasterᵇ master (When m _) = Identifier.name m ≡csᵇ master

allRefsMasterᵇ : List Char → List DBCSignal → Bool
allRefsMasterᵇ master = all (muxRefsMasterᵇ master ∘ DBCSignal.presence)

checkMasterCoherence : String → List DBCSignal → List ValidationIssue
checkMasterCoherence msgName sigs with findMuxMaster sigs
... | nothing     = []
... | just master with findSignalInList master sigs
...   | nothing        = mkIssue IsWarning MuxMasterIncoherent
                           ("Message '" ++ₛ msgName ++ₛ "': mux master not found") ∷ []
...   | just masterSig with presenceIsAlwaysᵇ (DBCSignal.presence masterSig)
                             ∧ allRefsMasterᵇ master sigs
...     | true  = []
...     | false = mkIssue IsWarning MuxMasterIncoherent
                    ("Message '" ++ₛ msgName ++ₛ "': mux group is not single-master/flat (nested or multi-master mux; text emission covers one master with Always presence)") ∷ []
```

(The lift is `concatMap (λ msg → checkMasterCoherence (messageNameStr msg) (DBCMessage.signals msg)) msgs` — a per-*message* check, one `liftConcatMap` level, unlike the per-signal doubles.)

**CHECK 27 — attribute typing** (Bool body; predicates stay in the Properties tree):

```agda
wfAttrTypeᵇ : AttrType → Bool
wfAttrTypeᵇ (ATEnum []) = false
wfAttrTypeᵇ _           = true

valueMatchesTypeᵇ : AttrType → AttrValue → Bool   -- 5 true clauses + catch-all false
defaultEnumOKᵇ    : AttrType → AttrValue → Bool
-- defaultEnumOKᵇ (ATEnum ls) (AVEnum n) =
--   ⌊ ≡-decᴹ _≟_ (findLabel (nthLabel (natDecRatToℕ n) ls) ls) (just (natDecRatToℕ n)) ⌋
-- defaultEnumOKᵇ _ _ = true

checkAttrTyping : List AttrDef → DBCAttribute → List ValidationIssue
-- DBCAttrDef d:     with wfAttrTypeᵇ (AttrDef.attrType d)     → [] / empty-ENUM issue
-- DBCAttrDefault d: with lookupDef (AttrDefault.name d) defs  → unknown-def issue /
--                   with valueMatchesTypeᵇ … ∧ defaultEnumOKᵇ … → [] / ill-typed issue
-- DBCAttrAssign a:  with lookupDef (AttrAssign.name a) defs   → unknown-def issue /
--                   with valueMatchesTypeᵇ …                   → [] / ill-typed issue

checkAllAttrTyping : List DBCAttribute → List ValidationIssue
checkAllAttrTyping attrs = concatMap (checkAttrTyping (collectDefs attrs)) attrs
```

**Composites** (`Aletheia.DBC.Validator`):

```agda
validateDBCFull dbc = …existing 22 arms unchanged, then…
     ++ₗ checkAllBEStartBitUnderflow msgs
     ++ₗ checkAllMultiValueMux msgs
     ++ₗ checkAllMasterCoherence msgs
     ++ₗ checkAllAttrTyping attrs

textRoundTripAdvisories : DBC → List ValidationIssue
textRoundTripAdvisories dbc =
  let msgs = DBC.messages dbc; attrs = DBC.attributes dbc
  in checkAllBEStartBitUnderflow msgs
     ++ₗ checkAllMultiValueMux msgs
     ++ₗ checkAllMasterCoherence msgs
     ++ₗ checkAllAttrTyping attrs
     ++ₗ checkAllUnknownValueDescriptionTargets (DBC.unresolvedValueDescs dbc)
```

`textRoundTripAdvisories` re-invokes the same check functions `validateDBCFull` calls on the same inputs (CHECK 23 included), so its issues are definitionally the corresponding slices of the validator output; the duplicate computation only runs on the diagnostics/theorem path (cold).

### 4.2 Advisory soundness (`Aletheia.DBC.Validity.AdvisoryChecks` + submodules, [P])

```agda
-- facade -------------------------------------------------------------
BEStartBitOK : DBCSignal → Set
BEStartBitOK sig = DBCSignal.byteOrder sig ≡ BigEndian
  → SignalDef.bitLength (DBCSignal.signalDef sig) ∸ 1
      ≤ SignalDef.startBit (DBCSignal.signalDef sig)

checkBEStartBitUnderflow-sound : ∀ msgName sig →
  checkBEStartBitUnderflow msgName sig ≡ [] → BEStartBitOK sig
checkBEStartBitUnderflow-complete : ∀ msgName sig →
  BEStartBitOK sig → checkBEStartBitUnderflow msgName sig ≡ []
checkAllBEStartBitUnderflow-sound : ∀ msgs →
  checkAllBEStartBitUnderflow msgs ≡ [] →
  All (λ m → All BEStartBitOK (DBCMessage.signals m)) msgs
-- (+ lifted complete)
```
*Approach*: mirror `checkMuxFoundSig-sound` (`ErrorChecks.agda:280-296`) — one `with DBCSignal.byteOrder sig` shared between body and proof; LE arm returns `λ boEq → ⊥` closed by `()` on `LittleEndian ≡ BigEndian`; BE arm is `requireDec-sound`/`-complete` one-liners; lift via `liftConcatMap-sound` twice (through `liftPerSignal`). ~40 LOC.

```agda
checkMultiValueMuxSig-sound : ∀ msgName sig →
  checkMultiValueMuxSig msgName sig ≡ [] →
  WellFormedTextPresence (DBCSignal.presence sig)
-- (+ complete, + All lifts)
```
*Approach*: `with DBCSignal.presence sig`; `Always → wftp-always`; `When _ (_ ∷ []) → wftp-when-single`; `When _ (_ ∷ _ ∷ _)` arm has hypothesis `issue ∷ [] ≡ []`, closed by `()`. Complete: match the `WellFormedTextPresence` witness (its two constructors pin the presence shape). ~35 LOC.

```agda
checkAllUnknownValueDescriptionTargets-sound : ∀ urvds →
  checkAllUnknownValueDescriptionTargets urvds ≡ [] → urvds ≡ []
```
*Approach*: induction on `urvds`; nil is `refl`; cons reduces the `concatMap` to `issue ∷ …`, hypothesis closed by `()`. Complete direction is `λ { refl → refl }`. ~8 LOC.

```agda
-- AdvisoryChecks/MasterCoherence -------------------------------------
findSignalInList-∈ : ∀ name sigs sig →
  findSignalInList name sigs ≡ just sig →
  sig ∈ sigs × Identifier.name (DBCSignal.name sig) ≡ name

presenceIsAlwaysᵇ-sound : ∀ p → presenceIsAlwaysᵇ p ≡ true → p ≡ Always

muxRefsMasterᵇ-sound : ∀ master p → muxRefsMasterᵇ master p ≡ true →
  ∀ (m : Identifier) (vs : List⁺ ℕ) → p ≡ When m vs →
  Identifier.name m ≡ master

checkMasterCoherence-sound : ∀ msgName sigs →
  checkMasterCoherence msgName sigs ≡ [] → MasterCoherent sigs
checkAllMasterCoherence-sound : ∀ msgs →
  checkAllMasterCoherence msgs ≡ [] →
  All (λ m → MasterCoherent (DBCMessage.signals m)) msgs

-- CONDITIONAL-COMPLETE (needs a uniqueness hypothesis — maintainer decision, §12.2):
checkMasterCoherence-complete : ∀ msgName sigs →
  AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂) sigs →
  MasterCoherent sigs → checkMasterCoherence msgName sigs ≡ []
```
*Approach*: `findSignalInList-∈` mirrors the existing `findSignalInList→SigPresent` (`Protocol/Adequacy/StreamingWarm.agda:131-138`): induct with `with name ≡csᵇ … in eq-name`; the true branch extracts `s ≡ sig` via `Data.Maybe.Properties.just-injective` and the name equation via `Identifier.≡csᵇ-sound` (the reflection kit cited at `CAN/DBCHelpers.agda:74`); false branch recurses with `there`. `muxRefsMasterᵇ-sound` pattern-matches the presence *value* at clause level (per the no-stacked-with and expose-scrutinee lessons): `Always` arm refutes the `Always ≡ When m vs` equation with `()`; `When m' vs'` arm matches `refl` on the equation, then `≡csᵇ-sound`. The main sound proof re-runs the body's `with` cascade (one `with` per scrutinee, `in eq` on `findMuxMaster` and `findSignalInList`); the `true` arm splits the `∧` with a bespoke `∧-split : a ∧ b ≡ true → a ≡ true × b ≡ true` (4-clause) and builds `mc-mux master eq₁ masterSig (proj₁ ∈-pair) (proj₂ ∈-pair) (presenceIsAlwaysᵇ-sound …) (All.map (muxRefsMasterᵇ-sound …) …)`, converting `allRefsMasterᵇ master sigs ≡ true` to a per-element `All` via stdlib **`all⁺`** (`Data.List.Relation.Unary.All.Properties` :670, `all⁺ : ∀ xs → T (all p xs) → All (T ∘ p) xs` — *corrected per panel; `all⁻` at :676 is the reverse direction*), feeding it `subst T (sym eq) tt` to lift the `≡ true` hypothesis into `T`, then per-element back to `≡ true` for `muxRefsMasterᵇ-sound`. The `nothing` branch of `findMuxMaster` yields `mc-no-mux eq`. The complete direction additionally needs `findSignalInList-unique` (first-hit = the named signal, under per-message name uniqueness — `findSignalInList` returns the first `≡csᵇ` hit, `CAN/DBCHelpers.agda:76-81`, so a duplicate-named non-Always signal can shadow `mc-mux`'s exhibited witness) — this is why it carries the `AllPairs` hypothesis; whether to ship it in V1 or defer is an **explicit maintainer decision** (§12.2), not this document's call. **~220-260 LOC total; the long pole of the whole route.**

```agda
-- AdvisoryChecks/Attributes ------------------------------------------
wfAttrTypeᵇ-sound      : ∀ ty  → wfAttrTypeᵇ ty ≡ true → WfAttrType ty
valueMatchesTypeᵇ-sound : ∀ ty v → valueMatchesTypeᵇ ty v ≡ true → ValueMatchesType ty v
defaultEnumOKᵇ-sound   : ∀ ty v → defaultEnumOKᵇ ty v ≡ true → DefaultEnumOK ty v

checkAttrTyping-sound : ∀ defs a →
  checkAttrTyping defs a ≡ [] → WFAttribute defs a
checkAllAttrTyping-sound : ∀ attrs →
  checkAllAttrTyping attrs ≡ [] → All (WFAttribute (collectDefs attrs)) attrs
-- (+ completes, cheap: match the WFAttribute witness, reconcile the lookup
--    with `with … in eq` + just-injective, then the Bool-complete mirrors)
```
*Approach*: `wfAttrTypeᵇ-sound` is a 6-clause match building `WfATInt mn mx` / … / `WfATEnum x xs` (empty-ENUM clause refuted by `false ≡ true`). `valueMatchesTypeᵇ-sound` matches both constructors (5 productive clauses; mismatching pairs refute on the hypothesis) — write the full case table rather than relying on catch-all reduction. `defaultEnumOKᵇ-sound` is `Relation.Nullary.Decidable.toWitness` on the `⌊_⌋` at the `(ATEnum, AVEnum)` clause, `tt` elsewhere. `checkAttrTyping-sound` re-runs the body's `with`s (`lookupDef … in eq-look`, then the `∧` scrutinee), splits with `∧-split`, and assembles `wfDef` / `wfDefault d def eq-look vmt deo` / `wfAssign a def eq-look vmt`. ~180-220 LOC across the module.

### 4.3 `-allW` lemmas (`Aletheia.DBC.Validity.WarningChecks`, [P])

Eight lemmas (`check*-allW` per-element + `checkAll*-allW` lifted, for CHECKs 24-27), each following the existing shapes at `WarningChecks.agda:742-752`: multi-arm `with` mirrors + `refl ∷ []` at issue-emitting arms, `All-concatMap ∘ universal` lifts. ~80 LOC. (These need only the check bodies + `IsWarning`, so they respect the WarningChecks/AdvisoryChecks split of §2.)

### 4.4 Theorem completeness extension (`Aletheia.DBC.Validity.Theorem`, [P])

Four additional `ei-combine` nesting levels at the tail of `completeness` (`Theorem.agda:106-150`), each closed by `errorIssues-allW _ (checkAll*-allW …)`. Precise diff shape as stated in §2's Changed-modules row (revised per panel): the innermost arm at :149 is rewritten to become the first component of the first new `ei-combine`; closing parens at :150 grow by 4; the two import blocks (:15-28, :50-59) gain 4 names each. `soundness` untouched (panel-verified). ~20 LOC.

### 4.5 Assembly (`Aletheia.DBC.TextParser.Properties.AggFromValidator`, [P])

```agda
-- bridges --------------------------------------------------------------
msgIdsUnique-bridge : ∀ msgs →
  AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs →
  AllPairs _≢_ (map DBCMessage.id msgs)
-- stdlib Data.List.Relation.Unary.AllPairs.Properties.map⁺ :
--   AllPairs (R on f) xs → AllPairs R (map f xs)   (verified at stdlib :45)
-- `(_≢_ on DBCMessage.id) m₁ m₂` is definitionally `id m₁ ≢ id m₂`; one line.

sigNamesUnique-bridge : ∀ sigs →
  AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂) sigs →
  AllPairs _≢_ (map DBCSignal.name sigs)
-- AllPairs.map with the contraposition
--   λ ne nameEq → ne (cong (fromList ∘ Identifier.name) nameEq)
-- (signalNameStr = fromList ∘ Identifier.name ∘ DBCSignal.name, Types.agda:298-299),
-- then map⁺.  ~8 LOC.

recvHeadStop : ∀ (cr : CanonicalReceivers) → RecvHeadStop cr
-- RecvHeadStop recv = Σ c, Σ cs, (emit canonicalReceiversFmt recv ≡ c ∷ cs)
--                     × isHSpace c ≡ false  (Format/SignalLine/Roundtrip.agda:106-109).
-- Mirror build-RecvHeadStop (Properties/Topology/Signal.agda:268-280) case-for-case,
-- but derive the head stop from Identifier validity instead of the SuffixStops input:
-- [] receivers → 'V' , _ , refl , refl (Vector__XXX emission reduces);
-- mkIdent [] vp → ⊥-elim vp (T false);
-- mkIdent (c ∷ cs) v → c , _ , refl , isIdentStart→¬isHSpace c (T-∧₁ v)
-- with a private T-∧₁ mirroring WellFormedFromValidity.agda:72-74.  ~15 LOC.

-- arithmetic ------------------------------------------------------------
1≤n⇒n∸1<n : ∀ {n} → 1 ≤ n → n ∸ 1 < n
-- match n = suc m: `suc m ∸ 1 = m < suc m` by n<1+n.  3 LOC.

-- per-signal ------------------------------------------------------------
wellFormedSignalFromChecks : ∀ (fb : ℕ) (sig : DBCSignal) →
  fb ≤ 64 → BitsInFrame fb sig → NonZeroBitLength sig → WellFormedSignal sig
-- Record shape (corrected per panel): WellFormedSignal has a SINGLE field
--   def-wf : WellFormedSignalDef (DBCSignal.signalDef sig)
-- (Formatter/WellFormed.agda:46-48); the bounds live one level down in
-- WellFormedSignalDef (:41-44):
--   startBit-bound  : startBit  < max-physical-bits
--   bitLength-bound : bitLength < suc max-physical-bits
-- Build: record { def-wf = record { startBit-bound = …; bitLength-bound = … } }.
-- startBit-bound  = <-≤-trans (m<m+n s (n≢0⇒n>0 nzl)) (≤-trans bif (*-monoˡ-≤ 8 fb≤64));
--   64 * 8 reduces to 512 ≡ max-physical-bits by refl (Constants.agda:22-23).
-- bitLength-bound = s≤s (≤-trans (m≤n+m l s) (≤-trans bif (*-monoˡ-≤ 8 fb≤64)))
--   — the s≤s wrapper lands exactly in `< suc max-physical-bits`.
-- The `*-monoˡ-≤ 8 n≤64` shape is already used at Formatter/WellFormed.agda:182. ~25 LOC.

physicallyValidFromChecks : ∀ (fb : ℕ) (sig : DBCSignal) →
  BitsInFrame fb sig → NonZeroBitLength sig → BEStartBitOK sig →
  PhysicallyValid fb sig
-- `with DBCSignal.byteOrder sig in boEq`:
-- LE → pv-LE boEq (n≢0⇒n>0 nzl);
-- BE → pv-BE boEq len-pos
--        (<-≤-trans-shape: s+l∸1 < s+l ≤ fb*8 via 1≤n⇒n∸1<n on 1 ≤ s+l)
--        (beok boEq).  ~30 LOC.

signalLineWFFromChecks : ∀ (sig : DBCSignal) →
  WellFormedTextPresence (DBCSignal.presence sig) → SignalLineWF sig
-- record { name-stop = signalNameStop sig ; recv-head-stop = recvHeadStop _ ;
--          presence-wf = wfp }.  signalNameStop from WellFormedFromValidity.  5 LOC.

-- per-message -----------------------------------------------------------
messageWFFromChecks : ∀ (msg : DBCMessage) →
  All (BitsInFrame (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg) →
  All NonZeroBitLength (DBCMessage.signals msg) →
  AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂) (DBCMessage.signals msg) →
  All (λ s → WellFormedTextPresence (DBCSignal.presence s)) (DBCMessage.signals msg) →
  MasterCoherent (DBCMessage.signals msg) →
  All BEStartBitOK (DBCMessage.signals msg) →
  MessageWF msg
-- fields: fb-bound = dlcBytes-bounded (DBCMessage.dlc msg);
-- wf-sigs / pvs via a private zip3-All recursion (avoid stacked All.zipWith);
-- wfps = given; mc = given;
-- name-pre = identNameStop (DBCMessage.name msg)  — IdentHeadNonHSpace
--   (Topology/Message.agda:279-283) is DEFINITIONALLY identNameStop's Σ-codomain
--   (Σ-syntax sugar for the same type), so no bridge lemma is needed;
-- send-pre likewise; item-pres = All.map signalLineWFFromChecks over wfps;
-- sig-names-unique = sigNamesUnique-bridge.  ~60 LOC incl. zip3-All.

messagesWFFromChecks : ∀ msgs → (the six All/AllPairs hypotheses over msgs)
  → All MessageWF msgs
-- single bespoke recursion consuming six Alls point-wise (~15 LOC).

-- DBC level --------------------------------------------------------------
aggFromValidatorClean : ∀ (d : DBC) →
  errorIssues (validateDBCFull d) ≡ [] →
  textRoundTripAdvisories d ≡ [] →
  WellFormedTextDBCAgg d
-- 1. v = soundness d ec  (Validity/Theorem)  → the eight ValidDBC fields.
-- 2. Split the advisory hypothesis into its five slices with
--    Validity.ListLemmas.++-≡[]-split (repeatedly; no errorIssues filter involved).
-- 3. Per-slice sounds → All-per-message facts; messagesWFFromChecks assembles
--    All MessageWF from ValidDBC.bitsInFrame / .nonZeroBitLengths / .uniqueSigNames
--    + the CHECK 25/26/24 sounds.
-- 4. attr-wfs = checkAllAttrTyping-sound; ids = msgIdsUnique-bridge (ValidDBC.uniqueIds v);
--    unres = checkAllUnknownValueDescriptionTargets-sound.
-- 5. Finish with wellFormedFromValidity d msg-wfs attr-wfs ids unres
--    (Properties/WellFormedFromValidity.agda:131-147).  ~60 LOC.
```

### 4.6 Capstone (`…/Properties/Substrate/Unsafe.agda`, the allowlisted module)

```agda
parseText-on-formatText-validated : ∀ (d : DBC) →
  errorIssues (validateDBCFull d) ≡ [] →
  textRoundTripAdvisories d ≡ [] →
  parseText (formatText d) ≡ inj₂ d
parseText-on-formatText-validated d ec ac =
  parseText-on-formatText d (aggFromValidatorClean d ec ac)

-- Wire-shaped corollary (new, per panel — composes §4.7's bridge):
parseText-on-formatText-advisory-wire : ∀ (d : DBC) →
  errorIssues    (validateDBCFull d) ≡ [] →
  advisoryIssues (validateDBCFull d) ≡ [] →
  parseText (formatText d) ≡ inj₂ d
parseText-on-formatText-advisory-wire d ec aw =
  parseText-on-formatText-validated d ec (advisoryWireClean⇒advisoriesEmpty d aw)
```
*Approach*: pure composition, ~6 lines total. Both live here because any consumer of `parseText-on-formatText` cannot be `--safe`, and the Unsafe-module policy co-locates all such consumers in this one allowlisted file.

### 4.7 Wire-code bridge (`Aletheia.DBC.Validity.AdvisoryChecks` facade + per-submodule `-allC` lemmas, [P]) — NEW, closes the panel's major finding

**Gap being closed.** The strict-profile observable (§1 option 2) is code-set membership over `issues[].code` in the *full* `validateDBCFull` output; the theorem hypothesis is `textRoundTripAdvisories d ≡ []`. Rev. 1 connected them only by construction-argument prose. The repo formalizes the exact severity analogue (`errorIssues-allW` / `-allE` / `ei-*`, `Validity/Composition.agda:61-90`), so the code-level mirror is built the same way. `ValidationIssue` carries `code : IssueCode` as a first-class field (`Types.agda:379-384`), so the machinery transplants directly.

```agda
-- facade ---------------------------------------------------------------
advisoryCodeᵇ : IssueCode → Bool          -- true exactly on the 5 profile codes
advisoryCodeᵇ BigEndianStartBitUnderflow    = true
advisoryCodeᵇ MultiValueMuxSelector         = true
advisoryCodeᵇ MuxMasterIncoherent           = true
advisoryCodeᵇ AttributeTypeMismatch         = true
advisoryCodeᵇ UnknownValueDescriptionTarget = true
advisoryCodeᵇ _                             = false

advisoryIssues : List ValidationIssue → List ValidationIssue
advisoryIssues = filterᵇ (advisoryCodeᵇ ∘ ValidationIssue.code)
-- (filterᵇ as in Validator/Formatting.agda:43-48; [P]-only — the kernel never
--  computes this at runtime, so no runtime module changes.)

private C : ValidationIssue → Set
        C i = advisoryCodeᵇ (ValidationIssue.code i) ≡ true

-- filter kit: LINE-FOR-LINE mirrors of Composition.agda:61-90 with the
-- scrutinee `advisoryCodeᵇ (code i)` instead of `severity i`:
advisoryIssues-++      : ∀ xs ys → advisoryIssues (xs ++ₗ ys)
                         ≡ advisoryIssues xs ++ₗ advisoryIssues ys
ai-split               : ∀ xs ys → advisoryIssues (xs ++ₗ ys) ≡ [] →
                         advisoryIssues xs ≡ [] × advisoryIssues ys ≡ []
advisoryIssues-allC    : ∀ xs → All C xs → advisoryIssues xs ≡ xs
advisoryIssues-allC-nil : ∀ xs → All C xs → advisoryIssues xs ≡ [] → xs ≡ []

-- per-check code lemmas (5) — the -allE/-allW analogue at the code level;
-- the emitting arms discharge `advisoryCodeᵇ (code (mkIssue _ <Code> _)) ≡ true`
-- by record-projection reduction (refl), exactly as Composition.agda:96-103
-- describes for the -allE refl witnesses:
checkAllBEStartBitUnderflow-allC : ∀ msgs → All C (checkAllBEStartBitUnderflow msgs)
checkAllMultiValueMux-allC       : ∀ msgs → All C (checkAllMultiValueMux msgs)
checkAllMasterCoherence-allC     : ∀ msgs → All C (checkAllMasterCoherence msgs)
checkAllAttrTyping-allC          : ∀ attrs → All C (checkAllAttrTyping attrs)
checkAllUnknownValueDescriptionTargets-allC :
  ∀ urvds → All C (checkAllUnknownValueDescriptionTargets urvds)

-- the bridge -----------------------------------------------------------
advisoryWireClean⇒advisoriesEmpty : ∀ d →
  advisoryIssues (validateDBCFull d) ≡ [] →
  textRoundTripAdvisories d ≡ []
```
*Approach*: an `ai-split` where-chain down `validateDBCFull`'s right-associated concatenation — 21 peel steps (`proj₂` at each non-advisory arm) reaching the 5 advisory slices, which sit **contiguously at the tail** (CHECK 23 is arm 22 of the existing 22, `Validator.agda:58`; the 4 new arms append after it), then 4 splits isolate each slice. Each slice closes by `advisoryIssues-allC-nil _ (…-allC …) (projᵢ …)` — its issues all carry an advisory code, so an empty advisory filter forces the slice itself empty. Recombine the five `≡ []` facts with `++-≡[]-combine` in `textRoundTripAdvisories`' concatenation order (slice order differs between the two composites — CHECK 23 last vs. first-of-tail — which is irrelevant when every slice is individually `[]`). Mechanical throughout; no check body is unfolded (only the concatenation spine and the filter). **~120-160 LOC total** (kit ~40, `-allC` ×5 ~50, bridge ~35), matching the panel's estimate. Placement: kit + bridge + CHECKs 24/25/23 `-allC` in the facade; CHECK 26/27 `-allC` co-located with their sound lemmas in the submodules.

**Honest residual (documented, not hidden)**: the CLI flag / binding helper tests wire *strings*. `advisoryIssues (validateDBCFull d) ≡ []` ⇔ "none of the 5 strings appear in `issues[].code`" additionally needs that `formatIssueCode` maps exactly the 5 advisory constructors to exactly those 5 strings — a closed 25-case fact about `ResponseFormat.formatIssueCode`. This last mile is **test-pinned** (4 binding parity tests + 5 byte-pinned CLI scenarios), the identical trust treatment every existing wire surface receives (severity strings, `has_errors`, error-code strings — none are proven into the bindings). Optionally it can also be proven kernel-side as a closed-term refl-family lemma (`formatIssueCode-advisory-faithful`); offered as §12.5, default = test-pinning.

---

## 5. Proof order (what unblocks what) + per-step verification

Each step type-checks green before the next begins; **each step boundary must also hold `check-proof-coverage` green** (revised per panel — the pre-push hook runs full `run_ci` against the working tree, and coverage requires every `src/` module to be reachable from `build` or the proofModules walk, `Shakefile.hs:600-611`). New [P] modules therefore enter `proofModules` **in the same commit that creates them**. Type-check commands use the mandatory `+RTS -N32 -M16G -RTS`.

1. **Leaf extraction** — create `MuxTopology.agda` + `AttrLookup.agda` (definitions moved verbatim), add `public` re-exports in `TextFormatter/Topology.agda`, `TextFormatter/Attributes.agda`, `TextParser/Attributes.agda`. (Coverage: the leaves are reached via their re-exporting hosts, which sit in the existing TextFormatter/TextParser walk roots — `Shakefile.hs:420-421` — and, once step 3 lands, via Main's runtime closure through `Checks.agda`.)
   Verify: `cd src && agda +RTS -N32 -M16G -RTS Aletheia/DBC/TextFormatter/Attributes.agda` and `…/TextParser/Attributes.agda`; then `cabal run shake -- gen-ffi-modules && cabal run shake -- build` (two new runtime modules enter the MAlonzo list); `cabal run shake -- check-properties` (all downstream proofs must still see the same definitions); `cabal run shake -- check-proof-coverage`; `cabal run shake -- iwyu`.
2. **Wire enum** — Types.agda +4 codes; ResponseFormat +4 clauses.
   Verify: `cabal run shake -- build && cabal run shake -- check-ffi-exports && cabal run shake -- check-fidelity` (constructor additions can shift MAlonzo manglings; the build prints exact `sed` fixes if the FFI names move).
3. **Check bodies + composites** — Checks.agda (4 checks + helpers), Validator.agda (`validateDBCFull` tail + `textRoundTripAdvisories`), WarningChecks +8 `-allW`, Theorem completeness +4 levels.
   Verify: `cabal run shake -- build`, `cabal run shake -- check-properties` (Theorem must re-close), `agda +RTS -N32 -M16G -RTS src/Aletheia/Main.agda` (Handlers-closure heap tripwire — the leaves must not have dragged formatter weight in), `cabal run shake -- check-no-properties-in-runtime`, `cabal run shake -- check-proof-coverage`. Then `bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput` (runtime code changed; expect streaming-neutral, DBC-ingest within noise — record the comparison per AGENTS.md).
4. **Advisory soundness + wire bridge** — `AdvisoryChecks.agda` + `MasterCoherence.agda` + `Attributes.agda`, including the §4.7 filter kit, `-allC` lemmas, and `advisoryWireClean⇒advisoriesEmpty`. **Same commit adds `Validity/AdvisoryChecks.agda` to `proofModules`** (the facade's re-exports pull the two submodules into the walk). Without the root, step-4's `check-properties` would be a false green — the new modules would be walked by nothing (`Shakefile.hs:600-611`; this is the strategy's own cited aggregator-walk lesson).
   Verify: direct `agda +RTS -N32 -M16G -RTS` on each of the three new modules, then `cabal run shake -- check-properties && cabal run shake -- check-proof-coverage`. (These are the modules where the with-discipline lessons bind: one `with` per scrutinee, `in eq` for external equations, `subst T` transport for `≡csᵇ` truths, never `rewrite` over goals mentioning check bodies.)
5. **Assembly** — de-private `dlcBytes-bounded`; `AggFromValidator.agda` through `aggFromValidatorClean`. **Same commit adds it to `proofModules`.**
   Verify: `agda +RTS -N32 -M16G -RTS src/Aletheia/DBC/TextParser/Properties/AggFromValidator.agda` (watch heap — this module joins the Validator closure with the Message-topology closure), then `cabal run shake -- check-properties && cabal run shake -- check-proof-coverage`.
6. **Capstone** — the two Unsafe corollaries (§4.6).
   Verify: `cabal run shake -- check-properties && cabal run shake -- check-invariants` (postulate/Unsafe allowlist unchanged) and `cabal run shake -- check-proof-coverage`. The roots added in steps 4-5 become redundant with the `Substrate/Unsafe` root (:470) here and STAY — harmless and precedented (`TextParser/Properties` :411 coexists with :470).
7. **Bindings + docs + tests** (see §6).
   Verify: full `tools/run_ci.py` sweep (warm ~110s), including the CLI parity harness and matrix gates.

Steps 1-2 are independent and can land in either order; 3 needs both; 4 needs 3; 5 needs 4; 6 needs 5; 7 needs 2-3 (binding mirrors) and is otherwise parallel to 4-6. With the per-step roots in place, **every step boundary is a pushable state** — no multi-step landing is forced by the gates.

---

## 6. Integration obligations (established patterns)

| Surface | Obligation |
|---|---|
| Kernel wire | 4 new `issues[].code` values, warning severity, appended at the END of the issues array (existing issue ORDER for all existing checks is untouched — the byte-pinning CLI harness only sees new lines on fixtures that actually trip the new advisories). `ParsedDBCResponse.warnings` (via `warningIssues` in `loadValidatedEpilogue`) may now include the advisories on load — additive. |
| Typed-error lift (#152) | **Not applicable** — the new codes are warnings, never load-refusals, so no `ValidationFailed` lift changes in any binding. This is a deliberate consequence of the advisory design. |
| Binding mirrors | `python/aletheia/codes/_issue.py` (+4 enum members), `go/aletheia/result.go` (+4 `IssueCode` consts), `cpp/src/json_parse.cpp` (+4 mappings, `json_parse.cpp:347` region), `rust/src/response.rs` (+4 variants in the enum and in both match directions, `from_wire` :207-219 + the emit direction). **Rust/C++ enum growth is the §12.1 maintainer decision** — the mirrors land the same either way; only `#[non_exhaustive]`/policy/CHANGELOG-label differ. Parity tests per binding extended with the 4 strings. |
| FEATURE_MATRIX | New row `text_roundtrip_advisories` (matrix-row-or-invisible): entry = the IssueCode surface per binding; description names the 5-code advisory profile and the theorem it feeds. |
| PROTOCOL.md | **(corrected per panel)** The per-issue-code documentation surface is the counted inline lists at `PROTOCOL.md:315-317` — "**Issue Codes** (21 total): **Error** (8): … / **Warning** (13): …" — NOT the § Error Code Reference (:1240-1244), which catalogs `Error.agda` ENVELOPE codes only ("drawn from the Agda source of truth src/Aletheia/Error.agda"). The edit: append the 4 codes to the Warning list and update the counts 13→17 and 21→25, each cited as measured from the `IssueCode` enum (`Types.agda:355-376` + the 4 additions) per the numbers-in-prose rule. PLUS a new subsection "Text round-trip advisory profile": the 5-code set (`big_endian_start_bit_underflow`, `multi_value_mux_selector`, `mux_master_incoherent`, `attribute_type_mismatch`, `unknown_value_description_target`), the guarantee statement (validator-error-clean + advisory-clean ⇒ `parse_dbc_text(format_dbc_text(d)) == d`, backed by the named theorem chain `parseText-on-formatText-advisory-wire` — hypothesis = no advisory code in `issues[]`, per §4.7's bridge; the string↔code last mile test-pinned), and the honest caveat (advisory-fired means *unproven*, not *defective* — the envelope is sufficient, not necessary). |
| CLI harness | `docs/CLI_SCENARIOS.yaml` + `test_cli_parity.py`: one new validate-scenario per advisory code (5 fixtures, each tripping exactly one), byte-pinned across the 3 CLIs. Audit existing broken-DBC fixtures for incidental advisory hits first (see risks). |
| Docs | `Handlers/FormatDBCText.agda` docstring: replace the "MessageWF / WFAttribute are NOT discharged" caveat (:100-113) with the new conditional guarantee. `DEFERRED_ITEMS.md` E.2: restate as CLOSED-conditional (needs user sign-off — §12.4). `docs/architecture/DESIGN.md` if it states the old E.2 residue. |
| CHANGELOG | `### Added` — 4 warning codes + the conditional round-trip theorem; "kernel acceptance unchanged; wire-additive" (verified: all three CLIs key exit on `has_errors` only — `python/aletheia/cli.py:410`, `go/cmd/aletheia/main.go:277-289`, `cpp/src/cli/cli.cpp:282` — and `loadValidatedEpilogue` refuses only on `hasAnyError`, `LoadDBC.agda:125-130`; panel-confirmed). **The BREAKING label is decision-gated (§12.1)**: if the Rust enum grows without `#[non_exhaustive]` and without a ratified growth policy, the entry carries BREAKING(Rust); do NOT write an unqualified "Not BREAKING". One header per category. |
| Mutation | Binding-side enum additions are covered by parity tests; Python `[tool.mutmut]` needs no new `--ignore` (no new tools-importing tests). |
| Module count | +6 modules; sync prose counts in the same commit per the count-drift rule (`cabal run shake -- count-modules`). |

**Strict profile (deferred follow-up, wire design pinned here)**: CLI flag `--strict-roundtrip` on `validate` (×3 CLIs) + binding helper (e.g. Python `ValidationResult.roundtrip_clean`), implemented purely as membership of the PROTOCOL-documented code-set in `issues[].code` — now formally backed on the kernel side by §4.7. No kernel change. If a kernel profile is later mandated, the flag rides `validateDBC` as an optional `"profile"` string in `Routing.tryValidateDBC` — but the severity-parametric check refactor it forces (doubled `-allW`/Theorem surface) is the recorded argument against. A kernel-computed `roundtrip_clean` response field is the recorded middle option (§12.5).

---

## 7. Perf & heap discipline

- **Cold path only.** All four checks run per-DBC-ingest inside `validateDBCFull` (called from the three DBC handlers, never per frame) — exactly the cat-26 acceptance already documented in the `Checks.agda` header (:13-21). `Dec`/`⌊_⌋` allocation is acceptable there; the frame hot path (`SignalExtraction`, `Protocol.FrameProcessor`) is untouched by every step. `advisoryIssues` is [P]-only — never computed at runtime.
- **Handlers heap wall.** `Handlers/LoadDBC.agda:22-27` documents that the Handlers closure must stay free of the TextParser/TextFormatter trees (16 GiB elaborator blowup pre-split). The leaf extraction (§2) is what keeps `findMuxMaster`/`lookupDef` reachable from `Checks.agda` without breaching that wall. Step 3's `Main.agda` type-check is the tripwire; if elaboration time/heap jumps, the leaves picked up a heavy import — fix the leaf, don't bump `-M`.
- **Issue-array ordering.** Append-only at the tail of `validateDBCFull`. This (a) leaves `soundness`'s `ei-split` chain untouched, (b) leaves every existing pinned CLI byte output stable on fixtures that don't trip advisories, (c) costs only 4 mechanical `ei-combine` levels in `completeness` (plus the :149 rewrite, §4.4), and (d) puts all 5 advisory slices contiguously at the tail — which is what keeps §4.7's bridge a linear peel instead of an interleaved split.
- **Benchmarks**: step 3 is a runtime change ⇒ mandatory `run_all.sh` comparison against the latest baseline before commit (AGENTS.md universal rule). Expected: Stream LTL/Signal Extraction/Frame Building unchanged; DBC-load may move 1-3% (two extra message walks + one attribute walk, cold).

---

## 8. What route (c) must NOT do (hard constraints)

1. **No new error-class checks; no severity flips** of existing codes. The load-accepted set across 4 bindings + 3 CLIs is invariant under this plan — that is the acceptance-preservation property tests must pin.
2. **Never refuse model-legal constructs**: multi-value selectors, nested/chained mux, and multi-group mux are honored by `SignalExtraction` and representable on the JSON wire; they may be *advised about*, never rejected at load or validate.
3. **No Set-level predicates in runtime modules**: `WFAttribute`, `ValueMatchesType`, `MasterCoherent`, `WellFormedTextPresence` stay in the Properties/Formatter proof surface; runtime sees only Bool/Dec bodies. (The grep gate covers 4 entry files, `Shakefile.hs:584-588`, but the MAlonzo-bloat rationale binds everywhere.)
4. **No TextParser/TextFormatter imports into the Handlers closure** — leaf extraction is the only sanctioned mechanism.
5. **No `rewrite` over goals mentioning parser/formatter applications** (`feedback_no_rewrite_over_parser_goal`); the sound proofs use helper + `cong`/`trans` and clause-level matching throughout.
6. **No reordering of existing wire issue output** — append-only.
7. **No silent reframing beyond this document**: restating E.2 as the conditional theorem is this strategy's explicit proposal and needs the maintainer's ratification before DEFERRED_ITEMS is rewritten (§12.4).
8. **No unilateral deferral or unqualified compatibility claims**: the CHECK 26 completeness direction and the Rust enum-growth stance are maintainer decisions (§12.1-12.2), surfaced with complete option sets — not silently pre-decided in either direction.

---

## 9. Risk register

| Risk | Likelihood | Mitigation / fallback |
|---|---|---|
| `emit canonicalReceiversFmt` fails to reduce in `recvHeadStop`'s cons cases (Format-DSL stuckness) | Low (build-RecvHeadStop's `refl`s show it reduces) | Fall back to reusing `build-RecvHeadStop` by constructing its `SuffixStops` input from Identifier validity, or state `recvHeadStop` in the module that hosts `build-RecvHeadStop` where the reduction environment is proven friendly. |
| CHECK 26 sound proof with-cascade fights abstraction (the classic breaker) | Medium | Discipline: helpers on `SignalPresence` values (the `MuxUnitScaling` precedent), `in eq` on both `find*` scrutinees, `∧-split` instead of stacked `with`. Budget 2× the 250-LOC estimate before invoking the step-back rule and surfacing alternatives. |
| §4.7 bridge where-chain (21 peels + 4 splits) is verbose or heavy to elaborate | Low (each step is one `ai-split` application over an opaque slice; no check body unfolds) | If elaboration drags, group the 21 non-advisory head arms as a single `let prefix = …` and split once against the 5-slice tail (`ai-split prefix tail`), reducing to 1 peel + 4 splits. |
| `Substrate.Unsafe` heap grows past 16G with the Validator+AggFromValidator closure | Low-medium | The Theorem/Validator closure is light next to the aggregator closure already in Unsafe. If tripped: do NOT bump `-M` silently; surface options (corollary-less state with documented manual composition vs. a user-approved cap bump for this one module). |
| MAlonzo name-mangling shifts from the IssueCode additions | Low | `check-ffi-exports` + build's printed `sed` commands (established recovery); step 2 is isolated to make the diff obvious. |
| Existing CLI fixtures incidentally trip new advisories (pinned outputs change) | Medium | Step-7 pre-audit: run the 3 CLIs' `validate` over every fixture before repinning; any hit is either a genuine fixture defect (fix the fixture) or an intended advisory (repin with a comment). |
| Existing binding tests assert exact warning lists on loads | Low-medium | Grep binding tests for warning-list equality assertions during step 7; extend expected sets. |
| Downstream Rust consumers with exhaustive `match` on `IssueCode` break at compile time | Certain *if* variants are added without `#[non_exhaustive]` and the consumer matches exhaustively | Decision-gated (§12.1); whichever option is chosen, the CHANGELOG entry states it explicitly. |
| The two `lookupDef` clones diverge someday post-unification concerns | N/A after fix | Unification in `AttrLookup` makes divergence impossible — this is a small SSOT win, not a risk. |
| `dlcBytes-bounded` de-privatization collides with a same-name symbol | Low | It's module-qualified; grep first (`rg "dlcBytes-bounded"`) — only the in-file uses exist today. |
| Advisory semantics misread as "file is broken" by users | Medium (comms risk) | Detail strings and PROTOCOL section consistently say "outside the verified round-trip envelope"; CHECK 24's text explicitly avoids claiming wire invalidity. |

(The rev.-1 risk "intermediate pushes fail `check-proof-coverage`" is retired by design — §2/§5 add roots in the creating commits.)

---

## 10. Acceptance criteria ("done" means all of these)

**Theorems that must exist and check under `cabal run shake -- check-properties`:**
- `Aletheia.DBC.TextParser.Properties.AggFromValidator.aggFromValidatorClean : ∀ d → errorIssues (validateDBCFull d) ≡ [] → textRoundTripAdvisories d ≡ [] → WellFormedTextDBCAgg d`
- `Aletheia.DBC.Validity.AdvisoryChecks.advisoryWireClean⇒advisoriesEmpty : ∀ d → advisoryIssues (validateDBCFull d) ≡ [] → textRoundTripAdvisories d ≡ []` (§4.7 — the wire bridge)
- `Aletheia.DBC.TextParser.Properties.Substrate.Unsafe.parseText-on-formatText-validated : ∀ d → errorIssues (validateDBCFull d) ≡ [] → textRoundTripAdvisories d ≡ [] → parseText (formatText d) ≡ inj₂ d`
- `Aletheia.DBC.TextParser.Properties.Substrate.Unsafe.parseText-on-formatText-advisory-wire : ∀ d → errorIssues (validateDBCFull d) ≡ [] → advisoryIssues (validateDBCFull d) ≡ [] → parseText (formatText d) ≡ inj₂ d`
- `Aletheia.DBC.Validity.Theorem.soundness` / `completeness` still close over the extended `validateDBCFull` (soundness textually unchanged).
- The per-check sound/complete/`-allW`/`-allC` lemmas of §4.2-4.4 and §4.7. **Exception handling**: `checkMasterCoherence-complete` ships or is deferred per the §12.2 maintainer decision, recorded in DEFERRED_ITEMS if deferred — not silently dropped.

**Gates**: `build`, `check-properties`, `check-invariants`, `check-no-properties-in-runtime`, `check-erasure`, `check-fidelity`, `check-ffi-exports`, `check-proof-coverage` (green at EVERY step boundary, not only at the end — §5), `iwyu`, full `tools/run_ci.py` — all green at head SHA (gate-claim integrity).

**User-visible behavior**:
- Every DBC that loaded before still loads; every `validate` that exited 0 still exits 0 (acceptance invariance — pinned by the untouched existing CLI scenarios; kernel/CLI exit semantics verified: `has_errors`-keyed only).
- `validate` / load-warnings now include the new advisory codes on files exhibiting the five conditions; 5 new CLI scenarios pin them byte-exactly ×3 CLIs.
- 4 binding IssueCode mirrors resolve the new codes; parity tests + matrix gate green; the Rust/C++ enum-growth stance implemented per the §12.1 decision.
- PROTOCOL.md documents the advisory profile (counted lists at :315-317 updated with measured counts) and the conditional guarantee naming the theorem chain; FormatDBCText docstring + DEFERRED_ITEMS E.2 updated (post-ratification, §12.4).

**Benchmarks**: streaming hot-path deltas within the WSL2 noise bands; recorded comparison in the step-3 commit.

---

## 11. Advisory → blocked-Agg-field map (the (b) V1 diagnostics contract)

This table is the deliverable route (b) consumes; the check functions and sound lemmas here are designed once and shared verbatim.

| Wire code | Check | Agg field it gates | Sound lemma |
|---|---|---|---|
| `big_endian_start_bit_underflow` | CHECK 24 | `msg-wfs → pvs` (`pv-BE.msb-ge-len`) | `checkAllBEStartBitUnderflow-sound` |
| `multi_value_mux_selector` | CHECK 25 | `msg-wfs → wfps` + `item-pres.presence-wf` | `checkAllMultiValueMux-sound` |
| `mux_master_incoherent` | CHECK 26 | `msg-wfs → mc` | `checkAllMasterCoherence-sound` |
| `attribute_type_mismatch` | CHECK 27 | `attr-wfs` | `checkAllAttrTyping-sound` |
| `unknown_value_description_target` (existing) | CHECK 23 | `unresolved-empty` | `checkAllUnknownValueDescriptionTargets-sound` (new lemma, existing check) |
| `duplicate_message_id` (existing, error) | CHECK 1 | `msg-ids-unique` | via `soundness` + `msgIdsUnique-bridge` |
| `duplicate_signal_name` (existing, error) | CHECK 2 | `msg-wfs → sig-names-unique` | via `soundness` + `sigNamesUnique-bridge` |
| `signal_exceeds_dlc` + `bit_length_zero` (existing, error) | CHECK 8+10 | `msg-wfs → wf-sigs`, `pvs` backbone | via `soundness` + `wellFormedSignalFromChecks` / `physicallyValidFromChecks` |
| — (unconditional) | — | `node/vt/ev/cm-stops`, `sg-wfs`, `name-pre`, `send-pre`, `item-pres.{name,recv}-stop`, `fb-bound` | `identNameStop` family + `recvHeadStop` + `dlcBytes-bounded` |
| *(whole profile)* | — | *(wire observable → theorem hypothesis)* | `advisoryWireClean⇒advisoriesEmpty` (§4.7) |

---

## 12. Open questions — maintainer decisions (complete set, none pre-decided)

1. **Rust `IssueCode` enum growth (blocks final CHANGELOG wording).** `pub enum IssueCode` is not `#[non_exhaustive]` (`rust/src/response.rs:155-201`); adding 4 variants is source-breaking for downstream exhaustive matches (cargo-semver-checks: `enum_variant_added` = major), even though the `Unknown(String)` fallback (:200) and the enum's own docstring (:151-154, "the code set may grow") give wire-level forward-compatibility. Options: **(a)** add `#[non_exhaustive]` now — itself a one-time source break for exhaustive matchers, but makes all future code-set growth additive, and matches the docstring's declared intent; **(b)** ratify an enum-growth policy (RUST_API.md + CHANGELOG conventions): additive `IssueCode` variants are expected surface growth, each labeled BREAKING(Rust) (or explicitly exempted) when shipped; **(c)** no structural change — label this change BREAKING(Rust). Annotation (not pruning): C++'s `enum class IssueCode` (`validation_issue.hpp:16`) has a weaker analogue (downstream `-Wswitch`/`-Werror`), and the same decision should state whether it is covered; Go (`type IssueCode string`, `result.go:175`) and Python (str-enum) are additive-safe.
2. **`checkMasterCoherence-complete`: ship in V1 or defer.** Every existing warning check ships both directions (WarningChecks convention); the complete direction here needs the per-message name-uniqueness hypothesis (`findSignalInList` is first-hit, `CAN/DBCHelpers.agda:76-81`) and ~60-80 extra LOC (`findSignalInList-unique`). Deferral breaks the both-directions convention; shipping costs schedule on the route's long pole. Explicitly the maintainer's call; if deferred, recorded in DEFERRED_ITEMS with the hypothesis-shaped signature already pinned (§4.2).
3. **`AttributeTypeMismatch`: one code with detail variants (proposed) vs. two codes** (unknown-def vs. ill-typed) mirroring #150's `AttrRefineCause` split. One code matches `UnknownCommentTarget` style; two codes give machine-distinguishable triage. Wire codes freeze once shipped — decide before step 2.
4. **E.2 restatement ratification.** Rewriting DEFERRED_ITEMS E.2 as CLOSED-conditional (the two-hypothesis theorem) is this document's explicit proposal and needs sign-off before the docs flip (§8.7).
5. **Strict-profile last mile.** Default = option 2 (binding-side code-set membership, test-pinned string mapping). Optional hardenings, either/both: **(i)** `formatIssueCode-advisory-faithful` — a closed-term [P] lemma pinning that exactly the 5 advisory constructors map to the 5 profile strings (25-case refl-family; closed literals, so String primitives reduce); **(ii)** a kernel-computed `roundtrip_clean` boolean on `validateDBC` responses (mirrors `has_errors`; Bool-only cold-path computation, but a wire-shape addition). Neither blocks V1.
6. **`AdvisoryChecks` module-family ratification.** The WarningChecks-convention deviation is argued necessary in §2 (Theorem-root closure weight); the panel should ratify the family rather than read it as drift.

---

## 13. Evidence-quality note (added per panel)

Claims in this document about **other tools** (cantools/canmatrix behavior, OEM-file prevalence of extended mux) are *believed, unverified* — the repo contains no grounding for them, and §1's verdicts are constructed so that none depends on them. All other factual claims cite file:line re-verified against the working tree on 2026-07-12, including every line the adversarial panel checked (`Composition.agda:61-90`, stdlib `All/Properties.agda:670/676`, `Theorem.agda:149-150`, `Shakefile.hs:600-611`, `rust/src/response.rs:155-201`, `PROTOCOL.md:315-317`/`1240-1244`, `Formatter/WellFormed.agda:41-48`).
