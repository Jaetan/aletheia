> **Provenance** — rev. 2 (post-adversarial-panel) proof strategy for E.2 route (b),
> produced 2026-07-12 by the multi-agent deep-dive indexed in
> [E2_PROOF_STRATEGY.md](E2_PROOF_STRATEGY.md) (method, panel record, scheduling).
> Route ranking and the E.2 schedule live in [DEFERRED_ITEMS.md](DEFERRED_ITEMS.md) § E.2.
> File:line references are pinned to the 2026-07-12 tree (post-#176 `e9d609f9` plus the
> E.2 accuracy batch); re-verify them against the current tree before executing.

# E.2 Route (b) — Proof Strategy: Runtime Decision Procedure at the Format Handler (rev. 2, post-panel)

**Goal.** `format_dbc_text` round-trips, or tells you exactly why it won't: a runtime checker evaluated in `Protocol/Handlers/FormatDBCText.agda`, surfaced as a #150-style issues envelope. Default = format-anyway + issues on the success response (wire-additive; binding signatures change **in place — BREAKING**, ratified 2026-07-12 §7.4). Opt-in `strict` = typed refusal. All file paths relative to the repository root.

**Recommendation: HYBRID — V2 is the verdict authority, V1 is the diagnostics layer, and the theorem stitches them.**

- **V2 (exact check)** answers *"does it round-trip?"* with zero over-refusal: evaluate `parseText (formatText d′)` and deep-compare. Its YES is ground truth by construction and **axiom-free** (§6.3). Strict mode gates on V2 only, which **dissolves the over-refusal caveat entirely** (the standing caveat that `WellFormedTextDBCAgg` is sufficient-not-necessary stops mattering for refusal decisions).
- **V1 (per-field checker + soundness)** answers *"why?"* with per-field issue codes, and — via `wfTextIssues-sound` → `wellFormedFromValidity` → `parseText-on-formatText` — proves the coherence theorem: **`wfTextIssues d ≡ [] → roundTripsᵇ d ≡ true`**. Contrapositive: every V2 divergence ships **at least one V1 diagnostic**. Two qualifiers, stated up front because they bound what is being sold: **(i)** the stitching theorem consumes the two String↔List Char bridging axioms (it lives in `Substrate/Unsafe.agda`, §6.4) — it is a model-level guarantee with the same trust base as the headline round-trip theorem, unlike `roundTripsᵇ-sound`, which is genuinely axiom-free; **(ii)** it guarantees the diagnostic *set* is non-empty on divergence, **not** that any shipped diagnostic names the actual loss mechanism (V1 is sufficient-not-necessary, so the non-empty set can consist of envelope warnings orthogonal to the real cause). Refusal/docs wording is "at least one diagnostic", never "the explanation". On the wire, acceptance (e) additionally holds unconditionally because the handler prepends the `text_roundtrip_divergence` issue itself on every V2-false path (§8).
- **Fallback if V2's one hard blocker (the DLC `@0` equality, §6.2 — now assessed LOW risk, in-tree precedent found) cannot be closed acceptably:** ship V1-only. This is a real scope change with its own wire/acceptance delta, specified in §7.6 — not a free swap.

Ship as three PRs (slices, per the repo's naming convention): **Slice 1** = IssueCode/formatIssueCode kernel additions + V1 checker + soundness tree; **Slice 2** = V2 equality suite + exact verdict; **Slice 3** = wire/envelope/handler/bindings/docs. (The IssueCode additions were originally scheduled in Slice 3; they MUST land in Slice 1 because the checker's `mkIssue` calls reference the new constructors and `formatIssueCode` is a total function in Main's runtime closure — §9 S1.0.)

---

## 1. The MUST-answer question: runtime import closure

**Does evaluating the checker pull any Properties-tree module into the runtime import closure? NO — and no predicate extraction is needed at all.** This is the central architectural simplification over the landscape inventory's §6 extraction list:

- The **runtime checker** (`Aletheia.DBC.TextParser.WellFormedCheck`, new) computes issue lists / Bools over **runtime-only imports**: `Aletheia.DBC.Types`, `Aletheia.DBC.Identifier` (`_≟ᴵ_`, `_≡csᵇ_` suite, Identifier.agda:209-275), `Aletheia.CAN.DLC` (`dlcBytes`), `Aletheia.CAN.Constants` (`max-physical-bits = 512`, Constants.agda:22-23), `Aletheia.CAN.Endianness` (`ByteOrder`), `Aletheia.CAN.DBCHelpers` (`_≟-CANId_`), `Aletheia.DBC.TextFormatter.Topology` (`findMuxMaster` — in `.so`), `Aletheia.DBC.TextFormatter.Attributes` (`collectDefs` :84, `nthLabel` :101), `Aletheia.DBC.TextParser.Attributes` (`lookupDef` :576, `findLabel` :519), `Aletheia.DBC.DecRat.Refinement` (`natDecRatToℕ`), `Aletheia.DBC.Validity.Combinators` (`requireDec` + `requireDec-sound/-complete`, Combinators.agda:36-48 — already runtime via Validator/Checks.agda) **and `Aletheia.DBC.Validity.ListLemmas` directly** (`concatMap-≡[]-sound/-complete`, `++-≡[]-split/-combine` — these are DEFINED in ListLemmas and imported by Combinators *without* `public` at Combinators.agda:21-23, so they cannot be re-exported from Combinators; the original draft mis-attributed them), plus stdlib (`Data.List.Relation.Unary.AllPairs.allPairs?` :69, `Data.Nat` `_<?_`/`_≤?_`, `Relation.Nullary.Decidable` `⌊_⌋`/`¬?`). It never *states* a Properties-tree `Set` — it decides runtime-statable propositions (arithmetic `Dec`s, stdlib `AllPairs _≢_` on runtime types, constructor-shape Bools).
- The **soundness/completeness lemmas** live in the Properties tree and import both the checker and the Properties-tree predicates (`MessageWF` at Properties/Topology/Message.agda:559-578, `WFAttribute` at Properties/Aggregator/Foundations.agda:148-160, `MasterCoherent`/`WellFormedTextPresence` at Formatter/WellFormedText.agda:88-90/:127-154, `PhysicallyValid`/`WellFormedSignal` at Formatter/WellFormed.agda:41-81, `SignalLineWF` at Properties/Topology/SignalList.agda:204-208). Proof modules importing runtime modules is always legal; the reverse never happens here. **Zero moves of `MessageWF`, `WFAttribute`, `MasterCoherent`, `WellFormedTextPresence`, `SignalLineWF`, `RecvHeadStop`, `IdentHeadNonHSpace`, or the Agg record.** The "RE-EXPORT migrated to Format.*" pattern is NOT invoked.
- The **V2 equality suite** extends `Aletheia.DBC.Properties.Equality` — which is Properties-*named* but **already in the runtime `.so`** (`MAlonzo.Code.Aletheia.DBC.Properties.Equality` is listed in haskell-shim/aletheia.cabal; precedent: runtime `Validator/Checks.agda:47` imports `Aletheia.DBC.Properties`; `DBC/Properties.agda:15` re-exports Equality publicly). The new submodule `Aletheia.DBC.Properties.Equality.Full` adds Dec code (no lemma tree) to an already-runtime surface — no new Properties-tree *lemma* module enters MAlonzo. If the panel prefers a non-Properties name for a runtime-imported module, the identical content lands as `Aletheia.DBC.Equality` instead (pure naming choice; flagged in §13).
- The gate itself: `check-no-properties-in-runtime` (Shakefile.hs:581-598) greps exactly 4 files (`Main.agda`, `Main/JSON.agda`, `Main/Binary.agda`, `Protocol/Handlers.agda`) — none of which gains any new import here. The handler split module `Handlers/FormatDBCText.agda` gains imports of the two new **non-Properties-named runtime modules** only. The gate's letter AND spirit are both satisfied.

**When these modules actually enter the `.so`:** `gen-ffi-modules` derives the cabal module list from the *generated MAlonzo tree* — it `need`s `build/MAlonzo/Code/Aletheia/Main.hs` and then globs `build/MAlonzo//**/*.hs` (Shakefile.hs:1484-1495). A module with no importer in Main's runtime closure produces no `.hs` and cannot be listed. So `WellFormedCheck`, `RoundTripCheck`, and `Equality.Full` generate **no MAlonzo code and do not enter the `.so` until Slice 3**, when `Handlers/FormatDBCText.agda` gains the imports; the one required `gen-ffi-modules` run is at S3.1 (§9). In Slices 1–2 they are covered by direct `agda` type-checks plus the proof-gate walk (each `Sound` module is a `proofModules` root importing its checker).

---

## 2. Module layout

All NEW `.agda` files carry the repo's SPDX dash-comment header (`-- SPDX-FileCopyrightText:` / `-- SPDX-License-Identifier:`) — the SPDX gate maps `.agda` to dash-comments (tools/check_spdx_headers.py:67).

| Module (exact path) | New/changed | OPTIONS pragma | Side | Slice | Contents |
|---|---|---|---|---|---|
| `src/Aletheia/DBC/Types.agda` | changed | unchanged | runtime | **1** | `IssueCode` +8 constructors, appended AFTER the existing 21 (:355-376) — required by the checker's `mkIssue` calls; wire-inert until Slice 3 (no handler emits them before then) |
| `src/Aletheia/Protocol/ResponseFormat.agda` (formatIssueCode only) | changed | unchanged | runtime | **1** | `formatIssueCode` +8 arms (:99-120) — total function in Main's closure; MUST land with the IssueCode ctors |
| `src/Aletheia/DBC/TextParser/WellFormedCheck.agda` | NEW | `--safe --without-K` | runtime (MAlonzo/.so from Slice 3, per §1) | 1 | V1 issue-list checker `wfTextIssues` + Bool leaves (§4) |
| `src/Aletheia/DBC/TextParser/Properties/WellFormedCheck/Sound.agda` | NEW | `--safe --without-K` | proof tree — add to `proofModules` (Shakefile.hs:384) | 1 | facade: top soundness/completeness + Agg assembly (§5.4) |
| `src/Aletheia/DBC/TextParser/Properties/WellFormedCheck/Sound/Signal.agda` | NEW | `--safe --without-K` | proof tree (reached via facade) | 1 | bounds/PV/presence lemmas (§5.1) |
| `src/Aletheia/DBC/TextParser/Properties/WellFormedCheck/Sound/Master.agda` | NEW | `--safe --without-K` | proof tree | 1 | `mcGo-sound/-complete` (§5.2 — the hard lemma) |
| `src/Aletheia/DBC/TextParser/Properties/WellFormedCheck/Sound/Attr.agda` | NEW | `--safe --without-K` | proof tree | 1 | `WFAttribute` reconstruction (§5.3) |
| `src/Aletheia/DBC/TextParser/Properties/Topology/Signal.agda` | changed | unchanged | proof tree | 1 | + universal `recvHeadStop` — placed OUTSIDE the `private` block that opens at :247 (`build-RecvHeadStop` at :268-279 is private and stays so) (§5.1) |
| `src/Aletheia/DBC/JSONParser/MessageWF.agda` | changed | unchanged | proof-adjacent | 1 | de-privatize `dlcBytes-bounded` (move out of the `private` block at :41; :50-67) |
| `src/Aletheia/DBC/TextParser/Properties/WellFormedFromValidity.agda` | changed | unchanged | proof tree (already a root) | 1 | + the two validator bridges (§5.5) + comment refresh |
| `src/Aletheia/CAN/DLC.agda` | changed | unchanged | runtime | 2 | + `dlc-code-inj` + `_≟-DLC_` (§6.2), **appended at END of file** — Marshal.hs:22 and ConstructorTest.hs:48 import `MAlonzo.Code.Aletheia.CAN.DLC` (`T_DLC_18`/`C_mkDLC_28`); appending keeps existing mangled numbering stable |
| `src/Aletheia/DBC/Properties/Equality/Full.agda` | NEW | `--safe --without-K` | runtime-reachable (Properties-named; cabal precedent §1) | 2 | 20 mechanical Dec-equality operators up to `_≟-DBC_` (§6.1) |
| `src/Aletheia/DBC/Properties/Equality.agda` | changed | unchanged | runtime-reachable | 2 | de-privatize `_≟-vd_` (:72-77, inside the `private` block at :72) so `Full` can reuse it |
| `src/Aletheia/DBC/TextParser/RoundTripCheck.agda` | NEW | `--safe --without-K` | runtime (MAlonzo/.so from Slice 3) | 2 | V2 `roundTripsᵇ` / `roundTripsWithᵇ` (§6.3). Imports `TextParser` + `TextFormatter` + `Equality.Full` — deliberately a leaf so its interface caches (heap note §9) |
| `src/Aletheia/DBC/TextParser/Properties/RoundTripCheck/Sound.agda` | NEW | `--safe --without-K` | proof tree — add to `proofModules` | 2 | `roundTripsᵇ-sound` (§6.3; axiom-FREE) |
| `src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda` | changed | `--without-K` only (allowlisted) | the ONE Unsafe module (root at Shakefile.hs:470) | 2 | + `wf→roundTripsᵇ`, `issues-empty→roundTrips` (§6.4) — co-located per G-A8 (axiom-consumer policy; the module's own header states it, :103-110) |
| `src/Aletheia/Protocol/Message.agda` | changed | unchanged | runtime | 3 | `FormatDBCText : JSON → Bool → StreamCommand` (:56); `DBCTextResponse : String → List ValidationIssue → Response` (:110-112) |
| `src/Aletheia/Protocol/Routing.agda` | changed | unchanged | runtime | 3 | `tryFormatDBCText` (:58-61): absent `strict` ⇒ `false`; present-but-non-Bool ⇒ typed `RouteErr` (§7.1) |
| `src/Aletheia/Protocol/Handlers.agda` | changed | unchanged | runtime (gate-watched file — gains NO new import) | 3 | dispatch arm :330 threads the Bool |
| `src/Aletheia/Protocol/Handlers/FormatDBCText.agda` | changed | unchanged | runtime | 3 | handler pipeline (§8); contract comment :81-123 rewritten |
| `src/Aletheia/Protocol/ResponseFormat.agda` (response arms) | changed | unchanged | runtime | 3 | `DBCTextResponse` arm (:250) gains `issues`; `errorExtras` arm for `TextRoundTripFailed` mirroring the `ValidationFailed` arm (:169-172) |
| `src/Aletheia/Error.agda` | changed | unchanged | runtime | 3 | `TextRoundTripFailed : List ValidationIssue → HandlerError` beside `ValidationFailed` (:293) + `handlerErrorCode` arm (:324 region); `RouteInvalidField : String → RouteError` (:222-233) + `formatRouteError` + `routeErrorCode "route_invalid_field"` arms (:235-266) |
| `src/Aletheia/Protocol/FrameProcessor/Properties/Handlers.agda` | changed | unchanged | proof tree (reached via root `FrameProcessor/Properties.agda`, Shakefile.hs:392) | 3 | restate `handleFormatDBCText-preserves-state` (:105-110) over the 3-arg signature — stays a 2-clause `refl` proof because the handler keeps the `(state , respond …)` pair at arm level (§8) |
| `src/Aletheia/Protocol/ResponseFormat/Properties.agda` | changed | unchanged | proof tree (root, Shakefile.hs:391) | 3 | `formatResponse-ack-unique` arm :44 → `(DBCTextResponse _ _) ()` (still refutable: the new emit is a ≥3-field JObject vs Ack's 1 field; import :16 unchanged) |

These two proof-module rows close the enumeration gap the panel found: a full-tree grep for `FormatDBCText`/`DBCTextResponse` confirms **no other** constructor/consumer sites exist outside this table (Message.agda:56, Routing.agda:58-70, Handlers.agda:40/132/330, the handler module, and the two Properties files).

---

## 3. Reduction inherited for free

`wellFormedFromValidity : ∀ (d : DBC) → All MessageWF (DBC.messages d) → All (WFAttribute (collectDefs (DBC.attributes d))) (DBC.attributes d) → AllPairs _≢_ (map DBCMessage.id (DBC.messages d)) → DBC.unresolvedValueDescs d ≡ [] → WellFormedTextDBCAgg d` (WellFormedFromValidity.agda:131-147, verified) discharges the five name-stop fields unconditionally. The checker decides only the four hypotheses. Within `MessageWF` (verified 9 fields, Message.agda:559-578), three more are free: `fb-bound` (vacuous — `dlcBytes-bounded`, de-privatized), `name-pre`/`send-pre` (`identNameStop`, WellFormedFromValidity.agda:78-83, definitionally the same Σ). Within `SignalLineWF`: `name-stop` free (`signalNameStop` :96-97), `recv-head-stop` free after the new universal lemma (§5.1), `presence-wf` shares the `wfps` witness. **Residual genuine decisions:** per signal — 2 arithmetic bounds (`wf-sigs`), byteOrder-split 1–3 bounds (`pvs`), presence shape (`wfps`); per message — `mc`, `sig-names-unique`; per attribute — `attr-wfs`; per DBC — `msg-ids-unique`, `unresolved-empty`.

---

## 4. Slice 1a — the runtime checker (`Aletheia.DBC.TextParser.WellFormedCheck`)

House import conventions apply throughout (`_++ₗ_` for list append, `_≟ᶜ_` for Char). All functions cold-path; Dec allocation is acceptable here (the CLAUDE.md hot-path rule is per-frame streaming only). Imports: `requireDec` / `requireDec-sound/-complete` from `Aletheia.DBC.Validity.Combinators` (defined there, :36-48); `concatMap-≡[]-sound/-complete` and `++-≡[]-split/-combine` **from `Aletheia.DBC.Validity.ListLemmas` directly** (Combinators imports them without `public` at :21-23 — they are not re-exported). Instantiated at `ValidationIssue` mirroring `Validator/Checks.agda`.

```agda
-- Arithmetic families: decide the EXACT propositions the WF records carry
-- (requireDec over stdlib Decs; soundness is requireDec-sound one-liners).
checkSignalBounds : DBCSignal → List ValidationIssue
-- requireDec (SignalDef.startBit sd <? max-physical-bits)      (mkIssue IsWarning StartBitOutOfRange …)   ++ₗ
-- requireDec (SignalDef.bitLength sd <? suc max-physical-bits) (mkIssue IsWarning BitLengthExcessive …)
-- Reuses CHECK 15/16's IssueCode VALUES (StartBitOutOfRange / BitLengthExcessive) but NOT their Decs:
-- CHECK 15's Dec (Checks.agda:419, <? max-physical-bits) matches the record field exactly; CHECK 16's
-- Dec (Checks.agda:433, ≤? max-physical-bits) is propositionally equivalent to but a DISTINCT proposition
-- from the record's `bitLength < suc max-physical-bits` (Formatter/WellFormed.agda:44). The checker
-- decides the `<? suc` form itself, so requireDec-sound lands the record field with no ≤/< conversion.

pvIssues : (frameBytes : ℕ) → DBCSignal → List ValidationIssue
pvIssues fb s = pvGo (DBCSignal.byteOrder s) fb (DBCSignal.signalDef s) (…name for detail…)
pvGo : ByteOrder → ℕ → SignalDef → String → List ValidationIssue
-- LittleEndian: requireDec (1 ≤? bitLength) (…BitLengthZero…)
-- BigEndian:    requireDec (1 ≤? bitLength) … ++ₗ
--               requireDec (startBit + bitLength ∸ 1 <? fb * 8) (…SignalExceedsDLC…) ++ₗ
--               requireDec (bitLength ∸ 1 ≤? startBit) (…BigEndianMSBLayout…)   -- checked by NO validator check today
-- EXPOSED SCRUTINEE (feedback_expose_scrutinee_for_external_rewrite): pvGo takes the
-- ByteOrder as an argument so Sound can `with DBCSignal.byteOrder s in eq` externally.

presenceIssue : DBCSignal → List ValidationIssue           -- = pGo (DBCSignal.presence s) …
pGo : SignalPresence → String → List ValidationIssue
-- Always → []; When _ (_ ∷ []) → []; When _ (_ ∷ _ ∷ _) → mkIssue IsWarning MultiValueMuxSelector … ∷ []

-- Master coherence: Bool leaves, exposed on the findMuxMaster result.
isAlwaysᵇ  : SignalPresence → Bool                          -- match
masterOkᵇ  : List Char → DBCSignal → Bool
-- masterOkᵇ n s = (Identifier.name (DBCSignal.name s) ≡csᵇ n) ∧ isAlwaysᵇ (DBCSignal.presence s)
wGo        : List Char → SignalPresence → Bool              -- Always → true; When m _ → Identifier.name m ≡csᵇ n
whenOkᵇ    : List Char → DBCSignal → Bool                   -- = wGo n (DBCSignal.presence s)
mcGo       : Maybe (List Char) → List DBCSignal → Bool
-- mcGo nothing  _    = true
-- mcGo (just n) sigs = any (masterOkᵇ n) sigs ∧ all (whenOkᵇ n) sigs
masterCoherentᵇ : List DBCSignal → Bool                     -- = mcGo (findMuxMaster sigs) sigs
mcIssue : List DBCSignal → List ValidationIssue             -- if masterCoherentᵇ sigs then [] else [MuxMasterIncoherent]

-- Uniqueness: decide the record fields' EXACT mapped forms directly (no bridge needed).
checkSigNamesUnique : List DBCSignal → List ValidationIssue
-- requireDec (allPairs? (λ i j → ¬? (i ≟ᴵ j)) (map DBCSignal.name sigs)) (…DuplicateSignalName…)
checkMsgIdsUnique : List DBCMessage → List ValidationIssue
-- requireDec (allPairs? (λ x y → ¬? (x ≟-CANId y)) (map DBCMessage.id msgs)) (…DuplicateMessageId…)

-- Attributes (checked NOWHERE today): exposed on the lookupDef result.
wfAttrTypeIssues   : AttrType → List ValidationIssue        -- ATEnum [] → [AttributeEnumEmpty]; else []
vmtᵇ               : AttrType → AttrValue → Bool            -- 5×5 double match (VMT pairs true, else false)
enumOkᵇ            : AttrType → AttrValue → Bool            -- ATEnum ls / AVEnum n → match findLabel (nthLabel k ls) ls: just m → m ≡ᵇ k; nothing → false; else true
attrGo             : Maybe AttrDef → (name : List Char) → (v : AttrValue) → (isDefault : Bool) → List ValidationIssue
-- nothing → [UnknownAttributeName]; just def → (if vmtᵇ … then [] else [AttributeValueTypeMismatch])
--                                            ++ₗ (if isDefault ∧ not (enumOkᵇ …) then [AttributeEnumDefaultUnstable] else [])
attrIssues         : List AttrDef → DBCAttribute → List ValidationIssue   -- 3-ctor dispatch into attrGo / wfAttrTypeIssues
checkAttrs         : List DBCAttribute → List ValidationIssue             -- concatMap (attrIssues (collectDefs attrs)) attrs

checkUnresolved : List RawValueDesc → List ValidationIssue  -- one IsWarning UnknownValueDescriptionTarget per entry (CHECK-23 code reuse)

checkTextMessage : DBCMessage → List ValidationIssue
-- concatMap (λ s → checkSignalBounds s ++ₗ pvIssues (dlcBytes dlc) s ++ₗ presenceIssue s) sigs
--   ++ₗ mcIssue sigs ++ₗ checkSigNamesUnique sigs

wfTextIssues : DBC → List ValidationIssue
-- checkMsgIdsUnique msgs ++ₗ concatMap checkTextMessage msgs
--   ++ₗ checkAttrs (DBC.attributes d) ++ₗ checkUnresolved (DBC.unresolvedValueDescs d)
```

All emitted with `IsWarning` severity ("outside the proven round-trip envelope") — as is V2's divergence issue on the default format-anyway path, per the ratified severity convention (success responses carry warnings only; §7.2). Inside a strict refusal the divergence issue is emitted with `IsError` severity (§8). Detail strings built with the validator's existing helpers (`nameStr`, `showℕ` — precedent Checks.agda).

**Slice-1 kernel footprint (the re-slice).** The 8 new `IssueCode` constructors (Types.agda:355-376) and the matching 8 `formatIssueCode` arms (ResponseFormat.agda:99-120 — a total function; adding constructors without arms breaks the exhaustiveness check of a module in Main's runtime closure) land in Slice 1, in the same commit as the checker. This is **wire-inert**: no handler constructs an issue with the new codes until Slice 3, so nothing new can serialize, and the binding-side code mirrors can safely stay in Slice 3 (there is no kernel↔binding issue-code exhaustiveness gate; C++ has an `Unknown`+`code_raw` fallback and Rust an `Unknown(String)` fallback regardless).

## 5. Slice 1b — the soundness/completeness tree (proof side)

### 5.1 Signal leaves (`Sound/Signal.agda`) — easy

```agda
signalBounds-sound : ∀ (s : DBCSignal) → checkSignalBounds s ≡ [] → WellFormedSignal s
-- split via ListLemmas.++-≡[]-split (house lemma, already used by the validator proofs);
-- two requireDec-sound; assemble the 2-field WellFormedSignalDef record
-- (Formatter/WellFormed.agda:41-48). `< suc n` IS the record's bitLength-bound form —
-- the checker decides it directly, so no ≤/< conversion is needed.

pvGo-sound : ∀ (bo : ByteOrder) (fb : ℕ) (sd : SignalDef) (nm : String) (s : DBCSignal)
  → DBCSignal.byteOrder s ≡ bo → DBCSignal.signalDef s ≡ sd
  → pvGo bo fb sd nm ≡ [] → PhysicallyValid fb s
-- match bo: LE arm → pv-LE byteOrder-eq (requireDec-sound …); BE arm → pv-BE with the three
-- requireDec-sound facts, transported through the signalDef equation (subst/cong, no rewrite
-- over any parser-bearing goal — there is none here). Caller in Sound.agda uses
-- `with DBCSignal.byteOrder s in eq` at the OUTER level only (proof-side with-in-eq is fine;
-- the checker side is already exposed, per feedback_with_in_eq_outer_abstraction_barrier).

pGo-sound : ∀ (p : SignalPresence) (nm : String) → pGo p nm ≡ [] → WellFormedTextPresence p
-- 3-way match: yes wftp-always / yes wftp-when-single / (∷ _ ∷ _) → the emitted singleton
-- list ≡ [] is refuted by λ().

-- Universal receiver-head lemma. Home: Properties/Topology/Signal.agda, placed OUTSIDE the
-- `private` block that opens at :247 (build-RecvHeadStop :268-279 is inside it and must stay
-- private; the new lemma must be importable by Sound consumers).
recvHeadStop : ∀ (cr : CanonicalReceivers) → RecvHeadStop cr
-- Mirror build-RecvHeadStop's FOUR clauses exactly (verified :272-279 — the non-empty-identifier
-- case splits singleton `mkIdent (c ∷ cs) _ ∷ []` vs ≥2 `∷ s ∷ rest`, because the emitted
-- comma-separated string reduces differently; same match depth ⇒ same refl shapes:
-- 'V',_,refl,refl for mkCanonical []; ⊥-elim vp for mkIdent [] vp; c , cs ++ₗ [] , refl , _
-- for the singleton; c , _ , refl , _ for ≥2) but replace the SuffixStops premise's head fact
-- with isIdentStart→¬isHSpace c (T-∧₁ w) — the identNameStop move (WellFormedFromValidity.agda:72-83,
-- CharClassDisjoint.agda:76). ~35 LOC.
```
Completeness duals (`…-complete : P → f ≡ []`): `requireDec-complete` + `++-≡[]-combine`; `pGo-complete` by matching the `WellFormedTextPresence` constructor.

### 5.2 Master coherence (`Sound/Master.agda`) — the hard lemma

```agda
isAlwaysᵇ-sound : ∀ (p : SignalPresence) → T (isAlwaysᵇ p) → p ≡ Always            -- match
wGo-sound : ∀ (n : List Char) (p : SignalPresence) → T (wGo n p)
  → ∀ (m : Identifier) (vs : List⁺ ℕ) → p ≡ When m vs → Identifier.name m ≡ n
-- match p: Always arm → λ m vs eq → ⊥ via eq (Always ≡ When: absurd unification, λ());
-- When m′ vs′ arm → match eq refl (constructor-injectivity unification, --without-K-safe),
-- then ≡csᵇ-sound (Identifier.agda:235) on the T fact.

mcGo-sound : ∀ (mm : Maybe (List Char)) (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ mm → mcGo mm sigs ≡ true → MasterCoherent sigs
-- nothing → mc-no-mux eq.  just n →
--   split via Data.Bool.Properties.T-∧ (:846, Equivalence.to) into
--     hₐ : T (any (masterOkᵇ n) sigs)  and  h_w : T (all (whenOkᵇ n) sigs);
--   any⁻ (Any/Properties.agda:181) → Any (T ∘ masterOkᵇ n) sigs;
--   Data.List.Membership.Propositional `find` (re-export of Setoid:51) →
--     (ms , ms∈sigs , tOk); T-∧-split tOk → nameFact/alwaysFact;
--   ≡csᵇ-sound → Identifier.name (DBCSignal.name ms) ≡ n;
--   isAlwaysᵇ-sound → DBCSignal.presence ms ≡ Always;
--   all⁺ (All/Properties.agda:670) → All (T ∘ whenOkᵇ n) sigs; All.map wGo-sound (per element,
--     instantiating the abstract p at DBCSignal.presence s — no with needed because wGo is
--     exposed on the presence);
--   assemble mc-mux n eq ms ms∈sigs nameEq presEq slaves.
-- Tactic discipline: the with-in-eq happens ONCE, in the top-level wrapper
-- masterCoherentᵇ-sound (sigs) = `with findMuxMaster sigs in eq` feeding mcGo-sound — never
-- stacked (feedback_no_stacked_with_in_proofs); all per-element reasoning is on abstract
-- scrutinee arguments, never on projections under with.

mcGo-complete : ∀ (mm : Maybe (List Char)) (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ mm → MasterCoherent sigs → mcGo mm sigs ≡ true
-- mc-no-mux: the two findMuxMaster equations force mm ≡ nothing (trans (sym eq₁) eq₂), then refl.
-- mc-mux: equations force mm ≡ just masterName; any-side via
--   lose (Membership.Propositional:34) / Any.map over ms∈sigs with ≡csᵇ-complete + isAlwaysᵇ-complete,
--   then any⁺ (:175); all-side via All.universal-style tabulation of wGo-complete from the
--   slave Π-field, then all⁻ (:676); recombine with T-∧ (Equivalence.from).
```

### 5.3 Attributes (`Sound/Attr.agda`)

```agda
vmtᵇ-sound   : ∀ (t : AttrType) (v : AttrValue) → T (vmtᵇ t v) → ValueMatchesType t v
-- 25-case double match; 5 diagonal yes-cases (VMTInt/…/VMTHex, Common.agda:93-98), off-diagonal T false absurd.
enumOkᵇ-sound : ∀ (t : AttrType) (v : AttrValue) → T (enumOkᵇ t v) → DefaultEnumOK t v
-- non-(ATEnum,AVEnum) pairs: DefaultEnumOK = ⊤, return tt. (ATEnum ls, AVEnum n): expose the
-- findLabel result (helper on Maybe ℕ); just m arm: ≡ᵇ⇒≡ (Data.Nat.Properties) then cong just;
-- nothing arm: T false absurd.
wfAttrType-sound : ∀ (t : AttrType) → wfAttrTypeIssues t ≡ [] → WfAttrType t
-- 5-way match; ATEnum [] refuted by the nonempty singleton ≢ [].

attrGo-sound : ∀ (defs : List AttrDef) (a : DBCAttribute) → attrIssues defs a ≡ [] → WFAttribute defs a
-- 3-ctor dispatch. For Default/Assign: `with lookupDef (name…) defs in eq` at the OUTER proof
-- level (checker exposed via attrGo); nothing arm refutes (UnknownAttributeName singleton ≢ []);
-- just def arm: eq : lookupDef … ≡ just def is EXACTLY the constructor's first premise
-- (Foundations.agda:151-159); vmtᵇ-sound + enumOkᵇ-sound fill the rest → wfDefault / wfAssign / wfDef.
```
Completeness duals by matching the `WFAttribute` constructor and rewriting the carried `lookupDef` equation into the exposed helper (`cong (λ r → attrGo r …) lookupEq`).

### 5.4 Top assembly (`Sound.agda` facade)

```agda
messageWF-from-check : ∀ (m : DBCMessage) → checkTextMessage m ≡ [] → MessageWF m
-- concatMap-≡[]-sound (from Aletheia.DBC.Validity.ListLemmas — imported DIRECTLY; Combinators'
-- import of it at :21-23 is non-public) splits the per-signal segment into per-element nils;
-- per signal derive (WellFormedSignal, PhysicallyValid, WellFormedTextPresence) — decide the
-- presence witness ONCE and share it into wfps AND item-pres (SignalLineWF via All.map with
-- name-stop = signalNameStop s, recv-head-stop = recvHeadStop (DBCSignal.receivers s));
-- fb-bound = dlcBytes-bounded (DBCMessage.dlc m) (de-privatized, JSONParser/MessageWF.agda:50-67);
-- name-pre/send-pre = identNameStop (definitional, same Σ as Topology/Message.agda:279-282);
-- mc from masterCoherentᵇ-sound; sig-names-unique = requireDec-sound of the allPairs? Dec
-- (the Dec already decides the field's EXACT Identifier-level mapped form — no bridge).

wfTextIssues-sound : ∀ (d : DBC) → wfTextIssues d ≡ [] → WellFormedTextDBCAgg d
-- ++-≡[]-split 4-way; msg-ids via requireDec-sound (exact mapped form);
-- All.map messageWF-from-check over the concatMap split; attrGo-sound lift;
-- unresolved: match the list — [] → refl; (_ ∷ _) → nonempty checkUnresolved refutes;
-- finish with wellFormedFromValidity d … (WellFormedFromValidity.agda:131-147).

wfTextIssues-complete : ∀ (d : DBC) → WellFormedTextDBCAgg d → wfTextIssues d ≡ []
-- project the Agg fields; per-family -complete duals; concatMap-≡[]-complete; ++-≡[]-combine.
```

### 5.5 The two mechanical validator bridges (home: `WellFormedFromValidity.agda`)

Not needed by the checker (it decides the mapped forms directly — a deliberate simplification), but written anyway (~40 LOC) because the handler's contract comment (:100-103) and DEFERRED_ITEMS E.2 cite them as unwritten, and they formalize "validator-clean ⇒ 2 of 4 hypotheses" for documentation-grade consumers of `Validity/Theorem.soundness` (:68-99, `ValidDBC.uniqueIds` unmapped at Validity.agda:108, `uniqueSigNames` String-level at :110-111):

```agda
uniqueIds→msg-ids-unique : ∀ {msgs : List DBCMessage}
  → AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
  → AllPairs _≢_ (map DBCMessage.id msgs)
-- = AllPairsₚ.map⁺ {R = _≢_} {f = DBCMessage.id} (AllPairs/Properties.agda:45); the source shape
-- is judgmentally (_≢_ on DBCMessage.id) via Function.Base._on_ — instantiate implicits explicitly.

sigNameStr≢→name≢ : ∀ {s₁ s₂ : DBCSignal}
  → signalNameStr s₁ ≢ signalNameStr s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂
-- λ strNeq nameEq → strNeq (cong (λ i → fromList (Identifier.name i)) nameEq); closes
-- definitionally because signalNameStr = fromList ∘ Identifier.name ∘ DBCSignal.name (Types.agda:298-299).
-- SAFE direction only — needs no fromList-injectivity, no axiom. (The REVERSE direction is the
-- one axiom-tainted corner in this landscape and is NOT needed anywhere in this plan.)

uniqueSigNames→sig-names-unique : ∀ {sigs : List DBCSignal}
  → AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂) sigs
  → AllPairs _≢_ (map DBCSignal.name sigs)
-- = AllPairsₚ.map⁺ ∘ AllPairs.map sigNameStr≢→name≢ (AllPairs.map at stdlib AllPairs:44).
```

---

## 6. Slice 2 — V2: the exact check

### 6.1 Decidable equality: what exists, what's missing

**Ceiling today** (`DBC/Properties/Equality.agda`, 103 lines, read in full): `_≟-List⁺ℕ_` (private), `_≟-SignalPresence_` (:37-44), `_≟-SignalDef_` (:47-69), `_≟-vd_` (private, :72-77), `_≟-DBCSignal_` (:80-103, the top). Leaves elsewhere: `_≟ᴵ_` (Identifier.agda:188), `_≟ᶜʳ_` (CanonicalReceivers.agda:160), `_≟-ByteOrder_` (Endianness), `_≟-CANId_` (DBCHelpers.agda:34-42, collapses to ℕ because CANId's bound is **irrelevant `.()`** — Frame.agda:41-43), `_≟ᵈ_` (DecRat:266).

**Missing** (all in new `Aletheia.DBC.Properties.Equality.Full`, house chain-`with` style, `no`-branches via `cong`-projection contraposition, exactly like `_≟-DBCSignal_`):
`_≟-VarType_` (3×3 match) · `_≟-IntDecRat_` / `_≟-NatDecRat_` (refinement records per the repo's `record { value; witness : T (predicateᵇ value) }` pattern — memory/project_refinement_types_pattern.md: `_≟ᵈ_` on `value`, close the **relevant** witness with `T-irrelevant` — the `_≟ᴵ_` :161 pattern) · `_≟-Node_` · `_≟-ValueTable_` (reuses de-privatized `_≟-vd_`) · `_≟-EnvVar_` · `_≟-SignalGroup_` (`≡-dec _≟ᴵ_`) · `_≟-CommentTarget_` (5 ctors) · `_≟-DBCComment_` · `_≟-AttrScope_` (7-ctor enum) · `_≟-AttrType_` (bounds via IntDecRat/DecRat/NatDecRat eq; labels via `≡-dec (≡-dec _≟ᶜ_)`) · `_≟-AttrValue_` · `_≟-AttrTarget_` · `_≟-AttrDef_` · `_≟-AttrDefault_` · `_≟-AttrAssign_` · `_≟-DBCAttribute_` · `_≟-RawValueDesc_` · `_≟-DLC_` (§6.2) · `_≟-DBCMessage_` (6-field chain: `_≟-CANId_`, `_≟ᴵ_`, `_≟-DLC_`, `_≟ᴵ_`, `≡-dec _≟ᴵ_`, `≡-dec _≟-DBCSignal_`) · `_≟-DBC_` (9-field chain over the verified DBC record, Types.agda:269-288).

### 6.2 The former "hard blocker", now LOW risk: `DLC` carries an `@0` witness

`record DLC { code : ℕ ; @0 bounded : T (code <ᵇ suc maxDLC-FD) }` (CAN/DLC.agda:73-78, verified). Unlike CANId's irrelevant `.()` field, `@0` fields are runtime-erased but NOT definitionally irrelevant, so a *generic* Dec-≡ over the record is blocked (memory/project_identifier_eq_revisit.md: "`cong₀` blocked by `--without-K`"). The closed-code enumeration sidesteps this:

```agda
dlc-code-inj : ∀ (d₁ d₂ : DLC) → DLC.code d₁ ≡ DLC.code d₂ → d₁ ≡ d₂
-- Match both records; after refl the codes unify. Enumerate the shared code over the 16
-- closed numerals 0..15: in each, (c <ᵇ 16) REDUCES to true, so both witnesses inhabit
-- T true = ⊤, and η-for-⊤ makes them convertible WITHOUT inspecting the erased variables
-- — `refl` closes each clause. Literals ≤ 15 are under the ≥20 literal ceiling
-- (feedback_literaltoobig_suc_chain). Catch-all: code = suc¹⁶ n makes (c <ᵇ 16) reduce to
-- false, so bounded : T false = ⊥ — close with an absurd pattern on the ERASED field.
_≟-DLC_ : (d₁ d₂ : DLC) → Dec (d₁ ≡ d₂)
-- with DLC.code d₁ ≟ DLC.code d₂ ; yes → yes (dlc-code-inj d₁ d₂ eq) ; no ¬p → no (¬p ∘ cong DLC.code)
```

**In-tree precedent (the panel's find, verified):** `dlcBytes-bounded` at JSONParser/MessageWF.agda:50-67 ALREADY enumerates this exact record over the 16 closed codes and closes the catch-all with an absurd pattern **on the `@0` field** — `dlcBytes-bounded (mkDLC (suc¹⁶ _) ())` at :67 — type-checking today under `--safe --without-K`. That was the plan's only genuinely novel ingredient; the sole residual novelty in `dlc-code-inj` is the η-⊤ convertibility of two erased witnesses inside a relevant `refl` goal, which is standard. **Risk downgraded to LOW.** The lemma is still spiked FIRST in Slice 2 (S2.1 — ~40 LOC, cheap insurance), but the fallbacks below are contingencies, not near-term expectations, and there is no case for pre-negotiating them:

- **(F1)** state V2's comparison against an observational setoid `_≈DBC_` (propositional everywhere except DLC compared by `code`) and prove `roundTripsᵇ d ≡ true → parseText (formatText d) ≈ inj₂ d` — semantically exact (T-witnesses are unique when inhabited; every consumer of DLC projects `code`/`dlcBytes`), but the headline lemma's phrasing weakens.
- **(F2)** migrate `DLC.bounded` from `@0` to irrelevant `.()` matching CANId. **Corrected blast radius (the original draft's was wrong):** this does NOT change the MAlonzo constructor arity — both modalities erase; `mkAgdaDLC = AgdaDLC.C_mkDLC_28` is already applied at arity 1 (Marshal.hs:174-176), and the CANId comment in the same file (:183-185) confirms irrelevant proof fields compile away identically. No Marshal.hs edit is forced. The real F2 costs are **proof-side**: every relevant consumer of the witness must be re-audited under irrelevance restrictions (the erased-absurd clauses in `dlcBytes-bounded`-style proofs; the repo's irrelevance-cascade lesson, feedback_data_ctor_irrelevance_cascade), plus `check-erasure`/`check-fidelity` re-verification and a confirming benchmark (representation governance on a type built per frame on the binary hot path — expected neutral, but the rule is unconditional). F2 still **requires explicit user approval**, for these reasons rather than the (incorrect) arity one.
- V1-only fallback (§7.6) keeps the envelope shippable in the worst case.

### 6.3 The V2 runtime check and its soundness story

```agda
-- Aletheia.DBC.TextParser.RoundTripCheck  (runtime, --safe --without-K)
rtGo : DBCTextParseError ⊎ DBC → DBC → Bool
rtGo (inj₁ _)  _ = false          -- parse-back FAILURE counts as divergence (honest: e.g. an
rtGo (inj₂ d″) d = ⌊ d ≟-DBC d″ ⌋ -- AVFloat under an ATInt def emits a line the parser rejects)

roundTripsWithᵇ : DBC → String → Bool          -- handler passes the already-computed text
roundTripsWithᵇ d txt = rtGo (parseText txt) d
roundTripsᵇ : DBC → Bool
roundTripsᵇ d = roundTripsWithᵇ d (formatText d)
```

**Soundness — axiom-free, and this is the precise sense in which V2's YES is ground truth by construction** (`Properties/RoundTripCheck/Sound.agda`):
```agda
rtGo-sound : ∀ (r : DBCTextParseError ⊎ DBC) (d : DBC) → rtGo r d ≡ true → r ≡ inj₂ d
-- inj₁: false ≡ true absurd. inj₂ d″: with d ≟-DBC d″ — yes p → cong inj₂ (sym p); no → absurd.
roundTripsᵇ-sound : ∀ (d : DBC) → roundTripsᵇ d ≡ true → parseText (formatText d) ≡ inj₂ d
-- = rtGo-sound (parseText (formatText d)) d.  ~10 lines, fully --safe: unlike the universal
-- theorem it is CONDITIONED ON THE EVALUATION — parseText (formatText d) is literally run and
-- the Dec's yes-branch IS the proof object for THIS d. No WF hypothesis, no String axiom
-- (both sides of the traced equation live at the String level already, computed by the same
-- runtime primitives the axiom bridges for the abstract proof).
```
**What "byte-identical" means vs structural ≡:** the check compares the parse-back **value** `d″` with `d′` under propositional `_≡_` (modulo §6.2's DLC caveat under fallback F1 only). Value-level ≡ immediately yields **emitted-text fixpointing**: `d″ ≡ d′ → formatText d″ ≡ formatText d′`, i.e. text → DBC → text is byte-identical from the emitted artifact onward — the sense used by TextFormatter.agda:19-21 ("the roundtrip target … at the DBC *value* level"). What is NOT claimed: byte-fidelity of the *input JSON document* (key order etc. — out of scope, same as today), and the round-trip is stated about `d′ = deriveNodesIfEmpty dbc` (the value actually formatted, per the handler's existing normalization :72-75).

**Cost bound:** one extra `parseText` over the emitted text (O(|text|), same machinery whose cold-path cost is the +3–5% measured for DBC-text positions) + one `_≟-DBC_` traversal (O(size of DBC) with per-leaf Dec allocation). Net: the `format_dbc_text` command roughly doubles in wall time; it is a cold, per-command path — the frame hot path is untouched. Input size is already bounded upstream by the JSON-side parse (cat 32 bounds), so the re-parse inherits the same bound. (The §8 handler guarantees the "one extra parseText, one formatText" accounting by argument-passing, not `let` — see the sharing note there.)

### 6.4 The stitching theorems (appended to `Substrate/Unsafe.agda`, per G-A8 co-location — the module's own header states the policy at :103-110)

```agda
wf→roundTripsᵇ : ∀ (d : DBC) → WellFormedTextDBCAgg d → roundTripsᵇ d ≡ true
-- cong (λ r → rtGo r d) (parseText-on-formatText d wf), then rtGo (inj₂ d) d ≡ true via a
-- dec-refl helper (⌊ d ≟-DBC d ⌋ ≡ true : with d ≟-DBC d — yes → refl; no ¬p → ⊥-elim (¬p refl)).

issues-empty→roundTrips : ∀ (d : DBC) → wfTextIssues d ≡ [] → roundTripsᵇ d ≡ true
-- = wf→roundTripsᵇ d ∘ wfTextIssues-sound d.  CONTRAPOSITIVE (docs + tests): a V2 divergence
-- implies wfTextIssues is non-empty — at least one V1 diagnostic accompanies every divergence,
-- MODULO THE SUBSTRATE AXIOMS (see trust-base note below).
```
Substrate.Unsafe is already a `proofModules` root (Shakefile.hs:470) — appends need no new root and stay inside the single allowlisted non-`--safe` module (`check-invariants` clean).

**Trust base, stated precisely.** These two theorems route through `parseText-on-formatText` (:119-124), whose `toList∘fromList` step IS one of the two postulated bridging axioms (:95-97). They are therefore model-level guarantees with exactly the headline theorem's trust base (the two String axioms + compiler), unlike `roundTripsᵇ-sound` (§6.3), which is axiom-free. In the theoretical corner where the axioms' operational justification fails (constructible only if JSON `\u`-unescaping could fabricate Text-unrepresentable chars; normal wire chars come from Data.Text unpacking), runtime V2 could report `false` with zero V1 diagnostics — acceptance (e) still holds on the wire because the handler prepends the divergence issue itself (§8), independent of any theorem. Docs and the §Recommendation carry the "modulo the Substrate axioms" qualifier wherever the coherence guarantee is stated.

---

## 7. Wire design

### 7.1 Command (backward-compatible, malformed-input honest)

`{"command": "formatDBCText", "dbc": {…}, "strict": true}` — `strict` optional. Ctor becomes `FormatDBCText : JSON → Bool → StreamCommand`. **Routing semantics (revised — `lookupBool` alone is insufficient):** `lookupBool` returns `nothing` both when the key is absent AND when it is present-but-non-Bool (`lookupWith` collapses the two at Protocol/JSON/Lookup.agda:110-113), which would silently coerce `"strict": "true"` (a string) to non-strict formatting — violating the repo's non-fatal-≠-silent rule, and inconsistent with Routing's typed-RouteErr posture for every other field mis-shape (Routing.agda:36-61). `tryFormatDBCText` therefore splits the lookup:

```agda
tryFormatDBCText obj with lookupByKey "dbc" obj
... | nothing  = inj₁ (RouteErr (InContext "FormatDBCText" MissingDBCField))
... | just dbc with lookupByKey "strict" obj
...   | nothing = inj₂ (FormatDBCText dbc false)                 -- absent ⇒ default false
...   | just v with getBool v
...     | just b  = inj₂ (FormatDBCText dbc b)
...     | nothing = inj₁ (RouteErr (InContext "FormatDBCText"
                            (RouteInvalidField "strict")))       -- present-but-malformed ⇒ typed error
```

`RouteInvalidField : String → RouteError` is new (Error.agda:222-233 has no invalid-type constructor today), with a `formatRouteError` arm ("field 'strict' must be a boolean") and `routeErrorCode … = "route_invalid_field"` (:259-266 family). One kernel test + one Python parity test pin the malformed case.

### 7.2 Responses

Default (always formats; `issues` always present, possibly `[]` — wire-additive; all four decoders read only `"text"` today and tolerate extra fields, verified table §7.4):
```json
{"status":"success","text":"VERSION \"\"\n…","issues":[
  {"severity":"warning","code":"text_roundtrip_divergence","detail":"re-parsing the emitted text does not reproduce the input DBC"},
  {"severity":"warning","code":"multi_value_mux_selector","detail":"message 291 signal 'S3': multi-value mux selector — text form emits only the first selector value"}]}
```
Strict refusal (only when `strict:true` AND `roundTripsWithᵇ d′ txt ≡ false` — exact, never over-refusing):
```json
{"status":"error","code":"handler_text_roundtrip_failed","message":"FormatDBCText: …","has_errors":true,"issues":[ …same element shape… ]}
```
Kernel: `DBCTextResponse : String → List ValidationIssue → Response` (Message.agda:110-112); ResponseFormat arm (:250) appends `("issues", JArray (map formatValidationIssue issues))`; `TextRoundTripFailed : List ValidationIssue → HandlerError` beside `ValidationFailed` (Error.agda:293) with `handlerErrorCode … = "handler_text_roundtrip_failed"` (:324 region) and an `errorExtras` arm mirroring the `ValidationFailed` arm (:169-172 — `has_errors` + `issues`; bindings reuse the one issue decoder). Severity vocabulary stays the closed 2-value set (ResponseFormat.agda:82-84), and the ratified convention governs its use: on a `status:"success"` response every issue — including the divergence verdict — is `"warning"`; inside the strict `status:"error"` refusal the divergence issue is `"error"` (mirroring `handler_validation_failed`).

**Wire-convention items to document in PROTOCOL.md:**
1. **RATIFIED (2026-07-12): the existing severity convention is preserved, and PROTOCOL.md now states it as a protocol-wide invariant.** Success responses carry warning-severity issues only (the `ParsedDBCResponse` rule, Message.agda:105-108); error-severity issues appear only inside `status:"error"` refusal envelopes; `validateDBC`'s both-severity report keeps its own `status:"validation"`. The divergence issue is therefore severity-context-dependent — `warning` on the default format-anyway success path, `error` inside a strict refusal — and its *fact* content lives in the code `text_roundtrip_divergence`, not in the severity. ("A good interface is one that does not surprise." The rejected alternative — severity-as-finding-class, `severity:"error"` inside `status:"success"` — is recorded here for history only.)
2. **Reused codes have context-dependent severity.** `SignalExceedsDLC`/`BitLengthZero` are error-class from the validator but `IsWarning` from the format envelope; CHECK 15/16's codes were already warning-class and stay so; `text_roundtrip_divergence` follows the same context rule per item 1. PROTOCOL.md's issue-code table gains a per-context severity column for these rows.

### 7.3 Issue codes (IssueCode +8 in **Slice 1**; `formatIssueCode` +8 same slice; unprefixed per the ResponseFormat.agda:86-98 rationale)

| Agda constructor | wire code | fires on | class |
|---|---|---|---|
| `TextRoundTripDivergence` | `text_roundtrip_divergence` | V2 verdict false (Slice-3 handler; V2-only — see §7.6) | **actual loss** (error) |
| `MultiValueMuxSelector` | `multi_value_mux_selector` | `wfps` (Topology.agda:147-148 head-only emission; ExtendedMux.agda:113 drop) | actual loss (warning by mode design) |
| `MuxMasterIncoherent` | `mux_master_incoherent` | `mc` | envelope |
| `BigEndianMSBLayout` | `big_endian_msb_layout` | `pv-BE` `msb-ge-len` (no validator counterpart) | envelope |
| `UnknownAttributeName` | `unknown_attribute_name` | `lookupDef` miss | envelope/likely-loss |
| `AttributeValueTypeMismatch` | `attribute_value_type_mismatch` | `ValueMatchesType` | envelope/likely parse-back failure |
| `AttributeEnumEmpty` | `attribute_enum_empty` | `WfAttrType` (`ATEnum []`) | envelope |
| `AttributeEnumDefaultUnstable` | `attribute_enum_default_unstable` | `DefaultEnumOK` | envelope |

Reused existing codes (no mirror cost): `StartBitOutOfRange`, `BitLengthExcessive` (CHECK 15/16's code values; §4 note on the CHECK-16 Dec-form difference), `BitLengthZero`, `SignalExceedsDLC` (pv arithmetic; `startBit+len∸1 < fb*8` ⇔ CHECK 8's form given `len ≥ 1`), `DuplicateMessageId`, `DuplicateSignalName`, `UnknownValueDescriptionTarget` (CHECK-23 code for `unresolved-empty`).

### 7.4 Four-binding lift table (per #152 pattern; entry points verified by the landscape team)

| Binding | sender (add `strict`) | success decoder (read optional `issues`) | new-code mirrors | error-code gate arm |
|---|---|---|---|---|
| Python | `python/aletheia/client/_client.py:523-568` + async `asyncio/_client.py:180-182` + `types.py:493-503/677-687` (`NotRequired`) | inline in `_client.py` | `codes/_issue.py:23-46` +8 | `_response_parsers.py` new gate beside :115 (`handler_text_roundtrip_failed` → typed exception) |
| Go | `go/aletheia/client.go:418-439` | `json.go:1474-1494` | `result.go:179+` consts | `json.go:985-1005` `checkErrorStatus` arm |
| C++ | `cpp/src/client.cpp:225-232` + `json_serialize.cpp:508-511` | `json_parse.cpp:1122-1139` | `validation.hpp` enum + `issue_code_table` (unknown→`Unknown`+`code_raw` keeps forward-compat) | `json_parse.cpp` `make_json_error` arm beside :262-264 |
| Rust | `rust/src/lib.rs:645-656` + `async_client.rs:190-195` | `response.rs:595-608` | `response.rs:156-200` (+`Unknown(String)` fallback exists) | `response.rs:323-360` arm + `error.rs` variant beside :73-82 |

Binding API shape (**RATIFIED 2026-07-12: no sibling methods — in-place, BREAKING**): each binding's existing `format_dbc_text` changes signature to mirror its own parse-path shape (the #150/#152 precedent), returning text **plus** issues: Python `format_dbc_text(dbc, *, strict=False) -> DBCTextResponse | ErrorResponse` (TypedDict with `text` + `issues`, like `ParsedDBCResponse`; `dbc_to_text` follows suit), Go `FormatDBCText(ctx, dbc, opts…) (*DBCText, error)` (struct with `Text` + `Warnings`, like `*ParsedDBC`), C++ `format_dbc_text(...) -> Result<DbcText>` (struct with `text` + `issues`, like `Result<ParsedDbc>`), Rust `format_dbc_text(...) -> Result<(String, Vec<ValidationIssue>), Error>` (like `parse_dbc_text`) — plus the strict-refusal typed error on all paths. Labeled **BREAKING** in the CHANGELOG per the Go-#61 precedent. Rationale (user, 2026-07-12): pre-adoption window — no compatibility bridge, no deprecation cycle, no sibling ever created; the API's end state is its only state.

**Legacy docstring obligation (same PR as the behavior change):** all four bindings' existing `format_dbc_text` docs assert "`parse_dbc_text(format_dbc_text(d))` returns `d` byte-identical for any well-formed DBC" — verified at `python/aletheia/client/_client.py:523-530`, `go/aletheia/client.go:413`, `cpp/include/aletheia/client.hpp:110`, `rust/src/lib.rs:643-646`. These are gated doc surfaces (doc examples run in CI). Each is rewritten with the method's new signature to state the operational contract: "returns the text plus the round-trip verdict and diagnostics; with `strict`, refuses instead of emitting divergent text" — replacing the static qualifier with the checkable one.

### 7.5 Matrix / docs / CLI / CHANGELOG timing

- **FEATURE_MATRIX.yaml**: new row `dbc_text_roundtrip_check` (4 cells, entries = the enriched `format_dbc_text` methods; structural gates ×4 verify entry-resolves + reason-non-empty only). Existing `dbc_text_format` row gets a `notes` update.
- **PROTOCOL.md**: new `formatDBCText` schema section (the numbered-commands gap :75-556 is real — write the section, don't patch a table); error-code table rows for `handler_text_roundtrip_failed` and `route_invalid_field` (:1329-1335 family); issue-code table +8 with the per-context severity column; the two wire-convention deltas from §7.2.
- **Same-commit doc obligations** (feedback_findings_doc_disposition_sync): rewrite the handler contract comment (FormatDBCText.agda:81-123 — the "does NOT discharge at runtime" paragraph becomes "discharged observably at runtime; see WellFormedCheck/RoundTripCheck"), flip DEFERRED_ITEMS.md E.2 route (b) to shipped (full closure still gated on A.1/A.3 losslessness), WellFormedFromValidity.agda header comment, the four legacy binding docstrings (§7.4).
- **CHANGELOG timing (corrected):** `check_changelog.py` watches `^Shakefile\.hs$` (INFRA_PATTERNS, tools/check_changelog.py:67-68), and Slices 1 AND 2 both edit Shakefile.hs (`proofModules` additions). **Each slice PR carries its own CHANGELOG bullet** — one line under the existing `[Unreleased]` header for the appropriate category, merged under the single existing `### Added`/`### Changed` header (feedback_changelog_one_header_per_category), not deferred to Slice 3. Slice 3 carries the full public-API + wire entry.
- **CLI**: none — verified no CLI calls `format_dbc_text` (all three `format-dbc` subcommands are the binary `format_dbc` JSON re-export). No CLI_SCENARIOS.yaml changes forced.

### 7.6 V1-only fallback delta (if S2.1 fails and F1/F2 are both declined)

Not a footnote — a scope change with its own wire surface:
- **Issue table:** the `TextRoundTripDivergence` row (§7.3) is dropped (it can only fire from V2). The table has no error-class row; all issues are warnings.
- **Strict trigger:** `strict:true` refuses iff `wfTextIssues d′` is non-empty (decidable, complete against the Agg by `wfTextIssues-complete`, but sufficient-not-necessary against actual round-tripping — the over-refusal caveat RETURNS in this mode and must be documented).
- **Refusal wording:** "round-trip not *proven*" — never "will not round-trip".
- **Acceptance restatement:** (a′) default mode on a multi-value-mux DBC returns text + issues including `multi_value_mux_selector` (no divergence code exists); (b′) `strict:true` on the same input returns `handler_text_roundtrip_failed` whose issues are exactly `wfTextIssues d′`; (c) unchanged; (d) unchanged; (e′) every strict refusal carries ≥1 diagnostic — trivially, since non-empty `wfTextIssues` IS the trigger; (f′) all warning wording says "outside the proven round-trip envelope".
- Slices 1 and 3's *code* are otherwise unchanged; §6.4's stitching theorems reduce to `issues-empty→roundTrips`' V1 half (`wfTextIssues d ≡ [] → parseText (formatText d) ≡ inj₂ d`, via `wfTextIssues-sound` + `parseText-on-formatText` — still Substrate-housed).

---

## 8. Handler pipeline (Slice 3)

```agda
handleFormatDBCText : JSON → Bool → StreamState → StreamState × Response
handleFormatDBCText dbcJSON strict state with parseDBCWithErrors dbcJSON
... | inj₁ err = (state , Response.Error (WithContext "FormatDBCText" err))
... | inj₂ dbc = (state , respond (deriveNodesIfEmpty dbc))
  where
  -- SHARING DISCIPLINE (corrected from rev. 1): Agda `let` is eliminated by
  -- substitution at elaboration — a let-bound `txt` used twice becomes two
  -- copies of `formatText d′` in the elaborated term, and MAlonzo does no CSE.
  -- Sharing is achieved the repo way: thread each computed value as a HELPER
  -- ARGUMENT (one lazily-shared thunk in the compiled Haskell, evaluated at
  -- most once). The `(state , respond …)` pair stays at arm level so the
  -- preserves-state proof remains a 2-clause refl (feedback_whereblock_provability).
  -- Severity is context-dependent per the ratified convention (§7.2 item 1):
  -- warning on the format-anyway success path, error inside the strict refusal.
  divergenceIssue : Severity → ValidationIssue
  divergenceIssue sev = mkIssue sev TextRoundTripDivergence
                          "re-parsing the emitted text does not reproduce the input DBC"

  finish : String → Bool → List ValidationIssue → Response
  finish txt rt diags =
    if strict ∧ not rt
    then Response.Error (WithContext "FormatDBCText"
           (HandlerErr (TextRoundTripFailed (divergenceIssue IsError ∷ diags))))
    else Response.DBCTextResponse txt
           (if rt then diags else (divergenceIssue IsWarning ∷ diags))

  respond : DBC → Response
  respond d′ = withText (formatText d′)
    where
    withText : String → Response
    withText txt = finish txt (roundTripsWithᵇ d′ txt) (wfTextIssues d′)
```

`formatText`, `parseText` (inside `roundTripsWithᵇ`), and `wfTextIssues` each run exactly once per command; `rt` and `diags` are shared Bool/list thunks. State stays untouched (read-only contract preserved). The strict-refusal arm fires only when `rt ≡ false`, so its issue list always leads with the divergence issue — this is what makes acceptance (e) hold on the wire unconditionally (independent of §6.4's axioms). Under the V1-only fallback (§7.6), `rt` is replaced by `null diags` and `divergenceIssue` disappears.

**Proof repairs in the same slice (missed in rev. 1, now owned):**
- `handleFormatDBCText-preserves-state` (FrameProcessor/Properties/Handlers.agda:105-110) is quantified over the old 2-argument signature; restate as `∀ (dbcJSON : JSON) (strict : Bool) state → proj₁ (handleFormatDBCText dbcJSON strict state) ≡ state` — the proof body is unchanged (2 clauses, `refl`/`refl` over the same `with parseDBCWithErrors`) because the pair shape stays at arm level.
- `formatResponse-ack-unique` (ResponseFormat/Properties.agda:44) matches `(DBCTextResponse _)`; becomes `(DBCTextResponse _ _) ()` — still refuted structurally (the new emit is a ≥3-field JObject vs Ack's 1-field shape; the module comment :24-28 stays accurate).
Both parents are `proofModules` roots (Shakefile.hs:391-392), so `check-properties` enforces these — but they are planned edits, not gate surprises.

---

## 9. Proof order (what unblocks what) + per-step verification

Heap discipline: proof modules `-M4G` first, escalate to `-M8G`/`-M16G` only if needed (AGENTS/agda.md Verification); anything touching Message/Handlers/Main re-checks `Aletheia/Main.agda` with `-N32 -M16G`. New `.agda` files get SPDX dash-comment headers (§2). Slices 1 and 2 each carry a one-line CHANGELOG bullet (Shakefile.hs is CHANGELOG-watched — §7.5).

1. **S1.0** Types.agda `IssueCode` +8 (appended after the existing 21) + ResponseFormat.agda `formatIssueCode` +8 arms. Wire-inert (nothing emits the codes yet); binding mirrors deferred to S3.2 (§4). → `agda +RTS -N32 -M16G -RTS Aletheia/Main.agda`; `cabal run shake -- build` (both files are in Main's closure; `check-ffi-exports` expected CLEAN — the shim imports no MAlonzo module from Types/ResponseFormat, §11 R4).
2. **S1.1** `WellFormedCheck.agda` (runtime-side code, no proofs; no MAlonzo output yet — not in Main's closure until S3.1, per §1). → `cd src && agda +RTS -N32 -M4G -RTS Aletheia/DBC/TextParser/WellFormedCheck.agda`. (No `gen-ffi-modules` here — it would be a no-op.)
3. **S1.2** `recvHeadStop` universal in Topology/Signal.agda (outside the `private` block at :247); de-privatize `dlcBytes-bounded` (JSONParser/MessageWF.agda:41). → type-check both modules; `check-properties`.
4. **S1.3** `Sound/Signal.agda` (bounds/PV/presence, sound + complete). → module check `-M4G`.
5. **S1.4** `Sound/Master.agda` (`mcGo-sound/-complete`) — the schedule-risk lemma; do after S1.3 confidence. → module check `-M8G`.
6. **S1.5** `Sound/Attr.agda`. → module check.
7. **S1.6** `Sound.agda` facade (`messageWF-from-check`, `wfTextIssues-sound/-complete`) + §5.5 bridges in WellFormedFromValidity. Add `Sound.agda` to `proofModules`. → `cabal run shake -- check-properties && cabal run shake -- check-proof-coverage` (new proof modules must be walk-reachable or the gate fails). CHANGELOG bullet for the Shakefile edit.
8. **S2.1 (SPIKE, do before committing to V2)** `dlc-code-inj` + `_≟-DLC_`, **appended at the end of** CAN/DLC.agda (mangled-name stability — §2, §11 R4). → module check; on the (now LOW-likelihood) failure, decide F1/F2 with the user before proceeding.
9. **S2.2** `Equality.Full` (+ `_≟-vd_` de-privatization in Equality.agda). → module check `-M4G` (no `gen-ffi-modules`/`build` value here — no MAlonzo output until S3.1).
10. **S2.3** `RoundTripCheck.agda` (runtime-side) + `Properties/RoundTripCheck/Sound.agda` (new `proofModules` root). → module checks (`RoundTripCheck` is the parseText+formatText double-closure module — budget `-M16G`, expect fine since it consumes interfaces only); `check-properties`, `check-proof-coverage`. CHANGELOG bullet for the Shakefile edit.
11. **S2.4** Substrate/Unsafe appends (`wf→roundTripsᵇ`, `issues-empty→roundTrips`). → `agda +RTS -N32 -M16G -RTS Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`; `check-invariants` (allowlist unchanged); `check-properties`.
12. **S3.1** Message.agda (both ctors) + Routing (`strict` split + `RouteInvalidField`) + Error.agda (`TextRoundTripFailed`, `RouteInvalidField` + code arms) + ResponseFormat (DBCTextResponse arm + errorExtras arm) + Handlers.agda:330 + handler rewrite + **the two proof-module repairs (§8)**. → `agda +RTS -N32 -M16G -RTS Aletheia/Main.agda` (the heap-critical chain); **`cabal run shake -- gen-ffi-modules`** (THE run that lists the 3 new MAlonzo modules — omitting it fails `build` via `-Werror=missing-home-modules`); then FULL gate set: `build`, `check-properties`, `check-invariants`, `check-no-properties-in-runtime`, `check-erasure`, `check-fidelity`, `check-ffi-exports` (expected CLEAN per §11 R4; any drift = stop and investigate, not shrug-and-resnapshot).
13. **S3.2** Bindings ×4 (senders/decoders/mirrors/lifts/new methods + legacy docstring rewrites) + parity tests (incl. the malformed-`strict` RouteErr case) + FEATURE_MATRIX row + gates. → `cd python && pytest && basedpyright && pylint`; `cd go && go test ./aletheia/ -race`; `cd cpp && ctest`; `cargo test + fmt --check + clippy`.
14. **S3.3** PROTOCOL.md / CHANGELOG (full entry) / DEFERRED_ITEMS / contract comments; benchmarks `bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput` (mandatory for runtime code per AGENTS universal rule; expected neutral — cold path — record the comparison); mutation-lane hygiene if Python tests import tools.

---

## 10. Perf discipline

- The format/validate path is **cold** (one command, not per-frame). Dec allocation (`allPairs?`, `_≟-DBC_`, `requireDec`) is acceptable there; **nothing new is imported by any frame-hot-path module** (`Protocol/StreamState`, `CAN/Encoding*`, `CAN/Batch*`, `LTL/*` untouched). `WellFormedCheck`/`RoundTripCheck` are imported ONLY by `Handlers/FormatDBCText.agda` and the Properties tree — assert this in review.
- `_≟ᴵ_`/Identifier Dec history (~5-10% Signal Extraction from the 2026-04-24 data-repr change) is a representation cost already paid; no new leakage vector.
- V2 adds one parse + one compare per format command (§6.3 cost bound, guaranteed by §8's argument-passing sharing). No `Fin`, no reflection, no instance args.
- Benchmark before commit anyway (rule is unconditional for runtime code); expected inside the ±5% WSL2 band.
- Type-check heap: the risky chains are (a) `RoundTripCheck` (first module importing both `TextParser` and `TextFormatter` aggregates — interfaces only, precedent says fine) and (b) the `Message → Handlers → Main` recheck (the reason FormatDBCText was split; we add only small leaf imports to the split module, not to Handlers). Both budgeted `-M16G`; blow-ups are R3 below.

---

## 11. Risk register

| # | Risk | Likelihood | Mitigation / fallback |
|---|---|---|---|
| R1 | `dlc-code-inj` erased-absurd clause rejected | **low** (was medium) | In-tree precedent: `dlcBytes-bounded` (JSONParser/MessageWF.agda:50-67) already pattern-matches this record over the 16 closed codes AND closes the catch-all with an absurd pattern on the `@0` field, under `--safe --without-K`, today. Residual novelty = η-⊤ convertibility of two erased witnesses in a relevant refl goal (standard). Spike anyway (S2.1, ~40 LOC). If it fails: F1 observational setoid (always works, weakens phrasing); F2 `.()` migration (**corrected**: no MAlonzo arity change — Marshal.hs:174-176/:183-185 — costs are proof-side irrelevance re-audits + governance; user approval required). V1-only (§7.6) keeps the envelope shippable. |
| R2 | `mcGo-sound` with-abstraction hell | medium | Checker is exposed-scrutinee BY CONSTRUCTION (`mcGo`/`wGo`/`pvGo`/`attrGo` take the scrutinee as an argument); one outer `with … in eq` per wrapper; stdlib `any⁻`/`all⁺`/`find`/`T-∧` verified present at the cited lines. If a specific reconstruction balloons past ~500 LOC, stop and surface alternatives (feedback_step_back_when_proofs_balloon) — e.g. carry the master index as data. |
| R3 | Heap blow-up: `RoundTripCheck` or the Main chain | low-medium | Leaf-module isolation (interfaces cache); `-M16G` tripwire; worst case split V2 into a sibling handler module mirroring the ParseDBCText/FormatDBCText split precedent. |
| R4 | MAlonzo mangled-name / snapshot drift | **low — expect all gates CLEAN** (was mis-stated "high (expected)") | The shim references no MAlonzo names from Protocol.Message or DBC.Types (verified import lists: AletheiaFFI.hs:29-41 — Main.JSON/Main.Binary/StreamState.Types/CAN/Trace/RationalRenderer/DecimalEntry; Marshal.hs:21-26 — CAN.*; BinaryOutput.hs:23-27 — stdlib codes; ConstructorTest.hs:41-52 — Main.JSON/Binary + CAN), and Main.agda is untouched, so `check-ffi-exports` should pass unchanged. The ONE real vector: Marshal.hs and ConstructorTest.hs import `MAlonzo.Code.Aletheia.CAN.DLC` (`T_DLC_18`/`C_mkDLC_28`) — mitigated by APPENDING `dlc-code-inj`/`_≟-DLC_` at the end of CAN/DLC.agda (declaration-order numbering stays stable). Any snapshot/`sed` prompt that appears anyway = stop and investigate; never normalize drift-gate churn. |
| R5 | `wfTextIssues-complete` (esp. mc-complete) heavier than budgeted | medium | Completeness is what guarantees warnings never fire on WF DBCs. If it balloons, DO NOT silently drop — surface scope options to the user (feedback_no_silent_proof_reframing). |
| R6 | Copilot/panel objection to a Properties-named module (`Equality.Full`) in runtime closure | low | Precedent chain documented (§1); alternative non-Properties name `Aletheia.DBC.Equality` costs nothing — decide at review (§13). |
| R7 | Binding decoder strictness on the new success field | low | Verified: all four tolerate extra success fields; severity stays in the closed 2-value vocabulary AND the success-carries-warnings-only convention is unchanged (§7.2 item 1), so no decoder semantics shift; unknown-code fallbacks exist (C++ `Unknown`+`code_raw`, Rust `Unknown(String)`). |
| R8 | `allPairs?` O(n²) on adversarial cardinality | low | Cold path; cardinality already bounded upstream (cat 32); mirrors validator CHECK 1's existing triangular cost. |

---

## 12. Acceptance criteria ("done" means)

**Theorems/definitions that must exist and type-check under the stated pragmas:**
1. `wfTextIssues : DBC → List ValidationIssue` (runtime, `--safe --without-K`, no Properties imports).
2. `wfTextIssues-sound : ∀ d → wfTextIssues d ≡ [] → WellFormedTextDBCAgg d` and `wfTextIssues-complete` (proof tree, `--safe`).
3. `recvHeadStop : ∀ cr → RecvHeadStop cr` (universal, no SuffixStops premise; importable — outside the private block).
4. `roundTripsᵇ-sound : ∀ d → roundTripsᵇ d ≡ true → parseText (formatText d) ≡ inj₂ d` (**axiom-free**, `--safe`).
5. `wf→roundTripsᵇ` and `issues-empty→roundTrips : ∀ d → wfTextIssues d ≡ [] → roundTripsᵇ d ≡ true` (in Substrate/Unsafe, the sole axiom consumers added; documented as sharing the headline theorem's trust base, §6.4).
6. `_≟-DBC_ : (d₁ d₂ : DBC) → Dec (d₁ ≡ d₂)` (or the F1-fallback setoid variant, explicitly user-approved).
7. Bridges `uniqueIds→msg-ids-unique`, `sigNameStr≢→name≢`, `uniqueSigNames→sig-names-unique`.

**Gates:** `build`, `check-properties` (incl. the two repaired proof modules, §8), `check-invariants` (Unsafe allowlist still = 1 module), `check-no-properties-in-runtime`, `check-erasure`, `check-fidelity`, `check-ffi-exports` (expected clean — R4), `check-proof-coverage` (new roots registered), SPDX headers on new files, full `tools/run_ci.py` green; benchmark comparison recorded (cold-path-neutral); CHANGELOG bullet present in EVERY slice PR (§7.5).

**User-visible behavior:** (a) default `format_dbc_text` on a multi-value-mux DBC returns text + a non-empty `issues` array including `multi_value_mux_selector` and `text_roundtrip_divergence`; (b) `strict:true` on the same input returns `handler_text_roundtrip_failed` with the same issues; (c) `strict:true` on an **envelope-clean fixture family** — fixtures with `wfTextIssues d′ ≡ []` (validator-clean alone does NOT suffice: `big_endian_msb_layout` has no validator counterpart, the four attribute-WF issues are validator-unchecked, and CHECK 15/16 are warning-class, so validator-error-clean DBCs can still carry V1 issues) — returns text with `issues: []`; the theorem-side guarantee for such fixtures is `wfTextIssues-complete` ∘ Agg-WF; (d) all four bindings expose the issues + typed strict error + the malformed-`strict` typed RouteErr, and pass new parity tests; (e) every strict refusal carries ≥1 diagnostic — unconditionally on the wire (the handler prepends the divergence issue on every refusal path, §8), and additionally every V2 divergence is accompanied by ≥1 V1 diagnostic modulo the Substrate axioms (§6.4); (f) wording discipline: warnings say "outside the proven round-trip envelope", only `text_roundtrip_divergence` says "does not reproduce", and no surface claims per-cause attribution of diagnostics to the divergence mechanism.

Under the V1-only fallback, criteria (a)/(b)/(e)/(f) are replaced by (a′)/(b′)/(e′)/(f′) from §7.6.

**Docs:** PROTOCOL.md section + tables + the two wire-convention deltas (§7.2); FEATURE_MATRIX row; CHANGELOG; handler contract comment + DEFERRED_ITEMS E.2 + WellFormedFromValidity header + the four legacy binding docstrings updated in the same PR as the behavior change.

---

## 13. Decisions (three of four ratified by the user, 2026-07-12)

1. **Module naming — RATIFIED**: `Aletheia.DBC.Properties.Equality.Full`.
2. **Binding API shape — RATIFIED**: no sibling methods; `format_dbc_text` is enriched in place, labeled BREAKING (§7.4). The sibling-naming question is moot.
3. **Success-envelope severity — RATIFIED**: the existing convention is preserved — success responses carry warning-severity issues only; error severity appears only inside strict refusal envelopes (§7.2 item 1).
4. **OPEN — if S2.1 fails** (low likelihood): F1 vs F2 vs V1-only — user decision, with F2's corrected cost model (§6.2).
