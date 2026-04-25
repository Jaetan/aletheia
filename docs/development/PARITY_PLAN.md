# Cross-Binding Parity Plan

> **Status:** Active. Locked 2026-04-20 as the post-R17 roadmap.
> **Scope:** Make Python / C++ / Go bindings expose the same user-facing capabilities, enforce it mechanically.

## Goal

All three bindings expose the same complete set of user-facing capabilities, expressed idiomatically per language. **Parity means behavioral equivalence, not identical API shapes.** Python `async def`, Go `func(ctx context.Context, ...)`, and C++ `std::stop_token` can all express the same cancellation contract — that is parity.

Cross-language divergence is a bug per `feedback_cross_language_parity.md`. This plan is the mechanism that stops drift from happening by accident.

## Approach — Three Parts

1. **Language-agnostic logic → Agda core.** DBC text parsing, DBC metadata, mux queries live in the verified kernel and flow to every binding via the JSON protocol. One implementation, three surfaces.
2. **Language-native ergonomics.** Cancellation, streaming iteration, async composition: idiomatic per language, behaviorally equivalent (same cancel semantics, same partial-commit rules, same error surface).
3. **Declarative feature matrix + structural gates.** `docs/FEATURE_MATRIX.yaml` is the single source of truth for what parity means. Each binding has a structural test that reads it and fails when its surface drifts.

## Locked Decisions (2026-04-20)

| | Decision |
|---|---|
| **A.1 Matrix source** | YAML as authoritative; markdown generated for reading. |
| **B.3 DBC parser scope** | Full cantools equivalence. User DBCs are unknown; minimal-subset risks silent rejection. |
| **B.3 cantools removal** | Drop the Python dep as soon as B.3 reaches equivalence (B.3.g). |
| **C.0 Cancellation SSOT** | Needs its own review round — including whether the doc should exist at all. |
| **API shape** | Idiomatic per language; cross-binding identity is behavioral, not syntactic. |

## Matrix Granularity Rule

**One row per user-facing capability, not per method.** "Load a DBC file" is a row. `cpp::load_dbc`, `go.LoadDBC`, `aletheia.load_dbc` are all entries on the same row. If the three bindings for a row fit on one line, the granularity is right.

**`not_applicable` requires `reason`.** A binding cell with `status: not_applicable` MUST carry a non-empty `reason` string. The structural test fails if either is missing. The canonical `not_applicable` example is CLI: C++ and Go are library bindings; a CLI is a host-application concern.

## Phases

### Phase A — Feature Matrix + Structural Gates

Sets the rules of the game. No Part 1 or Part 2 work lands without a matching matrix row.

- **A.1** Draft `docs/FEATURE_MATRIX.yaml` schema. Fields per row: `id`, `name`, `description`, optional `related` (for tracking items like R17-DEF-4), and `bindings.{python,cpp,go}.{status, entry?, reason?, notes?}`.
- **A.2** Seed with currently-shipped capabilities (~15 rows — RTS cores, structured logging, Check DSL, YAML/Excel check loaders, YAML DBC loader, batch frame send, core streaming, CAN-FD, Python-only DBC text parse, mux extraction, violation enrichment, validation errors, custom logger backend, MockBackend). Then add `planned` rows for every R17-DEF and pre-R17 backlog item.
- **A.3** Python structural test first (`python/tests/test_feature_matrix_parity.py`). Pass on the seeded matrix before mirroring.
- **A.4** Go structural test (`go/aletheia/feature_matrix_test.go`); uses `gopkg.in/yaml.v3`.
- **A.5** C++ structural test (`cpp/tests/test_feature_matrix_parity.cpp`); uses `yaml-cpp` (already a dep).
- **A.6** Wire all three into the default test battery. Cat 32 contract: absence = CI failure.

**Deliverable:** matrix plus three tests, all green on current code. After this, any new feature requires a matrix row or the gate fails.

### Phase B — Agda-Core Migrations (Part 1)

#### B.1 — DBC Metadata Exposure (Tier 1, R17-DEF-2)

Low risk; data is already preserved in the Agda core, just dropped at the FFI boundary. Scope of B.1 is strictly **Tier 1** — the three arrays that exist on `Aletheia.DBC.Types.DBC` and round-trip through `Formatter`/`JSONParser` today (`signalGroups`, `environmentVars`, `valueTables`). Fields that do not exist in the Agda core (nodes, comments, attributes, signal receivers) are carved out as **B.1.x** below.

- B.1.a Audit — **complete 2026-04-20.** Tier 1 fields: Agda core ✓, formatter ✓, optional-array parser ✓; dropped in `dbc_converter.dbc_to_json` and in `DbcDefinition` for all three bindings. Tier 2 fields: not in core.
- B.1.b ✅ Python `DBCDefinition` TypedDict — `signalGroups`, `environmentVars`, `valueTables` as `NotRequired` entries + supporting row TypedDicts (`DBCSignalGroup`, `DBCEnvironmentVar`, `DBCValueTable`). Landed in `2928f63`.
- B.1.c ✅ `dbc_to_json` — populates the three arrays from cantools (`db.signal_groups`, `db.environment_variables`, `db.dbc.value_tables`). Empty-list semantics preserved. Landed in `2928f63`.
- B.1.d ✅ Go `DbcDefinition` struct — matching fields + row types. Landed in `e458a3a` + `ffd8679` (fixup: env-var test asserts exact `Rational` numerator/denominator).
- B.1.e ✅ C++ `DbcDefinition` struct — matching fields + row types. Landed in `1cc3250` (+ `eced521` to ignore the clang-tidy CMake tree).
- B.1.f ✅ Roundtrip test: fully-loaded DBC → JSON → reparse → byte-identical, per-binding alongside existing DBC suites.
- B.1.g ✅ `dbc_metadata_tier1` row added to `docs/FEATURE_MATRIX.yaml`; all three bindings `implemented`. Landed in `75a728c`.

**Status:** ✅ Complete. **Matrix row:** `dbc_metadata_tier1` (implemented × 3).

#### B.1.x — DBC Metadata Tier 2 (nodes, comments, attributes, receivers)

Adds DBC fields that the Agda core does not currently carry. Heavier than B.1 because every step touches the verified kernel. Landed 2026-04-20 in two commits.

- B.1.x.a ✅ Extended `Aletheia.DBC.Types.DBC` with `nodes : List Node`, `comments : List DBCComment` (node/message/signal-scoped), `attributes : List DBCAttribute` (`BA_DEF_`, `BA_DEF_DEF_`, `BA_`, and rel variants). Extended `DBCSignal`/`DBCMessage` with `receivers : List String`. Split across **Commit 1** (`2367812`, nodes + comments + attributes) and **Commit 2** (`93c02bf`, `DBCSignal.receivers`; `DBCMessage.receivers` derived binding-side).
- B.1.x.b ✅ `JSONParser.agda` updated — optional-array parsing for nodes/comments/attributes; `receivers` serialized strictly on every signal with a `"receivers"` JSON wire key.
- B.1.x.c ✅ `Formatter.agda` + roundtrip properties closed in `Formatter/Properties.agda`, `MessageRoundtrip.agda`, `SignalRoundtrip.agda` before binding work started. `Float` bounds round-trip as exact `Rational` (`Fraction` in Python).
- B.1.x.d ✅ Validator updates — attribute-name uniqueness + comment target existence (Commit 1); node reference integrity via CHECK 21 `UnknownSignalReceiver` warning using the `liftPerSignal` combinator (Commit 2).
- B.1.x.e ✅ Binding structs widened + `dbc_to_json` population mirror B.1. Python `DBCNode` / `DBCComment` / `DBCAttribute*` TypedDicts; matching Go / C++ structs. `Vector__XXX` cantools placeholder stripped on parse and re-emitted as fallback when per-signal receivers are empty (cantools parity).
- B.1.x.f ✅ Cross-binding roundtrip tests — fully-loaded DBC with every Tier 2 field → identical `DbcDefinition` across all three bindings (per-binding `test_dbc_metadata_tier2.*` suites).
- B.1.x.g ✅ `dbc_metadata_tier2` row flipped to `implemented` × 3; `dbc_signal_receivers` row added for Commit 2 and flipped to `implemented` × 3. `dbc_message_senders` row (`BO_TX_BU_` transmitters on `DBCMessage.senders`) flipped to `implemented` × 3 in Commit 3.

**Commit 3 (landed in `fc4242f`) — `dbc_message_senders`:** `DBCMessage.senders : List String` — the `BO_TX_BU_` additional-transmitter list on `BO_` lines. Primary `sender : String` stays separate (Q1 option A). `dbc_to_json` splits cantools' merged `message.senders` at index 0 / 1: (primary + additional). New CHECK 22 `UnknownAdditionalSender` warning via `liftPerMessage`, reusing the `UnknownMessageSender` issue code with an "additional sender" disambiguation in the message text (Q2 yes). Completeness proof extended. 27 files, +438/−76.

**Status:** ✅ Complete. **Matrix rows:** `dbc_metadata_tier2`, `dbc_signal_receivers`, `dbc_message_senders` (all implemented × 3).

#### B.2 — Mux Query Helpers (R8, from `project_go_features_to_explore.md`)

Read-only query API over in-memory DBC. Agda already handles mux.

**Audit finding — helpers pre-existed across all three bindings.** The plan originally scoped 2–3 days of FFI-protocol work. Pre-flight audit found the surface was already implemented client-side on the parsed DBC value types (not through JSON/FFI) in every binding:

- **Python** (`python/aletheia/dbc_queries.py`, 9 pure-Python helpers): `is_multiplexed`, `always_present_signals`, `multiplexed_signals`, `multiplexor_names`, `mux_values`, `signals_for_mux_value`, `message_by_id`, `message_by_name`, `signal_by_name`. Re-exported from `aletheia/__init__.py`. Tests: `python/tests/test_dbc_queries.py` (28 cases).
- **Go** (`go/aletheia/dbc.go`, 9 methods): `DbcMessage.IsMultiplexed`, `AlwaysPresentSignals`, `MultiplexedSignals`, `MultiplexorNames`, `MuxValues`, `SignalsForMuxValue`, `SignalByName`; `DbcDefinition.MessageByID`, `MessageByName`. Tests: `go/aletheia/mux_test.go` (27 cases).
- **C++** (`cpp/include/aletheia/dbc.hpp` + `cpp/src/dbc.cpp`, 9 methods): `DbcMessage::is_multiplexed`, `always_present_signals`, `multiplexed_signals`, `multiplexor_names`, `mux_values`, `signals_for_mux_value`, `signal_by_name`; `DbcDefinition::message_by_id`, `message_by_name` (both with lazy-index cache). Tests: `cpp/tests/unit_tests_dbc.cpp` (14 TEST_CASEs, ~20 checks).

Behavioral parity confirmed by side-by-side inspection: the three suites exercise the same scenarios — empty signals, unknown multiplexor, unknown mux value, non-mux messages, extended-vs-standard CAN ID discrimination, lookup hit/miss.

- B.2.a ✅ Pre-existing: mux logic lives in Agda core (`SignalPresence` ADT in `src/Aletheia/DBC/Types.agda`); query surface is defined client-side against the parsed DBC value.
- B.2.b ✅ Not applicable: query helpers are pure-value-layer — no JSON protocol command is needed. The DBC is already parsed and held binding-side.
- B.2.c ✅ Pre-existing: `aletheia.is_multiplexed` and 8 sibling helpers (module `aletheia.dbc_queries`, re-exported at package level).
- B.2.d ✅ Pre-existing: `DbcMessage` / `DbcDefinition` methods on the parsed value (not on `Client`).
- B.2.e ✅ Pre-existing: `DbcMessage` / `DbcDefinition` methods on the parsed value (not on `Client`), with lazy-index caching on name/ID lookups.
- B.2.f ✅ Closed by this audit: **matrix rows** `dbc_queries_mux` (Go flipped `planned` → `implemented`) and new `dbc_lookup` (all three `implemented`). The structural gate in each binding's parity test resolves the new entries, providing the cross-binding parity check.

**Granularity note.** Per the matrix schema ("one entry per user-facing capability, not per method"), the six mux helpers cluster under `dbc_queries_mux` and the three lookup helpers under `dbc_lookup`. Lookup and mux-structure are distinct capabilities — a user can need entity lookup without caring about mux, and vice versa.

**Status:** ✅ Complete via audit. **Matrix rows:** `dbc_queries_mux` (implemented × 3), `dbc_lookup` (implemented × 3, new).

#### B.3 — DBC Text Parser in Agda (R17-DEF-4) — Heaviest Item

**Scope: full cantools equivalence** — users may feed DBCs with any construct cantools accepts, and silent rejection is worse than loud failure.

**Done-criterion: the construct inventory below must round-trip to cantools' parsed representation on the corpus. "Round-trip" here is semantic `DbcDefinition` equivalence (byte-identical JSON from `dbc_to_json`), not byte-identical DBC text — cantools canonicalizes on output (sort order, whitespace, optional-field emission), so a text-level comparison is the wrong oracle. The snapshot JSON corpus in `python/tests/fixtures/dbc_corpus/snapshots/` is the structural spec.**

**New Agda modules in scope (B.3.b/c/d):** `src/Aletheia/DBC/TextParser.agda` (grammar) AND `src/Aletheia/DBC/TextFormatter.agda` (canonical DBC-text emitter for the `parseText ∘ formatText ≡ id` roundtrip property). The existing `DBC/Formatter.agda` emits the JSON wire shape, not DBC text, so B.3.d cannot close without a text formatter.

| Category | Constructs |
|---|---|
| Metadata | `VERSION`, `NS_` (namespaces), `BS_` (bus speed) |
| Structure | `BU_` (nodes), `BO_` (messages), `SG_` (signals) |
| Signal attributes (inside SG_) | start bit, length, byte order (`0`/`1` = Motorola/Intel), signedness (`+`/`-`), factor, offset, min/max, unit, receiver nodes, mux indicator (`M`, `m<n>`) |
| Message attributes (inside BO_) | extended CAN ID (bit 31), CAN-FD flag (attribute-encoded), sender node, DLC |
| Value tables | `VAL_` (signal-scoped), `VAL_TABLE_` (global) |
| Attributes | `BA_DEF_`, `BA_DEF_DEF_`, `BA_`, `BA_DEF_REL_`, `BA_REL_` |
| Comments | `CM_` (node/message/signal scoped) |
| Signal groups | `SIG_GROUP_` |
| Signal value types | `SIG_VALTYPE_` (float32/float64) |
| Extended mux | `SG_MUL_VAL_` |
| Environment vars | `EV_`, `EV_DATA_`, `ENVVAR_DATA_` |

Plan:

- B.3.a ✅ Build the construct corpus: `python/tests/fixtures/dbc_corpus/` with 8 hand-authored DBCs (see `README.md` coverage map) covering every inventory row. `test_dbc_corpus_baseline.py` snapshots each through `dbc_to_json`; snapshots are the structural spec for B.3.d onward. Landed 2026-04-21.
- B.3.b ✅ Grammar designed in `Parser/Combinators.agda` style (structural recursion on length; `--safe --without-K` throughout). `DBC/TextParser.agda` + `DBC/TextFormatter.agda` skeletons plus `Properties.agda` facade placeholders landed per `feedback_properties_facade_split.md`. Commit `785d2cc`.
- B.3.c ✅ Implemented incrementally, bottom-up: B.3.c.1 lexical primitives (`441b0d2`) → c.2 `VERSION`/`NS_`/`BS_` (`977783f`) → c.3 `BU_`/`BO_`/`SG_` + `showℚ-dec` (`4fb5270`) → c.4 `VAL_`/`VAL_TABLE_` (`c6d8998`) → c.5 `BA_DEF_`/`BA_DEF_DEF_`/`BA_`/`BA_REL_` (`7b55340`) → c.6 `CM_` (`52454a0`) → c.7 `SIG_GROUP_` (`f36e531`) → c.8 `SIG_VALTYPE_` + `SG_MUL_VAL_` parse-and-drop (`926f189`) → c.9 `EV_` (`3399695`) → c.k `parseText`/`formatText` aggregator (`7d77dcb`) + `showℚ-dec` off-by-one fix (`a7f255e`).
- B.3.d ⏳ Roundtrip theorem — **universal form is the target**: `∀ d → parseText (formatText d) ≡ inj₂ d`. Per-fixture point verifications (the "corpus-shape" approach attempted earlier and reverted) are not an acceptable substitute — the done-criterion is a theorem that quantifies over the `DBC` domain, not a finite conjunction of concrete equalities. Corpus-based coverage belongs to B.3.j (binding-layer parity against cantools snapshots); B.3.d is the Agda-side property.

  **Pre-gate ✅ complete (2026-04-24).** Every ℚ-valued DBC-on-disk field migrated to the `DecRat` canonical form (`n / (2^a · 5^b)`), closing the decimal-precision gap that previously prevented `parseText (formatText d)` from trivially composing through the `_/_` gcd normaliser.  Six commits `0b7849b` → `c05083e` → `6fa29e3` → `dd9b770` → `917465b` → current:
    * **Commit 1/6** — `DecRat` type, canonicalisation, `_≟ᵈ_`, `toℚ`, `fromℚ?`.
    * **Commit 2/6** — `parseDecRat` + `showDecRat-dec` + `fromℚ?-after-toℚ` universal sketch.
    * **Commit 3/6** — EV_ (`EnvironmentVar.{initial,minimum,maximum}`) + Layer-4 closure of `fromℚ?-after-toℚ` + `NonTerminatingRational` parse error wired cross-binding.
    * **Commit 4/6** — SG_ (`SignalDef.{factor,offset,minimum,maximum}`) + `lookupDecRat` JSON combinator + `mkℚ`-direct `toℚ` runtime optimisation (closed 9–15% CAN-FD Signal Extraction regression, delivered +16% on CAN 2.0B Signal Extraction as a bonus).
    * **Commit 5/6** — Attributes (`ATFloat.{min,max}` + `AVFloat.value`); `TextParser.agda` / `TextFormatter.agda` aggregators added to `check-properties` walk (caught a latent `RawSignal`-vs-DecRat typing bug from Commit 4/6 that slipped past the main build because the TextParser tree is not in Main's transitive closure).
    * **Commit 6/6** — docs + memory + this PARITY_PLAN.md section.

  With the pre-gate closed, the remaining proof-layer work is the four-layer decomposition, each layer closeable independently:
  1. **String-side substrate**. `toList-++ₛ : toList (a ++ₛ b) ≡ toList a ++ₗ toList b`, plus `toList` behaviour on each primitive used by the emitter (`showℕ`, `showDecRat-dec`, identifier/string-literal emitters, enum-tag emitters). Unblocks `primStringToList` reduction past abstract record fields — the obstacle that stalls `refl` on the universal.
  2. **Per-primitive lemmas**. One `parseX (toList (emitX v) ++ₗ rest) ≡ inj₂ (v, rest)` for every parser/emitter pair (string literal, identifier, ℕ literal, DecRat literal, enum tags, ByteOrder, Signed/Unsigned, etc.). Locally provable from the substrate.  The DecRat-side per-primitive proofs are already closed (`fromℚ?-after-toℚ` is the universal at the storage layer).
  3. **Per-line-construct lemmas**. One per `VERSION`, `NS_`, `BS_`, `BU_`, `BO_`, `SG_`, `CM_`, `BA_DEF_`, `BA_DEF_DEF_`, `BA_`, `BA_REL_`, `VAL_`, `VAL_TABLE_`, `EV_`, `SIG_GROUP_`, `SIG_VALTYPE_`, `SG_MUL_VAL_`. Compose primitive lemmas along each construct's bind chain.
  4. **Top-level aggregator**. Compose line-construct lemmas along `parseDBCText`'s bind chain against `formatText`'s concatenation order. Structural induction over each list-of-X field in `DBC`.

  **Layer 1 ✅ complete (2026-04-24, Option 3a per user decision).** Code-level structural audit of the four options resolved the audit hedge in favour of Option 3a — the **2-axiom hybrid** with formatter refactored to `List Char` internals.  Substrate at `src/Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda` (148-of-149 status stamp + 1 allowlisted Unsafe; the only non-`--safe` module in the project, allowlisted by name in `Shakefile.hs check-invariants` alongside the `^postulate` exception scoped to the same file).  Substrate hosts the two stdlib-equivalent axioms:

  ```agda
  postulate
    toList∘fromList : ∀ (cs : List Char) → toList (fromList cs) ≡ cs
    fromList∘toList : ∀ (s  : String)    → fromList (toList s)  ≡ s
  ```

  Mirrors `Data.String.Unsafe` (proven by `trustMe` under `--with-K`); structurally unprovable in `--safe --without-K` because `primStringToList` / `primStringFromList` reduce only on closed terms.  Why two and not one: any path that keeps `DBC` storing identifiers/comments/units as `String` forces the second axiom — every per-primitive identifier roundtrip reduces to `fromList (toList name) ≡ name`.  Eliminating the second axiom would require Option 2 (move every `String` field in `DBC` to `List Char`), a far larger surface change.

  Formatter refactor: every per-section emitter (`Preamble` / `Topology` / `ValueTables` / `Attributes` / `Comments` / `SignalGroups` / `EnvVars` + `Emitter` primitives) now exports only `-chars` companions (`emitX-chars : … → List Char`); `formatChars : DBC → List Char` in `TextFormatter/TopLevel.agda` is the substrate the top-level proof reasons about; the only `String`-returning function in the formatter pipeline is `formatText = fromList ∘ formatChars`.  Parser entry points: `parseTextChars : List Char → ⊎` extracted from `parseText : String → ⊎ = parseTextChars ∘ toList`.  External behaviour unchanged — every test (Python 760, C++ 6, Go) passes against the refactored emitters.

  **Shake gates in place**: `check-properties` walks `DBC/TextParser/Properties.agda` (skeleton; will host the universal theorem in layer 4), plus the `DBC/TextParser.agda` + `DBC/TextFormatter.agda` aggregators (Commit 5/6).  `check-invariants` enforces the 1-Unsafe / 1-postulate-file allowlist project-wide.  Layer 2 work can start when ready.

  **Layer 2 — in progress (2026-04-24).** Two commits landed the Identifier primitive end-to-end:

  * **Commit 2a** (`9adbc46`) — `Identifier` type lifts from bare `String` to `record { name : String; valid : T (validIdentifierᵇ (toList name)) }`.  All identifier-valued DBC fields migrated (DBCSignal.name + receivers; DBCMessage.name + sender + senders; SignalGroup; EnvironmentVar; ValueTable; Node; CommentTarget; AttrTarget variants; SignalPresence.When).  Attribute names (AttrDef/AttrDefault/AttrAssign) stay `String` (DBC wire format encodes them as quoted literals, no identifier-grammar restriction).  T3-fixed (relevant `valid` field rather than `@0 valid` erased) because the stdlib `cong` required by `_≟ᴵ_` rejects erased function args and a custom `cong₀` needs K.  Accepted cost: 5–10% Signal Extraction regression on C++/Go (MAlonzo compiles `data MkIdent String AgdaAny` — two-field boxed, not a newtype).  Revisit angles documented in `memory/project_identifier_eq_revisit.md`.  Scope-infection: the 15 `DBC/TextParser/*.agda` modules drop `--safe` to import the axiom-using `mkIdentFromCharsUnsafe` from `Substrate.Unsafe`.

  * **Commit 2b** (`4559d5c`) — `parseIdentifier-roundtrip` at `List Char` level:

    ```agda
    parseIdentifier-roundtrip : ∀ pos i suffix
      → SuffixStops isIdentCont suffix
      → parseIdentifier pos (toList (Identifier.name i) ++ₗ suffix)
        ≡ just (mkResult i
                  (advancePositions pos (toList (Identifier.name i)))
                  suffix)
    ```

    `SuffixStops isIdentCont suffix` mirrors `parseNatural-showNat-chars`'s `SuffixStops isDigit` discipline; Layer 3 will discharge it via char-class disjointness (every grammar context that ends an identifier has `isIdentCont c ≡ false`).  Two structural refactors were needed: (a) `mkIdentFromCharsUnsafe` in `Substrate.Unsafe` moved from `with validIdentifierᵇ cs in eq` to `ifᵀ validIdentifierᵇ cs then (λ w → …) else nothing` — the `with` form triggered an ill-typed with-abstraction (`validIdentifierᵇ (toList name) != w`) because `Identifier.valid`'s type depends on the scrutinee; (b) `buildIdent h t` in `Lexer.agda` split into `fromMaybeIdent (mkIdentFromCharsUnsafe (h ∷ t))` so the `Maybe Identifier` value is externally rewritable via `cong fromMaybeIdent`.  New file `Properties/Primitives.agda` (253 lines): 5 staging probes + main theorem, composed via `bind-just-step` following `DecRatParse/Properties.parseDecRat-roundtrip-+suc` template.

  **Commit 2c** (`f315c6f`) — Tier A + Tier B primitive roundtrips closed.  Tier A: `parseByteOrderDigit-roundtrip`, `parseSignFlag-roundtrip`, `parseOptionalStandardScope-roundtrip` (5 cases incl. ASNetwork empty-emission), `parseRelScopeWS-roundtrip` (ASNodeMsg/ASNodeSig), `parseStringType-roundtrip`.  Tier B: `parseStringLit-roundtrip` (literal escape-body), `parseMuxMarker-IsMux-roundtrip` / `parseMuxMarker-NotMux-roundtrip` / `parseMuxMarker-SelBy-roundtrip` (mux marker variants embed `parseNatural`).  Tier C reclassified to Layer 3 (`ATInt`/`ATFloat`/`ATHex`/`ATEnum`/`SignalPresence` are per-line-construct payloads, not primitives — see `memory/project_b3d_universal_proof.md`).  Infrastructure: `Aletheia.Parser.Combinators.parseCharsSeq` lifted from `string`'s `where` clause to top-level export so Layer 2 proofs can reason about the inner recursion by name.

  **Layer 3 — in progress (2026-04-25).** Per-line-construct roundtrips compose Layer 2 primitives along each construct's bind chain.

  * **Commit 3a** (`804c584`) — Preamble: `parseVersion-roundtrip` + `parseBitTiming-roundtrip` + `parseNamespace-roundtrip`.  VERSION line + trailing blank lines (template-validates the bind-chain composition pattern); BS_: line with opaque tail (canonical empty-body emission); NS_ : 25-keyword block with newline-terminated `\t<keyword>` body lines.  Reusable infrastructure landed under `Properties/Preamble/Newline.agda` (exported via the Preamble facade): `isNewlineStart`, `parseNewline-match-LF` / `parseNewline-fail-on-stop`, `manyHelper-parseNewline-exhaust`, `manyHelper-one-iter`, `many-parseNewline-one-LF-stop`.  New `manyHelper-prog-cons` lemma (one-step iteration with non-empty tail) introduced for the NS_ keyword-line iteration.  Properties facade pattern (per `feedback_properties_facade_split.md`): `Properties/Preamble.agda` re-exports per-construct submodules under `Properties/Preamble/{Version,BitTiming,Namespace,Newline}.agda`; `Properties/Preamble/_Scratch.agda` carries a load-bearing reduction canary verifying `validIdentifierᵇ (toList kw)` reduces to `true` on every NS_ keyword (the `nsKeywords-valid : All (T ∘ validIdentifierᵇ ∘ toList) nsKeywords` discharge in the NS_ proof depends on this reduction).

  * **Commit 3b — Option C-broad ✅** (this commit): all four simple-line constructs with formatter pairs land together — `BU_` (node list, 611L), `VAL_TABLE_` (value table, 790L), `EV_` (env var, 1,581L), `CM_` (comment, 2,533L) — wired into `Properties.agda` via per-section facades (`Properties/Topology.agda`, `Properties/ValueTables.agda`, `Properties/EnvVars.agda`, `Properties/Comments.agda`) parallel to `Properties/Preamble.agda`.  All four type-check at the canonical `+RTS -N32 -M16G -RTS` cap.  CM_ proof closes the most complex Layer-3 construct: 5-way `CommentTarget` dispatch (`CTNetwork`/`CTNode`/`CTMessage`/`CTSignal`/`CTEnvVar`) via 4-fold `<|>`-chain (`parseBUTgt <|> parseBOTgt <|> parseSGTgt <|> parseEVTgt`, left-associative `infixl 3`) plus the outer fall-through `parseCommentTarget <|> pure CTNetwork`.  Per-target wrappers `wrapCTMessage` / `wrapCTSignal` (which use `with buildCANId r` to dispatch on out-of-range IDs) are discharged via `with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid`.  Heap blowup root-caused and fixed: `buildCANId-rawCanIdℕ`'s Extended clause used `rewrite n+ext∸ext≡n` over a goal containing nested `ifᵀ`s; under `--without-K` the with-abstraction generalised the entire goal type and ran the heap to multi-GB scale (`-M48G` insufficient).  Replaced with pointwise `subst` per AGENTS.md line 234 guidance — `Comment.agda` now type-checks at `-M16G`.  Notable patterns landed for BU_ in `Properties/Topology/Nodes.agda`: (a) η-on-record `map mkNode (map Node.name ns) ≡ ns` for the single-field `Node` record; (b) Σ-formulated `NodeNameStop` per-node precondition (non-empty `toList name = c ∷ cs` + `isHSpace c ≡ false`) — the `isIdentStart c → isHSpace c ≡ false` bridge lemma is owed at Layer 4; (c) `manyHelper-parseWSIdent-body` inductive over the node list with a fresh `afterNodes` position-walk helper aligned to `advancePositions` via `advancePositions-++`; (d) `sameLengthᵇ-lt` re-proven locally (currently private to `Properties/Preamble/Namespace.agda` — candidate for promotion to a shared module).  `EV_` brings 297 lines of new `showDecRat-chars-head-{dash,digit}` helpers in `DecRatParse/Properties.agda` (used to discharge `SuffixStops isHSpace` after a separator space).  CM_ adds chunk-reshape lemmas via `++ₗ-assoc` (needed because `emitComment-chars` emits `chunk ++ (' ' ∷ outer-tail)` while parser-side advances yield `(chunk ++ ' ' ∷ []) ++ outer-tail`) and `alt-fail-fail` / `alt-right-nothing` / `alt-left-just` chain composition for the 5-way dispatch.  The parse-and-drop trio (`VAL_` / `SIG_VALTYPE_` / `SG_MUL_VAL_`) needs no per-line roundtrip — composes for free at Layer 4 via `alt-left-just` short-circuit on the corresponding non-drop branch.

  * **Commits 3c / 3d pending** — 3c: attributes (BA_DEF_/BA_DEF_DEF_/BA_/BA_DEF_REL_/BA_DEF_DEF_REL_/BA_REL_/SIG_GROUP_).  3d: messages (BO_ + inner SG_ many).  Layer 4 then closes the universal `parseText (formatText d) ≡ inj₂ d` via aggregator induction over the `DBC` record.
- B.3.e Add JSON protocol command `{"command": "parse_dbc_text", "text": "..."}`.
- B.3.f Python: switch `parse_dbc` to Agda core. Keep the cantools path behind a single feature flag for the transition window.
- B.3.g Drop cantools dep once the corpus passes and a time-boxed grace window elapses with no regressions (see Risks §4). LGPL win per `project_lgpl_contingency.md`.
- B.3.h C++ `parse_dbc_text` API.
- B.3.i Go `ParseDBCText` API.
- B.3.j Cross-binding parity test: same DBC text → byte-identical `DbcDefinition` across all three.

**Estimate: 3–6 weeks of Agda work + proofs.** Driven primarily by the attribute subsystem and mux edge cases. The lower bound assumes clean real-world DBCs; the upper bound covers encoding quirks (signed value tables, bit-ordering subtleties, Motorola-endianness × mux).

**Matrix row:** `dbc_text_parse` (python=implemented/cpp,go=planned → all three=implemented after B.3.j).

### Phase C — Idiomatic Ergonomics (Part 2) — Design Rounds First

Every item below was proposed during R17 and **rejected** by the user ("The solutions will have to be discussed again — I do not like some of your proposals"). Each requires a fresh design round before code.

#### C.0 — Cancellation Contract SSOT (gated on its own review)

**Decision locked but subject to review:** does this doc exist at all, and if so what does it say?  Open questions before committing:
- Which operations support cancellation (long streams, big batches, live-bus loops)?
- What happens to partial work (rollback? return-what-you-have? commit-first-error?)?
- Is the contract identical across bindings, or does each idiom differ on partial-commit semantics?
- Does the contract need its own doc, or is a section in `docs/architecture/DESIGN.md` enough?

**Deliverable if approved:** `docs/architecture/CANCELLATION.md` — or rejection of the doc itself, with reasoning captured in memory.

#### C.1 + C.2 — Python `async` path + `send_frames_iter` (bundled)

Per `project_async_api_phase6.md`: both items share the Python streaming surface and their design decisions (chunking, cancellation, iterator-vs-async-iter contract) cannot be made coherently in isolation.

Open questions: sync generator first or native async? Shared `chunk_size` parameter? Cancellation via asyncio or generator `.close()`?

#### C.3 — Go `context.Context` on Client ops (R17-DEF-5)

Per `project_go_features_to_explore.md`. Open questions: per-method `...Context(ctx, ...)` overload, ctx-carrying `Client` variant, or both? How does ctx cancellation interact with `sync.Mutex` during an in-flight FFI call?

#### C.4 — C++ cancellation (new backlog item, surfaced by this plan)

Not in the R17 backlog but required for behavioral parity with C.1/C.3. `std::stop_token` is the obvious candidate. Design round required.

#### C.5 — Streaming iteration parity

Python has `iter_can_log` and a planned `send_frames_iter`. Does Go/C++ need a lazy variant for iteration over large traces, or is `SendFrames` / `send_frames_batch` (shipped) plus caller-side chunking enough? Part of C.1/C.2 design round.

### Phase D — Cross-Binding Doc Harness (R17-DEF-6)

Python shipped in R17 C6 via `pytest --markdown-docs`. C++/Go need equivalents.

- **D.1 C++** — catch2-based harness walking tracked markdown files, extracting fenced `cpp` blocks, synthesizing `#include` + `main()` wrappers, compiling with the project toolchain, running. Exclusion syntax: `<!-- cpp notest -->` above fence (mirrors the Python `notest` syntax).
- **D.2 Go** — test helper walking markdown, emitting `_test.go` wrappers, running `go test`. Simpler because `go run` exists and minimal boilerplate is needed.
- Both maintain a tracked-files list (same contract as R17 C6) and structurally ban undocumented `notest` escapes.
- Matrix row: `doc_example_gate_checks` (python=implemented, cpp/go=planned → implemented after D.1/D.2).

## Sequencing

```
Week 1:     Phase A (matrix + gates)         ──┐
                                                │
Week 1–2:   Phase B.1 → B.1.x (sequential)   ──┤
Week 2:     Phase B.2                        ──┤ parallel with B.1.x tail
                                                │
Week 2–3:   Phase D (doc harness C++/Go)     ──┤
                                                │
Week 2–6:   Phase B.3 (DBC parser)           ──┤ longest lead time
                                                │
Week 3+:    Phase C design rounds            ──┘
            (C.0 → C.1+C.2 → C.3 → C.4; implementation gated on user approval per round)
```

Calendar time is dominated by B.3 and Phase C review latency — both are acceptable because the alternative (skipping either) reintroduces the drift this plan exists to stop.

## Risks

1. **B.3 scope creep.** The cantools construct inventory may surface corner cases that push the upper bound past 6 weeks. Mitigation: the construct corpus in B.3.a is the hard boundary; anything outside it is documented as unsupported and deferred, not silently widened.
2. **Phase C review latency.** Four design rounds, each with user sign-off required. Weeks of calendar time for a few days of implementation. Acceptable because previous proposals were rejected — rushing is how we got here.
3. **Matrix gate becomes noise.** If the structural test fails for reasons unrelated to actual parity (e.g., an internal rename), it gets disabled. Mitigation: row `entry` fields must be public API, never internals; review each entry during the A.2 seed.
4. **Cantools fallback becomes permanent.** B.3.g drops the dep after a grace window. Time-box the window to 8 weeks from B.3.j; drop regardless after that and handle remaining issues as forward fixes. An indefinite "grace" becomes load-bearing by default.

## Out of Scope

- **LGPL hard-forced rewrite.** Tracked separately in `project_lgpl_contingency.md`. B.3 naturally resolves the cantools piece; this plan does not commit to the broader contingency (python-can, libgmp).
- **CLI parity for C++/Go.** `not_applicable` in the matrix with reason: "library bindings; CLI is a host-application concern."
- **FFI `unsafeCoerce` guard (R17-DEF-1).** Tracked separately in `project_ffi_unsafecoerce_guard.md`; not a parity concern.

## Related Memory

- `project_binding_feature_gaps.md` — R17-era feature gap snapshot (superseded by `FEATURE_MATRIX.yaml` after A.2 seed)
- `project_async_api_phase6.md` — Python streaming API evolution (drives C.1 + C.2)
- `project_go_features_to_explore.md` — Go backlog (C.3; mux helper merged into B.2)
- `project_ffi_unsafecoerce_guard.md` — explicit non-goal of this plan
- `project_lgpl_contingency.md` — adjacent concern, B.3 partially unblocks
- `feedback_cross_language_parity.md` — rationale for this plan's existence
- `feedback_defer_semantics.md` — these items are not Phase-6-gated; "right after R17"
