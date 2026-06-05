# agda-iwyu-reader — fixture validation harness

The reader's verdict logic (the IMPURE used-set + scope resolution half of the
IWYU tool) is validated against **synthetic Agda fixtures with verdicts known by
construction** — never against the live project tree, which a contributor can
rewrite at any time. This mirrors the validation split: the PURE finding-logic
(parsing `open` statements) is validated by the grammar harness
(`python/tests/test_agda_open_grammar*.py`); the reader's resolution is validated
here.

## Files

- `fixtures/*.agda` — self-contained synthetic modules (no stdlib dependency),
  each isolating one scope/resolution phenomenon.
- `manifest.tsv` — `consumer ⇥ module ⇥ name ⇥ expected` rows; `expected` ∈
  `{USED, DEAD, UNRESOLVED}`. For a renamed import the manifest passes the
  ORIGINAL name (the elaborated term references the origin, never the alias).
- `wildcard_manifest.tsv` — `consumer ⇥ module ⇥ used,comma,sep` rows; the
  expected USED subset of a wildcard `open import module` (the reader query
  `module *`), which narrowing/redundancy is judged from: empty → DEAD wildcard;
  ⊆ the explicit imports → REDUNDANT; else NARROWABLE to `using (used)`. Covers
  `ConsumerWild{Narrow,Redundant,Dead}` and `ConsumerWildInferred` (an instance
  used only via instance search — caught by `namesIn`, missed by body-token
  tools).

## What the matrix covers (and why each is an FN-risk)

| consumer(s) | phenomenon | verdict |
|---|---|---|
| `ConsumerUsed`/`ConsumerDead` `Mid idO` | re-export value (`open M public`) | USED / DEAD |
| `ConsumerUsed`/`ConsumerDead` `Mid InstR` | module-application **Function copy** (≡-Reasoning-like) — copy delegates to origin | USED / DEAD |
| `ConsumerDeadMod`/`ConsumerUsedMod` `Mid2 InstR2` | copy whose **type references a used QName** but copy itself unused — the blanket-`namesIn` false-"used" trap | DEAD / USED |
| `ConsumerChain*` `MidC2 InstC2` | **chained** re-export (`open InstC1 public`) — defining iface auto-derived from the copy's own module, not the queried one | USED / DEAD |
| `ConsumerDT*` `MidDT InstD` | **datatype/constructor copy** — consumer term keeps the copy QName, so direct match | USED / DEAD |
| `ConsumerPriv*` `LibP privF` | **private** import — resolved via the SOURCE module's scope, immune to consumer `withoutPrivates` | USED / DEAD |
| `ConsumerRename*` `Origin idO` | **renaming** — query the original name | USED / DEAD |
| `ConsumerOpUsed` `OpMod _⊕_`/`_⊗_` | **operator / mixfix** | USED / DEAD |
| `ConsumerInstUsed` `InstLib defI` | **instance / inferred use** (no body token; `namesIn` captures it) | USED |
| `ConsumerPat*` `PatLib two` | **pattern synonym** (expands to constructors, so absent from `sigDefinitions`; caught by the syntactic occurrence-count from `iHighlighting`) | USED / DEAD |
| `ConsumerAbs*` `AbsMid InstAb` | **abstract** Function copy | USED / DEAD |
| `ConsumerRecUsed` `RecLib fstP` | **record projection** | USED |
| `ConsumerAliasDup` `Origin idO` | **aliased duplicate** (same origin under two names, one used) — over-keep is the safe direction | USED |
| `ConsumerI*` `MidI InstI` | **module-application instance copy used via instance search** (no body token; origin in `used`) — the case that exercises the *delegated* signal | USED / DEAD |

The reader decides a candidate by the union of three signals, all read from the
`.agdai`:

1. **semantic** — its canonical QName is in `namesIn(iSignature)` (the
   elaborated terms; captures inferred / implicit / literal-backed uses);
2. **syntactic** — its definition site is referenced by a source token, counted
   from `iHighlighting`. An import-listed name always contributes one occurrence
   (the `using (...)` token), so a *value* needs count ≥ 2 to be a body use; a
   *module member* is not in the import list, so any occurrence (≥ 1) is a use.
   This is what catches pattern synonyms, which elaboration erases;
3. **delegated** — a module-application Function copy whose delegated origin
   reaches the used-set.

**FN-safety property** (the bar): no *used*-case ever resolves to DEAD — every
real use mechanism is covered by one of the three signals, so DEAD means "none
fired". UNRESOLVED is reserved for a candidate that cannot be resolved in scope
at all (which should not happen for a real candidate); the driver routes it to
the recompile-confirm oracle, never to DEAD.

## Running the validation

```bash
python -m tools.iwyu_fixture_test
# -> === iwyu-reader fixtures: 25/25 pass ===   (exit 0; 1 on any mismatch)
```

The runner type-checks every fixture in a scratch dir (agda runs FROM that dir
so its no-`.agda-lib` project root is the cwd — else a leaf module fails
`ModuleNameDoesntMatchFileName`), builds the reader against the cabal-store Agda,
runs it over every `manifest.tsv` query, and asserts each verdict — including the
true-positive DEAD cases (a `using`-listed name that is never used). This is the
synthetic, construction-known test of the reader's verdict logic; it does not
read the live tree.

Separately, `python -m tools.iwyu_reader --validate (--all | FILE.agda …)` runs
the reader against the recompile-confirm **oracle** on real modules, to catch any
false negative (reader DEAD yet removal fails) the synthetic matrix missed.
