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

## Running the validation (manual, until the runner lands)

```bash
# 1. type-check the fixtures in a scratch dir (they need no stdlib).
#    Run agda FROM the scratch dir: with no .agda-lib, agda derives the project
#    root from the cwd, so a leaf module `Origin` must be reached as `Origin.agda`
#    relative to cwd (else ModuleNameDoesntMatchFileName).
mkdir -p /tmp/iwyu-fx && cp fixtures/*.agda /tmp/iwyu-fx/
( cd /tmp/iwyu-fx && for f in *.agda; do
    /home/nicolas/.cabal/bin/agda +RTS -N4 -M4G -RTS --safe --without-K "$f"; done )

# 2. build the reader (links the prebuilt Agda from the cabal store)
ghc -package-db ~/.cabal/store/ghc-$(ghc --numeric-version)/package.db \
    -package Agda -package containers -package unordered-containers \
    -outputdir /tmp/iwyu-build ../Main.hs -o /tmp/iwyu-reader

# 3. feed queries (consumer.agdai ⇥ module ⇥ name) and compare to manifest
AGDA_IWYU_INCLUDE_PATHS=/tmp/iwyu-fx /tmp/iwyu-reader <<EOF
/tmp/iwyu-fx/ConsumerDeadMod.agdai	Mid2	InstR2
EOF
# -> {"path":...,"mod":"Mid2","name":"InstR2","verdict":"DEAD"}
```

The whole matrix passes (23/23). A scripted runner that does steps 1–3 over
`manifest.tsv` and asserts the verdicts is the next addition.
