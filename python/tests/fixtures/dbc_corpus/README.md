# B.3 DBC Text Parser Corpus

This directory holds the regression corpus for the Phase B.3 Agda DBC text
parser (`docs/development/PARITY_PLAN.md` §B.3). Every B.3 construct
inventory row is exercised by at least one corpus file.

Two snapshot trees live here, each a separate gate:

- `snapshots/` — cantools-baseline regression for `dbc_to_json(parser="cantools")`.
  Insertion order (no `sort_keys`); rational fields share the same
  "emit int when denominator=1" rule as `parity_snapshots/` (B.3.f
  canonicalised `FractionJSONEncoder` to match Agda's `formatRational`).
  Driven by `test_dbc_corpus_baseline.py`. Slated for removal alongside the
  cantools fallback in B.3.g.
- `parity_snapshots/` — B.3.j cross-binding parity oracle for the
  Agda-backed `parse_dbc_text` (shipped in B.3.e). Sorted keys, "emit int
  when denominator=1" rule, `presence: always` always explicit, `extended`
  omitted on standard CAN frames. The Python (`test_dbc_corpus_parity.py`),
  C++ (`cpp/tests/dbc_corpus_parity_tests.cpp`), and Go
  (`go/aletheia/dbc_corpus_parity_test.go`) parity tests all assert
  byte-equality against the same files.

The two trees differ only on `sort_keys` (parity sorts, baseline preserves
insertion order). Each gate is loud about its own concern: cantools
regressions vs cross-binding DbcDefinition drift. The Agda parser
correctness itself is not under test in either gate — that is established
by the universal roundtrip theorem in
`Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda` (B.3.d).

## Coverage map

| File | B.3 inventory rows exercised |
|---|---|
| `minimal.dbc` | `VERSION`, `NS_`, `BS_`, `BU_`, `BO_`, `SG_`, start bit, length, byte order (Intel `@1` + Motorola `@0`), signedness (`+`/`-`), factor, offset, min/max, unit, receivers (list / single / empty), sender, DLC |
| `multiplexing.dbc` | mux indicator (`M`, `m<n>`), nested mux (`m0M`), `SG_MUL_VAL_` (single range + multi-range) |
| `value_tables.dbc` | `VAL_` (signal-scoped), `VAL_TABLE_` (global) |
| `attributes.dbc` | `BA_DEF_` × 5 types (INT/FLOAT/STRING/ENUM/HEX), `BA_DEF_DEF_`, `BA_`, `BA_DEF_REL_` (BU_BO_REL_ + BU_SG_REL_), `BA_REL_`, attribute scopes ×7 (network/node/message/signal/envVar/nodeMsg/nodeSig) |
| `comments_groups.dbc` | `CM_` × 5 scopes (network/node/message/signal/envVar), `SIG_GROUP_`, `SIG_VALTYPE_` (float32 + float64 — see "known divergences") |
| `env_vars.dbc` | `EV_` × 3 varTypes (int/float/string), `EV_DATA_` / `ENVVAR_DATA_` declared in `NS_` (see "known divergences") |
| `extended_can.dbc` | extended CAN ID (bit 31), CAN-FD flag (via `BA_ "VFrameFormat"` attribute, standard + extended variants) |
| `kitchen_sink.dbc` | cross-construct stress test combining all rows above in a single DBC |

## Snapshot refresh policy

Snapshots in both trees are compared byte-for-byte. The tests fail closed
when output drifts.

**When to regenerate `snapshots/` (cantools baseline):**
- A corpus `.dbc` is intentionally edited or added.
- The `dbc_to_json` wire shape changes (B.1.x-style widening).

```bash
cd python && ALETHEIA_UPDATE_SNAPSHOTS=1 python3 -m pytest \
  tests/test_dbc_corpus_baseline.py::test_corpus_matches_cantools_snapshot
```

**When to regenerate `parity_snapshots/` (Agda-backed cross-binding oracle):**
- A corpus `.dbc` is intentionally edited or added.
- Agda's wire shape for the parsed DBC body changes (rare — would touch
  `Aletheia/Protocol/ResponseFormat.agda` or `formatDBC` paths).

```bash
cd python && ALETHEIA_UPDATE_SNAPSHOTS=1 python3 -m pytest \
  tests/test_dbc_corpus_parity.py::test_corpus_parses_to_parity_snapshot
```

## Known divergences from the B.3 construct inventory

Two rows in the B.3 inventory are *in the DBC* but not yet reflected in
`dbc_to_json` output. They are kept in the corpus so the Agda parser has
coverage when these rows get wired:

- **`SIG_VALTYPE_`** — `comments_groups.dbc` declares float32/float64 via
  `SIG_VALTYPE_ <msg_id> <sig> : 1;` (or `: 2;`). The current
  `dbc_converter` doesn't emit the float-width into `DBCSignal`. B.3.e
  scope: decide whether to surface this as a `DBCSignal` field or leave
  encoding implicit in `factor`/`length`.
- **`EV_DATA_` / `ENVVAR_DATA_`** — declared in `NS_` (keyword support)
  but never emitted as statements; cantools' grammar doesn't accept them
  as statements either. If a real-world DBC ever uses them as statements,
  both our parser and cantools will fail the same way.

One observed cantools normalization (in `dbc_to_json`):

- **Empty `VERSION ""` → `"1.0"`** — `dbc_to_json` substitutes `"1.0"`
  when `db.version` is empty. The Agda parser must mirror this on the
  wire-shape path (applied post-parse, not during tokenization), or the
  snapshot gate will fail after switchover.

## License

Hand-authored by the aletheia project. BSD-2-Clause (matches the repo
license). No redistribution of third-party DBCs — the corpus is designed
for coverage precision, not realism. Real-world robustness is handled by
the same mechanism: adding new `.dbc` files to this directory and
rerunning snapshot generation.
