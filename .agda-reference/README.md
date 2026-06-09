<!-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier -->
<!-- SPDX-License-Identifier: BSD-2-Clause -->

# Agda grammar reference (for the dead-import / IWYU tooling)

`Parser.y` in this directory is a **local, gitignored** copy of Agda's concrete
grammar. It is the source of truth for `tools/_agda_opens.py` (which forms must
be detected/classified) and for the grammar-coverage test harness
`python/tests/test_agda_open_grammar.py`. The file itself is not committed (it is
external, BSD-2-Clause code); this README is the durable provenance so it can be
re-fetched if wiped.

- **Source:** <https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Syntax/Parser/Parser.y>
- **Pinned tag:** `v2.8.0` — matches the Agda the build uses
  (`~/.cabal/store/ghc-9.6.7/Agda-2.8.0-…`).
- **License:** BSD-2-Clause (Agda's; compatible with this project's license).

Re-fetch:

```bash
curl -fsSL \
  "https://raw.githubusercontent.com/agda/agda/v2.8.0/src/full/Agda/Syntax/Parser/Parser.y" \
  -o .agda-reference/Parser.y
```

The import/open productions that matter for the tooling live around lines
1060–1097 (`ImportDirective` / `Using` / `Hiding` / `RenamingDir` / `Renaming` /
`RenamingTarget`) and 1454–1545 (`Open` / `OpenArgs` / `ModuleApplication`), plus
`ModuleName : QId` (line 504). The distilled facts are recorded in
`memory/project_agda_iwyu.md`.
