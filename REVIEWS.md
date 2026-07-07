# Review rounds — index

Human-readable index of the structured review archive at `.archive/reviews/r*/`.
Each round directory holds `round.yaml` + `findings/<id>.yaml` files.
Queryable via `tools/review_db.py` (see below).

## Rounds

| Round | Status | Forked | Merged | Raw findings | Closed | Critical (FIX) | High (FIX) |
|-------|--------|--------|--------|--------------|--------|----------------|------------|
| R20   | merged | 2026-05-12 | 2026-05-17 (`2477d5c`) | 671          | 88     | 1              | 22         |
| R21   | merged | 2026-05-17 | 2026-05-18 (`315c1a3`) | 241          | 48     | 0              | 17         |
| R22   | merged | 2026-05-18 | 2026-05-22 (`3ebfc37`) | 0 *          | 4      | 0              | 1          |
| R23   | merged | 2026-05-22 | 2026-05-26 (`4cb5220`) | 219          | 57     | 1              | 8          |
| R24   | merged | 2026-06-20 | 2026-06-21 (`551b033`) | 15           | 10     | 0              | 0          |
| R25   | merged | —          | 2026-07-07 (#80–164)   | 71 †         | ~65    | 0              | 1          |
| R26   | open   | 2026-07-07 | —                      | — ‡          | —      | —              | —          |

\* R22 is a carry-over round; no fresh Step-1/Step-2 agent fleet was launched.  Its work-to-date is exclusively closure of R21 carry-over items (AGDA-A-1.1 dead-import sweep #4, AGDA-D-12.1 end-of-stream warning emission, AGDA-D-15.1 `Format/AttrLine` split, Assign.agda b15 marker retirement) plus the review-process meta-review (this archive infrastructure).  R23 launched a fresh Step-1/Step-2 fleet on the new protocol.

† R25 was a two-round binding-review *program* over the Python / Go / C++ / Rust API surface (the first round to cover Rust), not a single fork→merge round.  It is archived as `FINAL_report.md` + `round{1,2}_findings.json` rather than per-finding YAML.  The 71 round-1 filings collapse to ~65 distinct defects; fixes shipped across PRs #80–164 (program closed 2026-07-07).  Severity was corrected by round 2 to 0 critical / 1 HIGH (the `never_exceeds` strict-inequality bug present consistently across all four bindings).

‡ R26 (this round) is the in-progress documentation overhaul; its finding counts finalize at close.

Earlier rounds (R6 — R19) are narrated in `memory/project_review_round{N}.md` and PROJECT_STATUS.md; their per-finding YAMLs were not retroactively backfilled — the per-finding YAML archive begins at R20 (R25 is the lone exception, archived in the pre-YAML JSON form noted above).

## Queries

```bash
# Round-by-round overview
tools/review_db.py --report round-summary

# The "0 critical stays 0 critical" invariant + cross-round high trend
tools/review_db.py --report critical-high-trend

# Per-category catch rate over time (which categories surface issues?)
tools/review_db.py --report category-trend

# Re-raise count (how many findings re-raise a closed predecessor?)
tools/review_db.py --report re-raise

# Disposition mix (FIX / FP / DEFER / DROP per round)
tools/review_db.py --report disposition-mix

# Graduation candidates (categories with zero real findings in last 2 rounds)
tools/review_db.py --report graduation

# Run every canned report
tools/review_db.py --report all

# Ad-hoc SQL
tools/review_db.py --query 'SELECT id, title FROM findings WHERE severity="critical"'
tools/review_db.py --schema    # dump the SQLite schema
```

## Schema

Per-finding YAML schema is in `.archive/reviews/schema.yaml` (JSON Schema in YAML form).
Validated automatically by `tools/review_db.py` on load.

Finding ID convention:

```
R<round>-<lang>-<agent>-<cat>.<num>
        |       |       |
        |       |       └── category number (1..N per AGENTS.md per-language section)
        |       └────────── A | B | C | D  (Step-1 hygiene / correctness / cross-file / Step-2 system-level)
        └────────────────── AGDA | GO | CPP | PY | RUST | DOCS | CICD | XBINDING
```

Examples: `R20-AGDA-A-1.1` · `R21-CPP-D-15.3` · `R22-PY-B-26.2`.

A re-raise of a closed finding from an earlier round uses a NEW id in the current round and points back via the `re_raised_from` field.

## Lifecycle

See `memory/feedback_review_branch_workflow.md` for the per-round lifecycle.  Headline: the working `review-r<N>-findings.md` is round-scope draft state; per-finding YAMLs are the durable cross-round record.  Round metadata at `round.yaml` records fork point, merge commit, agent fleet, finding counts.

## Graduated categories

See `memory/feedback_graduated_categories.md`.  Graduated categories are no longer reviewed by agents; mechanical gates enforce their semantic surface continuously.  Cat 1 (Dead code) graduated at R22 close; post-R23 its gate is the single scope-aware `.agdai` IWYU tool (`tools/iwyu.py`, run_ci step 9 + its `--self-test` at step 10), which replaced the recompile/regex dead-import tools.
