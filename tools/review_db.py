#!/usr/bin/env python3
"""tools/review_db.py -- Review findings database (R22 review-process meta-review).

Loads structured YAML findings under .archive/reviews/r*/ into an in-memory
SQLite database, then runs canned reports answering the three questions
that motivated the formalisation:

  1. Which categories catch issues?       --report category-trend
  2. How many issues are re-raised?       --report re-raise
  3. Does review scope decrease over time?  --report severity-trend
                                          --report graduation

The SQLite DB is REGENERABLE -- YAML is canonical, the DB is built on
demand and held in memory.  No binary state in the repo.  Same pattern
as ctags / sphinx-search.

═══ FILE LAYOUT (canonical YAML) ═══

  .archive/reviews/
    schema.yaml                # JSON Schema (in YAML form) for findings + rounds
    r20/
      round.yaml               # round metadata (id, fork, merge, fleet, ...)
      findings/
        AGDA-A-1.1.yaml        # one file per closed finding
        AGDA-D-11.2.yaml
        ...
    r21/
      round.yaml
      findings/...
    r22/
      round.yaml
      findings/...

═══ CANNED REPORTS ═══

  category-trend  : count of findings per category per round (which
                    categories catch issues? are they slowing down?).
  re-raise        : count of findings re-raising prior closures, broken
                    down by predecessor round.
  severity-trend  : count of findings per severity per round (the
                    "critical/high inventory" check -- spikes flag
                    regressions; flat-zero confirms scope decrease).
  disposition-mix : per-round disposition distribution (FIX / FP / DEFER
                    / DROP) -- FP rate trending up is the scanner-limit
                    signal we hit in R22 A-1.1 b25 series.
  graduation      : categories with zero real findings in the most-recent
                    N rounds (default 2).  These are graduation candidates
                    per AGENTS.md.
  round-summary   : per-round one-line summary (raw → closed counts +
                    cluster count + merge commit).

Each report is also available as --json for piping into other tooling.

═══ AD-HOC QUERIES ═══

  tools/review_db.py --query 'SELECT * FROM findings WHERE severity="critical"'
  tools/review_db.py --schema    # dump the SQLite schema and exit

Schema (kept tight; mirrors .archive/reviews/schema.yaml $defs):

  rounds(id PK, fork_point, fork_date, merge_commit, merge_date,
         status, raw_findings_count, closed_findings_count, notes)
  findings(id PK, round, category_number, category_name, category_language,
           category_agent, severity, disposition, status, title, description,
           cluster, resolution_commit, resolution_round, resolution_date,
           resolution_notes, re_raised_from, in_source_marker)
  finding_files(finding_id, path)        -- many-to-many: 1 finding -> N files
  finding_tags(finding_id, tag)

═══ INTEGRATION ═══

Read-only.  Does NOT modify the YAML corpus.  Safe to call from any
shell, hook, CI step.  Carry-over (AGENTS.md Step 0) reads the YAML
directly; review_db.py is for analytics, not workflow state.

References:
  * memory/feedback_review_branch_workflow.md  (archive lifecycle)
  * AGENTS.md § Graduation                     (criterion + queryable)
  * REVIEWS.md                                 (human-readable index)
"""

from __future__ import annotations

import argparse
import json
import re
import sqlite3
import sys
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError:
    sys.stderr.write(
        "tools/review_db.py: PyYAML is required.  Install via "
        "`python/.venv/bin/pip install pyyaml` or use the project venv.\n"
    )
    sys.exit(2)


# ─────────────────────────── repo discovery ──────────────────────────────

def find_repo_root(start: Path) -> Path:
    """Walk up from *start* until aletheia.agda-lib is found."""
    cur = start.resolve()
    while cur != cur.parent:
        if (cur / "aletheia.agda-lib").is_file():
            return cur
        cur = cur.parent
    raise SystemExit(
        "tools/review_db.py: cannot find repo root (aletheia.agda-lib not found in ancestors)"
    )


# ─────────────────────────── schema validation ───────────────────────────

_FINDING_ID_RE = re.compile(r"^R[0-9]+-[A-Z]+-[A-Z]-[0-9]+\.[0-9]+$")
_ROUND_ID_RE = re.compile(r"^R[0-9]+$")
_SHA_RE = re.compile(r"^[0-9a-f]{7,40}$")
_DATE_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}$")

_VALID_LANGUAGES = {"agda", "go", "cpp", "python", "docs", "cicd", "xbinding"}
_VALID_AGENTS = {"A", "B", "C", "D"}
_VALID_SEVERITIES = {"critical", "high", "medium", "low", "info"}
_VALID_DISPOSITIONS = {"FIX", "FIX-PARTIAL", "DEFER", "NO-FIX", "FP", "FP-VERIFIED", "DROP"}
_VALID_STATUSES = {"open", "in_progress", "closed"}
_VALID_ROUND_STATUSES = {"open", "merged", "abandoned"}


def _check(cond: bool, where: str, msg: str) -> None:
    if not cond:
        raise SystemExit(f"tools/review_db.py: schema error in {where}: {msg}")


def validate_finding(d: dict[str, Any], path: Path) -> None:
    where = str(path)
    _check(isinstance(d, dict), where, "top-level must be a mapping")
    for k in ("id", "round", "category", "severity", "disposition", "status", "title"):
        _check(k in d, where, f"missing required key: {k}")
    _check(bool(_FINDING_ID_RE.match(d["id"])), where, f"id {d['id']!r} not <ROUND>-<LANG>-<AGENT>-<CAT>.<NUM>")
    _check(bool(_ROUND_ID_RE.match(d["round"])), where, f"round {d['round']!r} not R<n>")
    cat = d["category"]
    _check(isinstance(cat, dict), where, "category must be a mapping")
    for k in ("number", "name", "language", "agent"):
        _check(k in cat, where, f"category missing {k}")
    _check(isinstance(cat["number"], int) and cat["number"] >= 1, where, "category.number must be a positive int")
    _check(cat["language"] in _VALID_LANGUAGES, where, f"category.language {cat['language']!r} invalid")
    _check(cat["agent"] in _VALID_AGENTS, where, f"category.agent {cat['agent']!r} invalid")
    _check(d["severity"] in _VALID_SEVERITIES, where, f"severity {d['severity']!r} invalid")
    _check(d["disposition"] in _VALID_DISPOSITIONS, where, f"disposition {d['disposition']!r} invalid")
    _check(d["status"] in _VALID_STATUSES, where, f"status {d['status']!r} invalid")
    if "resolution" in d and d["resolution"] is not None:
        r = d["resolution"]
        _check(isinstance(r, dict), where, "resolution must be a mapping")
        if "commit" in r:
            _check(bool(_SHA_RE.match(r["commit"])), where, f"resolution.commit {r['commit']!r} not a SHA")
        if "round" in r:
            _check(bool(_ROUND_ID_RE.match(r["round"])), where, f"resolution.round {r['round']!r} invalid")
        if "date" in r:
            _check(bool(_DATE_RE.match(r["date"])), where, f"resolution.date {r['date']!r} not YYYY-MM-DD")
    if "re_raised_from" in d and d["re_raised_from"]:
        _check(bool(_FINDING_ID_RE.match(d["re_raised_from"])), where,
               f"re_raised_from {d['re_raised_from']!r} not a finding id")


def validate_round(d: dict[str, Any], path: Path) -> None:
    where = str(path)
    _check(isinstance(d, dict), where, "top-level must be a mapping")
    for k in ("id", "fork_point", "fork_date", "status"):
        _check(k in d, where, f"missing required key: {k}")
    _check(bool(_ROUND_ID_RE.match(d["id"])), where, f"id {d['id']!r} not R<n>")
    _check(bool(_SHA_RE.match(d["fork_point"])), where, f"fork_point {d['fork_point']!r} not a SHA")
    _check(bool(_DATE_RE.match(d["fork_date"])), where, f"fork_date {d['fork_date']!r} not YYYY-MM-DD")
    _check(d["status"] in _VALID_ROUND_STATUSES, where, f"status {d['status']!r} invalid")
    if d.get("merge_commit"):
        _check(bool(_SHA_RE.match(d["merge_commit"])), where, f"merge_commit {d['merge_commit']!r} not a SHA")
    if d.get("merge_date"):
        _check(bool(_DATE_RE.match(d["merge_date"])), where, f"merge_date {d['merge_date']!r} not YYYY-MM-DD")


# ─────────────────────────── load + build DB ─────────────────────────────

_SCHEMA_SQL = """
CREATE TABLE rounds (
    id                     TEXT PRIMARY KEY,
    fork_point             TEXT NOT NULL,
    fork_date              TEXT NOT NULL,
    merge_commit           TEXT,
    merge_date             TEXT,
    status                 TEXT NOT NULL,
    raw_findings_count     INTEGER,
    closed_findings_count  INTEGER,
    notes                  TEXT
);

CREATE TABLE findings (
    id                  TEXT PRIMARY KEY,
    round               TEXT NOT NULL REFERENCES rounds(id),
    category_number     INTEGER NOT NULL,
    category_name       TEXT NOT NULL,
    category_language   TEXT NOT NULL,
    category_agent      TEXT NOT NULL,
    severity            TEXT NOT NULL,
    disposition         TEXT NOT NULL,
    status              TEXT NOT NULL,
    title               TEXT NOT NULL,
    description         TEXT,
    cluster             TEXT,
    resolution_commit   TEXT,
    resolution_round    TEXT,
    resolution_date     TEXT,
    resolution_notes    TEXT,
    re_raised_from      TEXT,
    in_source_marker    TEXT
);

CREATE TABLE finding_files (
    finding_id  TEXT NOT NULL REFERENCES findings(id),
    path        TEXT NOT NULL,
    PRIMARY KEY (finding_id, path)
);

CREATE TABLE finding_tags (
    finding_id  TEXT NOT NULL REFERENCES findings(id),
    tag         TEXT NOT NULL,
    PRIMARY KEY (finding_id, tag)
);

CREATE INDEX idx_findings_round         ON findings(round);
CREATE INDEX idx_findings_category      ON findings(category_language, category_number);
CREATE INDEX idx_findings_severity      ON findings(severity);
CREATE INDEX idx_findings_disposition   ON findings(disposition);
CREATE INDEX idx_findings_re_raised     ON findings(re_raised_from);
"""


def build_db(repo_root: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(":memory:")
    conn.executescript(_SCHEMA_SQL)
    archive = repo_root / ".archive" / "reviews"
    if not archive.is_dir():
        raise SystemExit(f"tools/review_db.py: archive directory {archive} not found")

    round_dirs = sorted(p for p in archive.iterdir() if p.is_dir() and p.name.startswith("r"))
    for rd in round_dirs:
        rfile = rd / "round.yaml"
        if not rfile.is_file():
            sys.stderr.write(f"tools/review_db.py: warning: {rd} missing round.yaml -- skipping\n")
            continue
        with rfile.open() as f:
            r = yaml.safe_load(f)
        validate_round(r, rfile)
        conn.execute(
            "INSERT INTO rounds VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                r["id"],
                r["fork_point"],
                r["fork_date"],
                r.get("merge_commit"),
                r.get("merge_date"),
                r["status"],
                r.get("raw_findings_count"),
                r.get("closed_findings_count"),
                r.get("notes"),
            ),
        )

        findings_dir = rd / "findings"
        if findings_dir.is_dir():
            for ff in sorted(findings_dir.glob("*.yaml")):
                with ff.open() as f:
                    d = yaml.safe_load(f)
                validate_finding(d, ff)
                cat = d["category"]
                res = d.get("resolution") or {}
                conn.execute(
                    """INSERT INTO findings VALUES
                       (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                    (
                        d["id"],
                        d["round"],
                        cat["number"],
                        cat["name"],
                        cat["language"],
                        cat["agent"],
                        d["severity"],
                        d["disposition"],
                        d["status"],
                        d["title"],
                        d.get("description"),
                        d.get("cluster"),
                        res.get("commit"),
                        res.get("round"),
                        res.get("date"),
                        res.get("notes"),
                        d.get("re_raised_from"),
                        d.get("in_source_marker"),
                    ),
                )
                for p in d.get("files") or []:
                    conn.execute("INSERT INTO finding_files VALUES (?, ?)", (d["id"], p))
                for t in d.get("tags") or []:
                    conn.execute("INSERT INTO finding_tags VALUES (?, ?)", (d["id"], t))

    conn.commit()
    return conn


# ─────────────────────────── canned reports ──────────────────────────────

def _print_table(rows: list[tuple], headers: list[str]) -> None:
    if not rows:
        print("(no rows)")
        return
    cols = list(zip(*([tuple(headers)] + [tuple(str(c) if c is not None else "" for c in r) for r in rows])))
    widths = [max(len(c) for c in col) for col in cols]
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    print(fmt.format(*headers))
    print(fmt.format(*("-" * w for w in widths)))
    for r in rows:
        print(fmt.format(*(str(c) if c is not None else "" for c in r)))


def report_category_trend(conn: sqlite3.Connection) -> tuple[list, list]:
    """Count of closed findings per (language, category_number) per round.

    Pivoted: one row per (language, category, name), columns = rounds.
    """
    cur = conn.cursor()
    rounds = [r[0] for r in cur.execute("SELECT id FROM rounds ORDER BY id").fetchall()]
    rows = cur.execute(
        """SELECT category_language, category_number, category_name, round, COUNT(*)
           FROM findings
           GROUP BY category_language, category_number, category_name, round
           ORDER BY category_language, category_number"""
    ).fetchall()
    pivot: dict[tuple[str, int, str], dict[str, int]] = {}
    for lang, num, name, rnd, cnt in rows:
        pivot.setdefault((lang, num, name), {})[rnd] = cnt
    headers = ["lang", "cat", "name", *rounds]
    out_rows = [
        (lang, num, name, *(pivot[(lang, num, name)].get(r, 0) for r in rounds))
        for (lang, num, name) in sorted(pivot.keys())
    ]
    return out_rows, headers


def report_re_raise(conn: sqlite3.Connection) -> tuple[list, list]:
    """For each round, count of findings that re-raise a prior closure,
    broken down by predecessor round."""
    cur = conn.cursor()
    rows = cur.execute(
        """SELECT f.round AS this_round,
                  SUBSTR(f.re_raised_from, 1, INSTR(f.re_raised_from, '-') - 1) AS predecessor_round,
                  COUNT(*)
           FROM findings f
           WHERE f.re_raised_from IS NOT NULL
           GROUP BY this_round, predecessor_round
           ORDER BY this_round, predecessor_round"""
    ).fetchall()
    return rows, ["round", "re-raised from", "count"]


def report_severity_trend(conn: sqlite3.Connection) -> tuple[list, list]:
    """Per-round severity distribution.  Critical/high are the key
    scope-decrease signal: should stay at 0 after they have been driven
    down."""
    cur = conn.cursor()
    rounds = [r[0] for r in cur.execute("SELECT id FROM rounds ORDER BY id").fetchall()]
    severities = ["critical", "high", "medium", "low", "info"]
    grid: dict[str, dict[str, int]] = {sev: {r: 0 for r in rounds} for sev in severities}
    for sev, rnd, cnt in cur.execute(
        "SELECT severity, round, COUNT(*) FROM findings GROUP BY severity, round"
    ).fetchall():
        grid[sev][rnd] = cnt
    headers = ["severity", *rounds]
    out_rows = [(sev, *(grid[sev][r] for r in rounds)) for sev in severities]
    return out_rows, headers


def report_disposition_mix(conn: sqlite3.Connection) -> tuple[list, list]:
    """Per-round disposition distribution.  FP rate climbing is the
    scanner-limit / agent-saturation signal."""
    cur = conn.cursor()
    rounds = [r[0] for r in cur.execute("SELECT id FROM rounds ORDER BY id").fetchall()]
    dispositions = sorted(_VALID_DISPOSITIONS)
    grid: dict[str, dict[str, int]] = {d: {r: 0 for r in rounds} for d in dispositions}
    for disp, rnd, cnt in cur.execute(
        "SELECT disposition, round, COUNT(*) FROM findings GROUP BY disposition, round"
    ).fetchall():
        grid[disp][rnd] = cnt
    headers = ["disposition", *rounds]
    out_rows = [(disp, *(grid[disp][r] for r in rounds)) for disp in dispositions]
    return out_rows, headers


def report_graduation(conn: sqlite3.Connection, n_rounds: int = 2) -> tuple[list, list]:
    """Categories with zero real findings in the most-recent *n_rounds* rounds
    AND that have been active in earlier rounds (i.e. had a real finding ever).

    A category that goes N rounds with no real findings (FIX/FIX-PARTIAL/NO-FIX
    closures imply a real issue was caught) after having had real findings
    earlier is a graduation candidate per AGENTS.md."""
    cur = conn.cursor()
    rounds = [r[0] for r in cur.execute("SELECT id FROM rounds ORDER BY id").fetchall()]
    recent = rounds[-n_rounds:] if len(rounds) >= n_rounds else rounds
    if not recent:
        return [], ["lang", "cat", "name", f"real (last {n_rounds})", "real (history)"]
    ph = ",".join("?" for _ in recent)
    rows = cur.execute(
        f"""SELECT category_language,
                   category_number,
                   MIN(category_name) AS name,
                   SUM(CASE WHEN disposition IN ('FIX','FIX-PARTIAL','NO-FIX')
                            AND round IN ({ph}) THEN 1 ELSE 0 END) AS real_recent,
                   SUM(CASE WHEN disposition IN ('FIX','FIX-PARTIAL','NO-FIX')
                            AND round NOT IN ({ph}) THEN 1 ELSE 0 END) AS real_earlier,
                   SUM(CASE WHEN round IN ({ph}) THEN 1 ELSE 0 END) AS any_recent
           FROM findings
           GROUP BY category_language, category_number
           HAVING real_recent = 0 AND real_earlier > 0
           ORDER BY real_earlier DESC, category_language, category_number""",
        (*recent, *recent, *recent),
    ).fetchall()
    headers = ["lang", "cat", "name", f"real (last {n_rounds})",
               "real (earlier rounds)", f"any disposition (last {n_rounds})"]
    return rows, headers


def report_round_summary(conn: sqlite3.Connection) -> tuple[list, list]:
    cur = conn.cursor()
    rows = cur.execute(
        """SELECT r.id, r.status, r.fork_date, r.merge_date, r.raw_findings_count,
                  r.closed_findings_count, COUNT(f.id), r.merge_commit
           FROM rounds r LEFT JOIN findings f ON f.round = r.id
           GROUP BY r.id
           ORDER BY r.id"""
    ).fetchall()
    return rows, ["round", "status", "forked", "merged", "raw", "closed (decl)", "closed (in DB)", "merge SHA"]


def report_critical_high_trend(conn: sqlite3.Connection) -> tuple[list, list]:
    """The 'should-stay-zero' invariant check: per-round count of critical
    + high severity findings (FIX/FIX-PARTIAL closures), and whether each
    round HONOURED the invariant of not regressing from a prior zero."""
    cur = conn.cursor()
    rows = cur.execute(
        """SELECT round,
                  SUM(CASE WHEN severity='critical'
                           AND disposition IN ('FIX','FIX-PARTIAL') THEN 1 ELSE 0 END) AS critical,
                  SUM(CASE WHEN severity='high'
                           AND disposition IN ('FIX','FIX-PARTIAL') THEN 1 ELSE 0 END) AS high,
                  SUM(CASE WHEN severity IN ('critical','high')
                           AND re_raised_from IS NOT NULL THEN 1 ELSE 0 END) AS regression_re_raises
           FROM findings
           GROUP BY round
           ORDER BY round"""
    ).fetchall()
    out: list = []
    prev_crit: int | None = None
    prev_high: int | None = None
    for rnd, crit, high, regr in rows:
        flag = ""
        if prev_crit == 0 and crit > 0:
            flag = "CRITICAL-REGRESSED"
        elif prev_high == 0 and high > 0:
            flag = "HIGH-REGRESSED"
        out.append((rnd, crit, high, regr, flag))
        prev_crit, prev_high = crit, high
    return out, ["round", "critical (FIX)", "high (FIX)", "C/H re-raises", "regression flag"]


REPORTS: dict[str, Any] = {
    "category-trend": report_category_trend,
    "re-raise": report_re_raise,
    "severity-trend": report_severity_trend,
    "critical-high-trend": report_critical_high_trend,
    "disposition-mix": report_disposition_mix,
    "graduation": report_graduation,
    "round-summary": report_round_summary,
}


# ─────────────────────────── cli ─────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(
        prog="tools/review_db.py",
        description="Review findings analytics over .archive/reviews/r*/",
    )
    ap.add_argument("--report", choices=sorted(REPORTS.keys()) + ["all"],
                    help="Run a canned report.")
    ap.add_argument("--query", metavar="SQL",
                    help="Run an ad-hoc SQL query against the DB and print rows.")
    ap.add_argument("--schema", action="store_true",
                    help="Print the SQLite schema and exit.")
    ap.add_argument("--json", action="store_true",
                    help="Emit report output as JSON instead of a table.")
    ap.add_argument("--graduation-rounds", type=int, default=2,
                    help="Window size for --report graduation (default 2).")
    args = ap.parse_args()

    if args.schema:
        print(_SCHEMA_SQL.strip())
        return 0

    repo_root = find_repo_root(Path(__file__).parent)
    conn = build_db(repo_root)

    if args.query:
        cur = conn.execute(args.query)
        headers = [d[0] for d in (cur.description or [])]
        rows = cur.fetchall()
        if args.json:
            print(json.dumps([dict(zip(headers, r)) for r in rows], indent=2, default=str))
        else:
            _print_table(rows, headers)
        return 0

    if not args.report:
        ap.print_help()
        return 0

    reports_to_run = sorted(REPORTS.keys()) if args.report == "all" else [args.report]
    for name in reports_to_run:
        fn = REPORTS[name]
        if name == "graduation":
            rows, headers = fn(conn, args.graduation_rounds)
        else:
            rows, headers = fn(conn)
        if args.json:
            block = {"report": name, "headers": headers, "rows": [list(r) for r in rows]}
            print(json.dumps(block, indent=2, default=str))
        else:
            print(f"\n═══ {name} ═══\n")
            _print_table(rows, headers)
    return 0


if __name__ == "__main__":
    sys.exit(main())
