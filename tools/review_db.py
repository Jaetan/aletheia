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
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NotRequired, TypedDict, cast

from tools._common import emit

if TYPE_CHECKING:
    from collections.abc import Callable

try:
    import yaml
except ImportError:
    _ = sys.stderr.write(
        "tools/review_db.py: PyYAML is required.  Install via "
        + "`python/.venv/bin/pip install pyyaml` or use the project venv.\n"
    )
    sys.exit(2)


# ─────────────────────────── typed record shapes ─────────────────────────
#
# YAML and sqlite both hand back dynamically-typed data.  The two validators
# below verify the raw shape of each parsed mapping (working over
# ``dict[str, object]`` so the ``isinstance`` checks are meaningful), after
# which ``build_db`` casts the verified mapping to one of these TypedDicts for
# statically-checked field access on the INSERT path.


class CategoryDict(TypedDict):
    """The ``category`` sub-mapping of a finding record."""

    number: int
    name: str
    language: str
    agent: str


class ResolutionDict(TypedDict):
    """The optional ``resolution`` sub-mapping of a finding record."""

    commit: NotRequired[str | None]
    round: NotRequired[str | None]
    date: NotRequired[str | None]
    notes: NotRequired[str | None]


class FindingDict(TypedDict):
    """A single closed-finding record, post-validation."""

    id: str
    round: str
    category: CategoryDict
    severity: str
    disposition: str
    status: str
    title: str
    description: NotRequired[str | None]
    cluster: NotRequired[str | None]
    resolution: NotRequired[ResolutionDict | None]
    files: NotRequired[list[str] | None]
    tags: NotRequired[list[str] | None]
    re_raised_from: NotRequired[str | None]
    in_source_marker: NotRequired[str | None]


class RoundDict(TypedDict):
    """A single review-round metadata record, post-validation."""

    id: str
    fork_point: str
    fork_date: str
    merge_commit: NotRequired[str | None]
    merge_date: NotRequired[str | None]
    status: str
    raw_findings_count: NotRequired[int | None]
    closed_findings_count: NotRequired[int | None]
    notes: NotRequired[str | None]


# A report returns its data rows plus the column headers that label them.
ReportResult = tuple[list[tuple[object, ...]], list[str]]


# ─────────────────────────── repo discovery ──────────────────────────────


def find_repo_root(start: Path) -> Path:
    """Walk up from *start* until aletheia.agda-lib is found."""
    cur = start.resolve()
    while cur != cur.parent:
        if (cur / "aletheia.agda-lib").is_file():
            return cur
        cur = cur.parent
    message = "tools/review_db.py: cannot find repo root (aletheia.agda-lib not found in ancestors)"
    raise SystemExit(message)


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

# Dispositions whose presence means a *real* issue was caught (as opposed to a
# false positive / dropped / deferred finding).  Used by the graduation and
# critical/high reports.
_REAL_DISPOSITIONS = {"FIX", "FIX-PARTIAL", "NO-FIX"}

# Default lookback window (in rounds) for the graduation report.
_DEFAULT_GRADUATION_ROUNDS = 2


def _check(*, cond: bool, where: str, msg: str) -> None:
    """Raise a schema ``SystemExit`` naming *where* and *msg* unless *cond* holds."""
    if not cond:
        message = f"tools/review_db.py: schema error in {where}: {msg}"
        raise SystemExit(message)


def _is_sha(value: object) -> bool:
    """Return whether *value* is a string matching the abbreviated-SHA pattern."""
    return isinstance(value, str) and bool(_SHA_RE.match(value))


def _is_round_id(value: object) -> bool:
    """Return whether *value* is a string matching the round-id pattern."""
    return isinstance(value, str) and bool(_ROUND_ID_RE.match(value))


def _is_date(value: object) -> bool:
    """Return whether *value* is a string matching the YYYY-MM-DD pattern."""
    return isinstance(value, str) and bool(_DATE_RE.match(value))


def _is_finding_id(value: object) -> bool:
    """Return whether *value* is a string matching the finding-id pattern."""
    return isinstance(value, str) and bool(_FINDING_ID_RE.match(value))


def _validate_category(cat: object, where: str) -> None:
    """Validate the ``category`` sub-mapping of a finding."""
    _check(cond=isinstance(cat, dict), where=where, msg="category must be a mapping")
    catd = cast("dict[str, object]", cat)
    for k in ("number", "name", "language", "agent"):
        _check(cond=k in catd, where=where, msg=f"category missing {k}")
    number = catd["number"]
    _check(
        cond=isinstance(number, int) and number >= 1,
        where=where,
        msg="category.number must be a positive int",
    )
    _check(
        cond=catd["language"] in _VALID_LANGUAGES,
        where=where,
        msg=f"category.language {catd['language']!r} invalid",
    )
    _check(
        cond=catd["agent"] in _VALID_AGENTS,
        where=where,
        msg=f"category.agent {catd['agent']!r} invalid",
    )


def _validate_resolution(res: object, where: str) -> None:
    """Validate the optional ``resolution`` sub-mapping of a finding."""
    _check(cond=isinstance(res, dict), where=where, msg="resolution must be a mapping")
    resd = cast("dict[str, object]", res)
    if "commit" in resd:
        _check(
            cond=_is_sha(resd["commit"]),
            where=where,
            msg=f"resolution.commit {resd['commit']!r} not a SHA",
        )
    if "round" in resd:
        _check(
            cond=_is_round_id(resd["round"]),
            where=where,
            msg=f"resolution.round {resd['round']!r} invalid",
        )
    if "date" in resd:
        _check(
            cond=_is_date(resd["date"]),
            where=where,
            msg=f"resolution.date {resd['date']!r} not YYYY-MM-DD",
        )


def validate_finding(raw: object, path: Path) -> None:
    """Validate the shape of a parsed finding YAML mapping, raising on error."""
    where = str(path)
    _check(cond=isinstance(raw, dict), where=where, msg="top-level must be a mapping")
    d = cast("dict[str, object]", raw)
    for k in ("id", "round", "category", "severity", "disposition", "status", "title"):
        _check(cond=k in d, where=where, msg=f"missing required key: {k}")
    _check(
        cond=_is_finding_id(d["id"]),
        where=where,
        msg=f"id {d['id']!r} not <ROUND>-<LANG>-<AGENT>-<CAT>.<NUM>",
    )
    _check(cond=_is_round_id(d["round"]), where=where, msg=f"round {d['round']!r} not R<n>")
    _validate_category(d["category"], where)
    _check(
        cond=d["severity"] in _VALID_SEVERITIES,
        where=where,
        msg=f"severity {d['severity']!r} invalid",
    )
    _check(
        cond=d["disposition"] in _VALID_DISPOSITIONS,
        where=where,
        msg=f"disposition {d['disposition']!r} invalid",
    )
    _check(cond=d["status"] in _VALID_STATUSES, where=where, msg=f"status {d['status']!r} invalid")
    if "resolution" in d and d["resolution"] is not None:
        _validate_resolution(d["resolution"], where)
    if d.get("re_raised_from"):
        _check(
            cond=_is_finding_id(d["re_raised_from"]),
            where=where,
            msg=f"re_raised_from {d['re_raised_from']!r} not a finding id",
        )


def validate_round(raw: object, path: Path) -> None:
    """Validate the shape of a parsed round YAML mapping, raising on error."""
    where = str(path)
    _check(cond=isinstance(raw, dict), where=where, msg="top-level must be a mapping")
    d = cast("dict[str, object]", raw)
    for k in ("id", "fork_point", "fork_date", "status"):
        _check(cond=k in d, where=where, msg=f"missing required key: {k}")
    _check(cond=_is_round_id(d["id"]), where=where, msg=f"id {d['id']!r} not R<n>")
    _check(
        cond=_is_sha(d["fork_point"]),
        where=where,
        msg=f"fork_point {d['fork_point']!r} not a SHA",
    )
    _check(
        cond=_is_date(d["fork_date"]),
        where=where,
        msg=f"fork_date {d['fork_date']!r} not YYYY-MM-DD",
    )
    _check(
        cond=d["status"] in _VALID_ROUND_STATUSES,
        where=where,
        msg=f"status {d['status']!r} invalid",
    )
    if d.get("merge_commit"):
        _check(
            cond=_is_sha(d["merge_commit"]),
            where=where,
            msg=f"merge_commit {d['merge_commit']!r} not a SHA",
        )
    if d.get("merge_date"):
        _check(
            cond=_is_date(d["merge_date"]),
            where=where,
            msg=f"merge_date {d['merge_date']!r} not YYYY-MM-DD",
        )


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


def _insert_round(conn: sqlite3.Connection, raw: object, rfile: Path) -> None:
    """Validate *raw* and insert it as one ``rounds`` row."""
    validate_round(raw, rfile)
    r = cast("RoundDict", raw)
    _ = conn.execute(
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


def _insert_finding(conn: sqlite3.Connection, raw: object, ff: Path) -> None:
    """Validate *raw* and insert it as one ``findings`` row plus its file/tag rows."""
    validate_finding(raw, ff)
    d = cast("FindingDict", raw)
    cat = d["category"]
    res: ResolutionDict = d.get("resolution") or {}
    _ = conn.execute(
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
        _ = conn.execute("INSERT INTO finding_files VALUES (?, ?)", (d["id"], p))
    for t in d.get("tags") or []:
        _ = conn.execute("INSERT INTO finding_tags VALUES (?, ?)", (d["id"], t))


def build_db(repo_root: Path) -> sqlite3.Connection:
    """Build the in-memory findings DB from the YAML corpus under *repo_root*."""
    conn = sqlite3.connect(":memory:")
    _ = conn.executescript(_SCHEMA_SQL)
    archive = repo_root / ".archive" / "reviews"
    if not archive.is_dir():
        message = f"tools/review_db.py: archive directory {archive} not found"
        raise SystemExit(message)

    round_dirs = sorted(p for p in archive.iterdir() if p.is_dir() and p.name.startswith("r"))
    for rd in round_dirs:
        rfile = rd / "round.yaml"
        if not rfile.is_file():
            _ = sys.stderr.write(
                f"tools/review_db.py: warning: {rd} missing round.yaml -- skipping\n"
            )
            continue
        with rfile.open() as f:
            _insert_round(conn, yaml.safe_load(f), rfile)

        findings_dir = rd / "findings"
        if findings_dir.is_dir():
            for ff in sorted(findings_dir.glob("*.yaml")):
                with ff.open() as f:
                    _insert_finding(conn, yaml.safe_load(f), ff)

    _ = conn.commit()
    return conn


# ─────────────────────────── canned reports ──────────────────────────────


def _cell(value: object) -> str:
    """Render one table cell: the empty string for ``None``, else ``str(value)``."""
    return "" if value is None else str(value)


def _print_table(rows: list[tuple[object, ...]], headers: list[str]) -> None:
    """Print *rows* as a left-aligned, column-width-padded text table."""
    if not rows:
        emit("(no rows)")
        return
    header_row: tuple[str, ...] = tuple(headers)
    body_rows: list[tuple[str, ...]] = [tuple(_cell(c) for c in r) for r in rows]
    cols = list(zip(*([header_row, *body_rows]), strict=False))
    widths = [max(len(c) for c in col) for col in cols]
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    emit(fmt.format(*headers))
    emit(fmt.format(*("-" * w for w in widths)))
    for r in rows:
        emit(fmt.format(*(_cell(c) for c in r)))


def _round_ids(cur: sqlite3.Cursor) -> list[str]:
    """Return all round ids in ascending order."""
    raw = cur.execute("SELECT id FROM rounds ORDER BY id").fetchall()
    return [cast("tuple[str]", r)[0] for r in raw]


def report_category_trend(conn: sqlite3.Connection) -> ReportResult:
    """Count of closed findings per (language, category_number) per round.

    Pivoted: one row per (language, category, name), columns = rounds.
    """
    cur = conn.cursor()
    rounds = _round_ids(cur)
    raw = cur.execute(
        """SELECT category_language, category_number, category_name, round, COUNT(*)
           FROM findings
           GROUP BY category_language, category_number, category_name, round
           ORDER BY category_language, category_number"""
    ).fetchall()
    pivot: dict[tuple[str, int, str], dict[str, int]] = {}
    for row in raw:
        lang, num, name, rnd, cnt = cast("tuple[str, int, str, str, int]", row)
        pivot.setdefault((lang, num, name), {})[rnd] = cnt
    headers = ["lang", "cat", "name", *rounds]
    out_rows: list[tuple[object, ...]] = [
        (lang, num, name, *(pivot[(lang, num, name)].get(r, 0) for r in rounds))
        for (lang, num, name) in sorted(pivot.keys())
    ]
    return out_rows, headers


def report_re_raise(conn: sqlite3.Connection) -> ReportResult:
    """Per round, count findings that re-raise a prior closure.

    Broken down by predecessor round.
    """
    cur = conn.cursor()
    raw = cur.execute(
        """SELECT f.round AS this_round,
                  SUBSTR(f.re_raised_from, 1, INSTR(f.re_raised_from, '-') - 1) AS pred,
                  COUNT(*)
           FROM findings f
           WHERE f.re_raised_from IS NOT NULL
           GROUP BY this_round, pred
           ORDER BY this_round, pred"""
    ).fetchall()
    rows = cast("list[tuple[object, ...]]", raw)
    return rows, ["round", "re-raised from", "count"]


def report_severity_trend(conn: sqlite3.Connection) -> ReportResult:
    """Per-round severity distribution.

    Critical/high are the key scope-decrease signal: should stay at 0 after
    they have been driven down.
    """
    cur = conn.cursor()
    rounds = _round_ids(cur)
    severities = ["critical", "high", "medium", "low", "info"]
    grid: dict[str, dict[str, int]] = {sev: dict.fromkeys(rounds, 0) for sev in severities}
    raw = cur.execute(
        "SELECT severity, round, COUNT(*) FROM findings GROUP BY severity, round"
    ).fetchall()
    for row in raw:
        sev, rnd, cnt = cast("tuple[str, str, int]", row)
        grid[sev][rnd] = cnt
    headers = ["severity", *rounds]
    out_rows: list[tuple[object, ...]] = [
        (sev, *(grid[sev][r] for r in rounds)) for sev in severities
    ]
    return out_rows, headers


def report_disposition_mix(conn: sqlite3.Connection) -> ReportResult:
    """Per-round disposition distribution.

    FP rate climbing is the scanner-limit / agent-saturation signal.
    """
    cur = conn.cursor()
    rounds = _round_ids(cur)
    dispositions = sorted(_VALID_DISPOSITIONS)
    grid: dict[str, dict[str, int]] = {d: dict.fromkeys(rounds, 0) for d in dispositions}
    raw = cur.execute(
        "SELECT disposition, round, COUNT(*) FROM findings GROUP BY disposition, round"
    ).fetchall()
    for row in raw:
        disp, rnd, cnt = cast("tuple[str, str, int]", row)
        grid[disp][rnd] = cnt
    headers = ["disposition", *rounds]
    out_rows: list[tuple[object, ...]] = [
        (disp, *(grid[disp][r] for r in rounds)) for disp in dispositions
    ]
    return out_rows, headers


@dataclass
class _CategoryTally:
    """Per-category accumulator for the graduation report's window aggregates."""

    name: str | None = None
    real_recent: int = 0
    real_earlier: int = 0
    any_recent: int = 0

    def note_name(self, name: str) -> None:
        """Track the lexicographically smallest category name seen (SQL ``MIN``)."""
        if self.name is None or name < self.name:
            self.name = name

    def observe(self, name: str, *, in_recent: bool, is_real: bool) -> None:
        """Fold one finding into this category's recent/earlier window counts."""
        self.note_name(name)
        if in_recent:
            self.any_recent += 1
            if is_real:
                self.real_recent += 1
        elif is_real:
            self.real_earlier += 1


def _graduation_rows(cur: sqlite3.Cursor, recent: list[str]) -> list[tuple[object, ...]]:
    """Tally per-category window aggregates and return the graduation candidates.

    A candidate is a category with zero real findings inside the *recent* window
    but at least one real finding earlier, ordered to mirror the SQL
    ``ORDER BY real_earlier DESC, category_language, category_number``.
    """
    recent_set = set(recent)
    raw = cur.execute(
        """SELECT category_language, category_number, category_name, round, disposition
           FROM findings"""
    ).fetchall()
    tallies: dict[tuple[str, int], _CategoryTally] = {}
    for row in raw:
        lang, num, name, rnd, disp = cast("tuple[str, int, str, str, str]", row)
        tallies.setdefault((lang, num), _CategoryTally()).observe(
            name, in_recent=rnd in recent_set, is_real=disp in _REAL_DISPOSITIONS
        )
    candidates = [
        (lang, num, t)
        for (lang, num), t in tallies.items()
        if t.real_recent == 0 and t.real_earlier > 0
    ]
    candidates.sort(key=lambda item: (-item[2].real_earlier, item[0], item[1]))
    return [
        (lang, num, t.name, t.real_recent, t.real_earlier, t.any_recent)
        for (lang, num, t) in candidates
    ]


def report_graduation(
    conn: sqlite3.Connection, n_rounds: int = _DEFAULT_GRADUATION_ROUNDS
) -> ReportResult:
    """Categories with zero real findings in the most-recent *n_rounds* rounds.

    Restricted to categories that have been active in earlier rounds (i.e. had a
    real finding ever).  A category that goes N rounds with no real findings
    (FIX/FIX-PARTIAL/NO-FIX closures imply a real issue was caught) after having
    had real findings earlier is a graduation candidate per AGENTS.md.
    """
    cur = conn.cursor()
    rounds = _round_ids(cur)
    recent = rounds[-n_rounds:] if len(rounds) >= n_rounds else rounds
    if not recent:
        return [], ["lang", "cat", "name", f"real (last {n_rounds})", "real (history)"]
    out_rows = _graduation_rows(cur, recent)
    headers = [
        "lang",
        "cat",
        "name",
        f"real (last {n_rounds})",
        "real (earlier rounds)",
        f"any disposition (last {n_rounds})",
    ]
    return out_rows, headers


def report_round_summary(conn: sqlite3.Connection) -> ReportResult:
    """Per-round summary: declared vs in-DB closed counts plus merge metadata."""
    cur = conn.cursor()
    raw = cur.execute(
        """SELECT r.id, r.status, r.fork_date, r.merge_date, r.raw_findings_count,
                  r.closed_findings_count, COUNT(f.id), r.merge_commit
           FROM rounds r LEFT JOIN findings f ON f.round = r.id
           GROUP BY r.id
           ORDER BY r.id"""
    ).fetchall()
    rows = cast("list[tuple[object, ...]]", raw)
    return rows, [
        "round",
        "status",
        "forked",
        "merged",
        "raw",
        "closed (decl)",
        "closed (in DB)",
        "merge SHA",
    ]


def report_critical_high_trend(conn: sqlite3.Connection) -> ReportResult:
    """Per-round count of critical + high severity findings (FIX/FIX-PARTIAL).

    The 'should-stay-zero' invariant check: flags any round that regressed a
    prior round's zero for either severity.
    """
    cur = conn.cursor()
    raw = cur.execute(
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
    out: list[tuple[object, ...]] = []
    prev_crit: int | None = None
    prev_high: int | None = None
    for row in raw:
        rnd, crit, high, regr = cast("tuple[str, int, int, int]", row)
        flag = ""
        if prev_crit == 0 and crit > 0:
            flag = "CRITICAL-REGRESSED"
        elif prev_high == 0 and high > 0:
            flag = "HIGH-REGRESSED"
        out.append((rnd, crit, high, regr, flag))
        prev_crit, prev_high = crit, high
    return out, ["round", "critical (FIX)", "high (FIX)", "C/H re-raises", "regression flag"]


REPORTS: dict[str, Callable[..., ReportResult]] = {
    "category-trend": report_category_trend,
    "re-raise": report_re_raise,
    "severity-trend": report_severity_trend,
    "critical-high-trend": report_critical_high_trend,
    "disposition-mix": report_disposition_mix,
    "graduation": report_graduation,
    "round-summary": report_round_summary,
}


# ─────────────────────────── cli ─────────────────────────────────────────


def _run_query(conn: sqlite3.Connection, query: str, *, as_json: bool) -> None:
    """Run an ad-hoc SQL *query* and print the rows as JSON or a text table."""
    cur = conn.execute(query)
    headers = [cast("tuple[str, object]", d)[0] for d in (cur.description or [])]
    rows = cast("list[tuple[object, ...]]", cur.fetchall())
    if as_json:
        payload = [dict(zip(headers, r, strict=False)) for r in rows]
        emit(json.dumps(payload, indent=2, default=str))
    else:
        _print_table(rows, headers)


def _run_reports(
    conn: sqlite3.Connection, report: str, *, graduation_rounds: int, as_json: bool
) -> None:
    """Run the named canned *report* (or every report when ``report == "all"``)."""
    reports_to_run = sorted(REPORTS.keys()) if report == "all" else [report]
    for name in reports_to_run:
        fn = REPORTS[name]
        rows, headers = fn(conn, graduation_rounds) if name == "graduation" else fn(conn)
        if as_json:
            block: dict[str, object] = {
                "report": name,
                "headers": headers,
                "rows": [list(r) for r in rows],
            }
            emit(json.dumps(block, indent=2, default=str))
        else:
            emit(f"\n═══ {name} ═══\n")
            _print_table(rows, headers)


def main() -> int:
    """Parse arguments and run the requested schema dump / query / report."""
    ap = argparse.ArgumentParser(
        prog="tools/review_db.py",
        description="Review findings analytics over .archive/reviews/r*/",
    )
    ap.add_argument(
        "--report", choices=[*sorted(REPORTS.keys()), "all"], help="Run a canned report."
    )
    ap.add_argument(
        "--query", metavar="SQL", help="Run an ad-hoc SQL query against the DB and print rows."
    )
    ap.add_argument("--schema", action="store_true", help="Print the SQLite schema and exit.")
    ap.add_argument(
        "--json", action="store_true", help="Emit report output as JSON instead of a table."
    )
    ap.add_argument(
        "--graduation-rounds",
        type=int,
        default=_DEFAULT_GRADUATION_ROUNDS,
        help="Window size for --report graduation (default 2).",
    )
    args = ap.parse_args()
    schema: bool = cast("bool", args.schema)
    query: str | None = cast("str | None", args.query)
    report: str | None = cast("str | None", args.report)
    as_json: bool = cast("bool", args.json)
    graduation_rounds: int = cast("int", args.graduation_rounds)

    if schema:
        emit(_SCHEMA_SQL.strip())
        return 0

    repo_root = find_repo_root(Path(__file__).parent)
    conn = build_db(repo_root)

    if query:
        _run_query(conn, query, as_json=as_json)
        return 0

    if not report:
        ap.print_help()
        return 0

    _run_reports(conn, report, graduation_rounds=graduation_rounds, as_json=as_json)
    return 0


if __name__ == "__main__":
    sys.exit(main())
