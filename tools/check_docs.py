# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Documentation-accuracy gate: broken links, broken anchors, transient labels.

Scans every tracked ``*.md`` and fails (exit 1) on:

1. **Broken relative links** — ``[text](target)`` whose target file is missing.
   Fenced code blocks are skipped, so a ``[](const T& e)`` lambda inside a
   ```` ``` ```` fence is not mistaken for a link (a real false positive the
   r26 audit hit).
2. **Broken anchors** — ``#slug`` (same-file or ``file.md#slug``) with no matching
   header in the target. GitHub slugs are computed WITHOUT collapsing whitespace
   runs, so ``## Change Detection & Stability`` → ``change-detection--stability``.
3. **Transient / internal labels** in the user-facing docs — internal review
   marks (``(PR C)``, ``R19 cluster``, ``AGDA-C-6.2``, ``PY-S-20.1``), transient
   session phrases (``pending push``), and committed links INTO the private
   ``~/.claude`` agent memory store (unresolvable in a checkout).

Run ``python -m tools.check_docs`` from the repo root. Its parsers are unit-tested
by ``python/tests/test_check_docs.py``.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

from tools._common import emit, find_executable

REPO = Path(__file__).resolve().parent.parent

# Inline [text](target) and reference-style [id]: target.
_INLINE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
_REFDEF = re.compile(r"^\s*\[[^\]]+\]:\s*(\S+)", re.MULTILINE)
_ATX = re.compile(r"^(#{1,6})\s+(.*?)\s*#*\s*$")
_HTML_ANCHOR = re.compile(r'(?:name|id)="([^"]+)"')
_FENCE = re.compile(r"^\s*(```|~~~)")
# An inline code span: `...`. A link-shaped string inside backticks is code, not
# a link — e.g. prose describing link syntax as `[text](target)`. Masked before
# link extraction so it is not mistaken for a real link (the inline analogue of
# the fenced-block skip).
_INLINE_CODE = re.compile(r"`[^`]*`")

# Transient / internal labels — checked only in the user-facing doc surface.
_LABEL_PATTERNS = [
    (re.compile(r"\(PR [A-Z]\d*\)"), "internal PR label"),
    (re.compile(r"\bR\d+ cluster\b"), "review-round cluster mark"),
    (re.compile(r"\b(?:AGDA|GO|CPP|PY|RUST|XBINDING|DOCS)-[A-Z]-\d+\.\d+"), "finding id"),
    (re.compile(r"\bPY-S-\d+"), "review finding mark"),
    (re.compile(r"\bpending push\b", re.IGNORECASE), "transient session phrase"),
    (re.compile(r"\bcommitted locally\b", re.IGNORECASE), "transient session phrase"),
]
# A markdown link INTO the agent memory store (outside any checkout).
_MEMORY_LINK = re.compile(r"\][(](?:[^)]*/\.claude/[^)]*|memory/[^)]*)[)]")

# Frozen/historical-by-purpose surfaces are skipped ENTIRELY (both checks):
# the archived snapshot and the presentation deck are not maintained.
_SKIP_PREFIXES = ("docs/archive/", "docs/presentation/")

# Transient-label + memory-link checks apply to every LIVING doc — the whole
# `docs/` tree (front door, guides, reference, AND the contributor docs under
# architecture/development/operations, which must describe the CURRENT state,
# pruned of past-referring review-process marks) plus README + per-binding
# READMEs. The repo-root logs (CHANGELOG, PROJECT_STATUS) are historical BY
# PURPOSE, so they are not label-scoped; they are still link-checked.
_LABEL_SCOPE_PREFIXES = ("docs/",)
_LABEL_SCOPE_FILES = {"README.md"}
_LABEL_SCOPE_SUFFIX = "/README.md"


def _tracked_md() -> list[Path]:
    out = subprocess.run(
        [find_executable("git"), "ls-files", "*.md", "*.markdown"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split()
    return [REPO / p for p in out]


def slug(header: str) -> str:
    """GitHub-flavored anchor slug (no whitespace-run collapse)."""
    s = header.strip().lower()
    s = s.replace("`", "")
    s = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", s)  # [t](u) -> t
    s = re.sub(r"[^\w\s-]", "", s)  # drop punctuation, KEEP surrounding spaces
    return re.sub(r"\s", "-", s)  # each whitespace char -> one hyphen (no collapse)


def header_slugs(path: Path) -> set[str]:
    """Return the set of GitHub anchor slugs for every header in ``path``.

    ATX headers outside fenced code blocks, deduplicated with GitHub's
    ``-1``/``-2`` suffixing, plus any explicit ``name=``/``id=`` HTML anchors.
    """
    slugs: set[str] = set()
    counts: dict[str, int] = {}
    text = path.read_text(encoding="utf-8", errors="replace")
    in_fence = False
    for line in text.splitlines():
        if _FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        m = _ATX.match(line)
        if m:
            base = slug(m.group(2))
            n = counts.get(base, 0)
            counts[base] = n + 1
            slugs.add(base if n == 0 else f"{base}-{n}")
    slugs.update(_HTML_ANCHOR.findall(text))
    return slugs


def links(path: Path) -> list[str]:
    """Links outside fenced code blocks."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    out: list[str] = []
    in_fence = False
    for line in lines:
        if _FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        masked = _INLINE_CODE.sub("", line)  # a `[t](u)`-shaped code span is not a link
        out.extend(_INLINE.findall(masked))
        out.extend(_REFDEF.findall(masked))
    return out


def _in_label_scope(rel: str) -> bool:
    return (
        rel in _LABEL_SCOPE_FILES
        or rel.startswith(_LABEL_SCOPE_PREFIXES)
        or rel.endswith(_LABEL_SCOPE_SUFFIX)
    )


def _link_finding(raw: str, src: Path, header_cache: dict[Path, set[str]]) -> str | None:
    """Return a finding suffix for one extracted link, or None if it resolves."""
    link = raw.strip().split(" ", 1)[0]  # drop optional "title"
    if link.startswith(("http://", "https://", "mailto:", "tel:", "#!", "<")):
        return None
    target, _, anchor = link.partition("#")
    tgt = src if target == "" else (src.parent / target).resolve()
    if not tgt.exists():
        return f"broken link -> {link}"
    if anchor and tgt.is_file() and tgt.suffix in (".md", ".markdown"):
        hs = header_cache.get(tgt) or header_slugs(tgt)
        if anchor.lower() not in {h.lower() for h in hs}:
            return f"broken anchor -> {link}"
    return None


def _label_findings(text: str) -> list[str]:
    """Return finding suffixes for each transient label / memory link in ``text``."""
    out = [
        f"link into the ~/.claude memory store -> {m.group(0)}" for m in _MEMORY_LINK.finditer(text)
    ]
    for pat, why in _LABEL_PATTERNS:
        out.extend(f"{why} -> {m!r}" for m in {m.group(0) for m in pat.finditer(text)})
    return out


def check_tree(md_files: list[Path]) -> list[str]:
    """Return a list of human-readable findings (empty = clean)."""
    header_cache = {p: header_slugs(p) for p in md_files}
    findings: list[str] = []

    for src in md_files:
        rel = str(src.relative_to(REPO))
        if rel.startswith(_SKIP_PREFIXES):
            continue
        findings.extend(
            f"{rel}: {f}"
            for raw in links(src)
            if (f := _link_finding(raw, src, header_cache)) is not None
        )
        if _in_label_scope(rel):
            text = src.read_text(encoding="utf-8", errors="replace")
            findings.extend(f"{rel}: {suffix}" for suffix in _label_findings(text))
    return findings


def main(argv: list[str] | None = None) -> int:
    """Scan every tracked Markdown file; return 1 (and list defects) if any, else 0."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)  # no options; --help only

    findings = check_tree(_tracked_md())
    if findings:
        emit(f"check_docs: {len(findings)} documentation defect(s):")
        for f in findings:
            emit(f"  {f}")
        return 1
    emit("check_docs: all documentation links/anchors resolve; no transient labels.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
