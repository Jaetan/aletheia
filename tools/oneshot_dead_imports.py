#!/usr/bin/env python3
"""PROTOTYPE (ci-speed branch): one-pass dead-import detection via `agda --html`.

Thesis: the current gate (tools/prune_unused_imports.py) is brute-force —
O(imports × full-type-check): it removes each import and re-runs `agda` to see
if the file still checks. That's N agda invocations per file (N = #imports),
each paying agda startup + a re-check (~12s for a heavy module).

This prototype runs `agda --html` ONCE per file and parses Agda's own
scope-resolved highlighting. Every identifier becomes
`<a id="OFFSET" href="DefiningModule.html#ANCHOR" class="Kind">name</a>`, where
the href is the canonical DEFINITION pointer. A `using`-imported name's
declaration in the `using (...)` clause and every body use of it link to the
SAME href — even for mixfix (`using (_∷_)` declares it; the body writes `∷`;
both href to Data.List.Base#7301). So: an import is DEAD iff the href it
introduces (in the import block) never reappears at a source offset BEYOND the
import block. Matching by href (not name) handles mixfix / renaming / operators
uniformly because it is Agda's own name resolution.

~N× fewer agda invocations. SCOPE: proof-of-concept. Defers `public`
re-exports, multi-line imports, `import M as N` qualified-only usage.
"""
from __future__ import annotations

import html
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

AGDA = "/home/nicolas/.cabal/bin/agda"
SRC = Path("/home/nicolas/dev/agda/aletheia/src")

# id (source offset), href (definition pointer), link text (name)
_LINK = re.compile(r'<a id="(\d+)"[^>]*href="([^"]+\.html#\d+)"[^>]*>([^<]+)</a>')


def module_name(relpath: str) -> str:
    return relpath[:-5].replace("/", ".")


def parse_imports(text: str) -> tuple[set[str], list[tuple[int, int]]]:
    """`using`-imported names + the char-offset ranges of each `using (...)`
    clause.  Handles MULTI-LINE clauses (`[^)]*` spans newlines).  Clause ranges
    (not a single import-block threshold) distinguish an import-clause name
    occurrence from a body use, robust to imports placed anywhere.  `renaming`
    is deferred."""
    names: set[str] = set()
    ranges: list[tuple[int, int]] = []
    for m in re.finditer(r"using\s*\(([^)]*)\)", text):
        ranges.append((m.start(1), m.end(1)))
        for nm in re.split(r"[;\n]", m.group(1)):
            nm = nm.strip()
            if nm and not nm.startswith("--"):
                names.add(nm)
    return names, ranges


def main() -> int:
    relpath = sys.argv[1]
    text = (SRC / relpath).read_text()
    using_names, using_ranges = parse_imports(text)

    t0 = time.time()
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(
            [AGDA, "--html", f"--html-dir={td}", relpath],
            cwd=SRC, env={**os.environ, "GHCRTS": "-M16G -N8"},
            check=True, capture_output=True,
        )
        html_text = (Path(td) / f"{module_name(relpath)}.html").read_text()
    elapsed = time.time() - t0

    # Map each using-name to the href it introduces (its link in the import
    # block); collect the set of hrefs referenced in the BODY.
    href_of_import: dict[str, str] = {}
    body_hrefs: set[str] = set()
    body_names: set[str] = set()
    for m in _LINK.finditer(html_text):
        off, href, name = int(m.group(1)), m.group(2), html.unescape(m.group(3))
        if any(s <= off <= e for s, e in using_ranges):
            if name in using_names:
                href_of_import.setdefault(name, href)
        else:
            body_hrefs.add(href)
            body_names.add(name)

    # An import is USED if its definition href appears in the body (handles
    # mixfix: `using (_∷_)` decl vs `∷` use share an href) OR its exact name
    # does (handles re-export aliases where decl/use hrefs differ — e.g. `[]`
    # decl links to Data.List.Base but uses link to Agda.Builtin.List).  Bias to
    # no-false-positive: missing a dead import is benign; wrongly pruning a used
    # one breaks the build.
    dead = sorted(n for n, href in href_of_import.items()
                  if href not in body_hrefs and n not in body_names)
    unresolved = sorted(using_names - set(href_of_import))  # no import-block link found

    print(f"file:                  {relpath}")
    print(f"using-imported names:  {len(using_names)}")
    print(f"one-pass agda --html:  {elapsed:.1f}s (1 invocation)")
    print(f"DEAD (href never used in body): {dead if dead else '(none)'}")
    if unresolved:
        print(f"unresolved (no import-block link; deferred cases): {unresolved}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
