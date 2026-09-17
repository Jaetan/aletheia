"""File-to-gate map: what elsewhere in the tree names each file of a directory.

Method, which is the whole of the lens and is what makes two runs comparable. For every
tracked file under the directory, three spellings are searched for as literal strings in
every other tracked file:

  the repository-relative path, always;
  the include spelling for a header under an ``include/`` root, since C++ names a header
  that way and never by its repository path;
  the bare file name, but only when no other tracked file in the repository shares it,
  so an ambiguous name is never credited to the wrong file.

The review's own archive and the probe store are excluded, the archive because it names
every file it reviews and the probe store because the file-to-probe map covers it.

A referring file counts as a gate when it is a workflow, a build-orchestration file, a
tool, or a test, wherever it lives: those are the things that fail. A sibling test inside
the directory counts, because it fails just as a workflow does.

Naming is not coverage, and the lens does not claim it is. A test that names a source
in a comment counts the same as one that exercises it, so a row can lose its gate
because a stale comment was deleted. The map is read as a list of places to look when
a file changes, and a row that falls is attributed before it is called a loss.

A file nothing outside itself names is carried by nothing but the compiler.

Usage: python3 file_gate_map.py <directory> [<git ref>]
Without a ref the working tree is read; with one, that revision is.
"""

import collections
import re
import subprocess
import sys

EXCLUDED_PREFIXES = (".archive/", "probes/")
INCLUDE_ROOTS = ("include/",)
GATE_PATTERNS = (
    re.compile(r"^\.github/workflows/"),
    re.compile(r"^tools/"),
    re.compile(r"^Shakefile\.hs$"),
    re.compile(r"^\.pre-commit-config\.yaml$"),
    re.compile(r"(^|/)tests?/"),
    re.compile(r"(^|/)test_[^/]+$"),
    re.compile(r"_test\.go$"),
    re.compile(r"(^|/)benchmarks?/"),
)


def _run(args: list[str]) -> str:
    return subprocess.run(args, capture_output=True, text=True, check=False).stdout


def _tracked(ref: str | None) -> list[str]:
    if ref is None:
        return _run(["git", "ls-files"]).splitlines()
    return _run(["git", "ls-tree", "-r", "--name-only", ref]).splitlines()


def _needles(path: str, unique_names: set[str]) -> list[str]:
    out = [path]
    for root in INCLUDE_ROOTS:
        marker = "/" + root
        if marker in path:
            out.append(path.split(marker, 1)[1])
    name = path.rsplit("/", 1)[-1]
    if name in unique_names:
        out.append(name)
    return sorted(set(out), key=len, reverse=True)


def _referrers(path: str, needles: list[str], ref: str | None) -> list[str]:
    found: set[str] = set()
    for needle in needles:
        args = ["git", "grep", "--no-color", "-l", "-F", "--", needle]
        if ref is not None:
            args = ["git", "grep", "--no-color", "-l", "-F", needle, ref, "--"]
        for hit in _run(args).splitlines():
            name = hit.split(":", 1)[1] if ref is not None and hit.startswith(ref + ":") else hit
            if name != path and not name.startswith(EXCLUDED_PREFIXES):
                found.add(name)
    return sorted(found)


def _is_gate(referrer: str) -> bool:
    return any(p.search(referrer) for p in GATE_PATTERNS)


def main() -> int:
    directory = sys.argv[1].rstrip("/") + "/"
    ref = sys.argv[2] if len(sys.argv) > 2 else None
    tracked = _tracked(ref)
    counts = collections.Counter(p.rsplit("/", 1)[-1] for p in tracked)
    unique_names = {n for n, c in counts.items() if c == 1}
    files = [f for f in tracked if f.startswith(directory)]
    gated = unnamed = 0
    for path in files:
        referrers = _referrers(path, _needles(path, unique_names), ref)
        if any(_is_gate(r) for r in referrers):
            gated += 1
        if not referrers:
            unnamed += 1
        print(path + "\t" + " ".join(referrers))
    print(
        f"# {len(files)} tracked files under {directory}, {gated} named by a gate, "
        f"{unnamed} named by nothing outside themselves",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
