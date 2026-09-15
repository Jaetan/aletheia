"""Which tracked file under a directory is named by at least one probe.

A probe names a file by writing its repository-relative path somewhere in the
script: in the header's claim, in a path it reads, or in a command it runs.
That spelling is the only link between the two, so this lens is a literal
search for it and nothing more.

Prints one row per tracked file, tab-separated: the path, then the probes that
name it, space-separated, and a trailing space so an unnamed file reads as an
empty second column rather than a missing one. The last line is a comment
carrying the two totals. Run from the repository root.
Usage: python file_probe_map.py <dir> [ref]
"""

import subprocess
import sys
from pathlib import Path


def tracked(directory: str, ref: str | None) -> list[str]:
    """Tracked paths under the directory, from the worktree or from a ref."""
    if ref is None:
        out = subprocess.run(
            ["git", "ls-files", directory], capture_output=True, text=True, check=True
        ).stdout
    else:
        out = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ref, directory],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    return sorted(p for p in out.split("\n") if p)


def main() -> None:
    directory = sys.argv[1].rstrip("/")
    ref = sys.argv[2] if len(sys.argv) > 2 else None
    probes = sorted(p for p in Path("probes").glob("*.sh") if p.name != "run_all.sh")
    texts = {p: p.read_text(encoding="utf-8") for p in probes}
    files = tracked(directory, ref)
    named = 0
    for f in files:
        hits = [str(p) for p in probes if f in texts[p]]
        if hits:
            named += 1
        print(f"{f}\t{' '.join(hits)} ")
    print(f"# {len(files)} tracked files under {directory}/, {named} named by a probe")


main()
