"""Every completed task of a round block in the task store carries the report lines its contract asks for.

The task store is one Markdown file; a round is one ``## File review round over`` block and a
task is one ``### <id> <path>`` entry under it, with its report under ``#### Report``. The
expected lines are keyed on the contract the entry names: an entry naming the directory review
contract is held to the XREV lines, one naming the document review contract to the DREV lines,
and every other entry to the file review lines. Run with the task store path and the directory
the block reviews; prints one line per report out of shape and exits non-zero if any is.
Usage: python report_shape.py <TASKS.md> <dir>
"""

import re
import sys
from pathlib import Path

COMMON = ["REPORT ", "sweep:", "decision points:"]
FREV = ["claims:", "1 line per line:", "2 guidelines:", "3 modernize:", "4 catalogue:",
        "5 value semantics:", "6 raii:", "7 dedup:", "8 ground truth:", "9 history:",
        "10 simpler:", "11 comments:"]
DREV = ["correctness:", "redundancy:", "clarity:", "checkability:", "implementability:",
        "precis:", "one line per paragraph:", "proof-read:", "diagrams:"]
XREV = ["claims:", "design and interfaces:", "value semantics:", "raii:",
        "consistency and compatibility:", "ease of use at the call sites:",
        "memory and sanitizers:", "coverage:", "ground truth:", "dryness:"]


def main() -> int:
    """Check every completed entry of the block reviewing the directory named on the command line."""
    store = Path(sys.argv[1]).read_text(encoding="utf-8")
    directory = sys.argv[2].rstrip("/")
    head = store.index(f"## File review round over `{directory}/`")
    tail = store.find("\n## ", head + 1)
    block = store[head : tail if tail != -1 else len(store)]
    entries = re.split(r"^### ", block, flags=re.M)[1:]
    bad = 0
    counts: dict[str, int] = {"frev": 0, "drev": 0, "xrev": 0, "not completed": 0}
    for entry in entries:
        title = entry.split("\n", 1)[0]
        if not re.match(r"\d{3} ", title):
            continue
        status = re.search(r"^- status: (.+)$", entry, re.M)
        if not status or status.group(1).strip() != "completed":
            counts["not completed"] += 1
            continue
        kind = ("drev" if "document review contract" in entry
                else "xrev" if "directory review contract" in entry else "frev")
        counts[kind] += 1
        body = entry[entry.index("#### Report"):]
        want = COMMON + {"frev": FREV, "drev": DREV, "xrev": XREV}[kind]
        missing = [w for w in want if w not in body]
        if missing:
            bad += 1
            print(f"{title} [{kind}] missing: {missing}")
    print(f"reports by contract: {counts}")
    print(f"out of shape: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
