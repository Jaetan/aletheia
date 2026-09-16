"""Every completed task's report carries the lines its own contract asks for.

The three words carry different contracts, so the expected lines are keyed on
which contract the task file itself holds: the file-review points are numbered
one to eleven and open with a claims table, the document-review points are the
nine named axes, and the directory-review points are its own list. Run from the
repository root with the round directory as the argument; prints one line per
report out of shape and exits non-zero if any is.
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
    """Check every completed report in the round directory named on the command line."""
    round_dir = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    bad = 0
    counts: dict[str, int] = {"frev": 0, "drev": 0, "xrev": 0, "not completed": 0}
    for task in sorted((round_dir / "tasks").glob("*.md")):
        text = task.read_text(encoding="utf-8")
        status = re.search(r"^- status: (.+)$", text, re.M)
        if not status or status.group(1).strip() != "completed":
            counts["not completed"] += 1
            continue
        kind = ("drev" if "## DREV: the document review contract" in text
                else "xrev" if "## XREV: the directory review contract" in text
                else "frev")
        counts[kind] += 1
        body = text[text.index("## Report"):text.index("## Contract")]
        want = COMMON + {"frev": FREV, "drev": DREV, "xrev": XREV}[kind]
        missing = [w for w in want if w not in body]
        if missing:
            bad += 1
            print(f"{task.name} [{kind}] missing: {missing}")
    print(f"reports by contract: {counts}")
    print(f"out of shape: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
