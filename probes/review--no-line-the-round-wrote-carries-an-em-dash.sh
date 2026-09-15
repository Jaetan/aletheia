# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the review store's own rule.
# Claim: no line a review round writes carries an em-dash. The rule covers
# what the round writes, not what it inherits, so a line is a finding only
# when it differs from every line of the same file in the tree the round
# started from. A round's record also holds captured tool output, which the
# round did not write but merely stored; under a record's base and end
# directories only Markdown is prose, and everything else is a capture and is
# not scanned. Skipped (exit 0) when the base tree is not anchored, since the
# claim is then untestable. Non-zero exit: at least one written line carries
# one.
set -u
cd "$(dirname "$0")/.." || exit 2
git rev-parse --verify --quiet refs/frev/base > /dev/null || {
    echo "no review base tree anchored, claim untestable"
    exit 0
}
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import subprocess
import sys

DASH = chr(0x2014)  # spelled by code point so this probe is not its own finding


def is_captured_output(path: str) -> bool:
    """A round's record stores tool output verbatim; the round did not write it."""
    parts = path.split("/")
    return "base" in parts or "end" in parts if not path.endswith(".md") else False
diff = subprocess.run(
    ["git", "diff", "refs/frev/base"], capture_output=True, text=True, errors="replace", check=False
)
if diff.returncode != 0:
    print("the diff against the review base tree could not be read")
    raise SystemExit(2)

base_lines: dict[str, set[str]] = {}
current = None
written: list[str] = []
for line in diff.stdout.split("\n"):
    if line.startswith("+++ b/"):
        current = line[6:]
    elif (
        line.startswith("+")
        and not line.startswith("+++")
        and DASH in line
        and current is not None
        and not is_captured_output(current)
    ):
        if current not in base_lines:
            shown = subprocess.run(
                ["git", "show", f"refs/frev/base:{current}"],
                capture_output=True,
                text=True,
                errors="replace",
                check=False,
            )
            base_lines[current] = set(shown.stdout.split("\n")) if shown.returncode == 0 else set()
        if line[1:] not in base_lines[current]:
            written.append(f"{current}: {line[1:].strip()[:90]}")
for row in written:
    print(row)
sys.exit(1 if written else 0)
PY
