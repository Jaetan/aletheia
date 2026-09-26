#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_common.py, scan_tracked_tree.
# Claim: the read the tracked-tree walk performs, read_text with utf-8 and the
# replace error handler, raises nothing but OSError, so the walk's except
# clause needs no ValueError arm. The interpreter's ValueError sources for that
# call are an undecodable byte sequence, which the handler replaces, and a NUL
# inside the path, which git's NUL-delimited index cannot carry. The probe
# reads a file whose bytes are invalid UTF-8 and contain NUL, and checks that
# the walk catches OSError alone. Non-zero exit: 1 when the read raises or the
# clause names another exception; 2 when the interpreter is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
printf '\xff\xfe\x00garbage\x80\xc3' > "$work/bytes"
"$py" - "$work/bytes" <<'PY' || exit 1
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
assert "�" in text, "the replacement character was not substituted"
assert "\x00" in text, "the NUL byte did not survive the read"
PY
# The walk's body, from its def to the next def, catches OSError and names no
# ValueError; matched on the words so a reflow or a rename leaves this green.
body=$(awk '/^def scan_tracked_tree\(/ {on=1; next} on && /^def / {exit} on' tools/_common.py)
[ -n "$body" ] || { echo "scan_tracked_tree was not found"; exit 1; }
printf '%s\n' "$body" | grep -qE '^[[:space:]]+except OSError( as [a-z_]+)?:' || {
    echo "the walk does not catch OSError"
    exit 1
}
if printf '%s\n' "$body" | grep -q 'ValueError'; then
    echo "the walk still names ValueError"
    exit 1
fi
