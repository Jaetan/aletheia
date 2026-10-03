#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_rts_runtime.py.
# Claim: the gate refuses a runtime block whose heap-cap flag and byte count
# name two caps, and a flag that is not a -M<size> heap cap as GHC reads one
# (a decimal count, a unit in either case), and passes the SSOT as it stands.
# The whole gate is run on a scratch copy of the SSOT whose byte count is
# wrong, so a gate that stopped calling the check fails here too. And the gate
# is the document's one reader: no binding's suite spells its file name.
# Non-zero exit: 1 when an arm passed a disagreeing block, refused an agreeing
# one, or found a suite reading the document; 2 when the gate could not check
# the tree, or the interpreter is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || { echo "no $py"; exit 2; }
"$py" -m tools.check_rts_runtime
gate=$?
[ "$gate" -eq 2 ] && { echo "the gate could not check the tree"; exit 2; }
[ "$gate" -ne 0 ] && { echo "the gate refuses the tree"; exit 1; }
readers=$(git grep -lE '"[^"]*RESOURCE_BUDGETS[.]yaml"' -- python/tests go rust cpp/tests)
[ -n "$readers" ] && { echo "suites that read the document: $readers"; exit 1; }
mkdir -p tools/ci-output || exit 2
work=$(mktemp -d tools/ci-output/.rts-runtime-XXXXXX) || exit 2
trap 'rm -rf "$work"' EXIT
sed 's/^\(    bytes: \)3221225472$/\12147483648/' docs/RESOURCE_BUDGETS.yaml > "$work/budgets.yaml"
cmp -s docs/RESOURCE_BUDGETS.yaml "$work/budgets.yaml" && { echo "the scratch SSOT was not changed"; exit 2; }
"$py" - "$work/budgets.yaml" << 'PY'
import contextlib
import io
import sys
from pathlib import Path

sys.path.insert(0, ".")
import tools.check_rts_runtime as gate
from tools.check_rts_runtime import ByteCount, RuntimeSSOT, cap_divergence

cases = {
    ("-M3G", 3 << 30): False,
    ("-M3g", 3 << 30): False,
    ("-M12M", 12 << 20): False,
    ("-M512k", 512 << 10): False,
    ("-M4096", 4096): False,
    ("-M1.5G", 3 << 29): False,
    ("-M3G", 2 << 30): True,
    ("-M3M", 3 << 30): True,
    ("-M1.3k", 1331): True,
    ("-N3", 3): True,
    ("-M3T", 3 << 40): True,
}
wrong = []
for (flag, size), refused in cases.items():
    said = cap_divergence(
        RuntimeSSOT(flag, ByteCount(size), 1, "hs_init_with_rtsopts", "ALETHEIA_RTS_OPTS")
    )
    if (said is not None) != refused:
        wrong.append(f"{flag} over {size} bytes: the check said {said!r}")
gate.DEFAULT_YAML_PATH = Path(sys.argv[1])
with contextlib.redirect_stderr(io.StringIO()) as said:
    status = gate.main()
if status != 1 or "runtime.heap_cap.bytes says 2147483648" not in said.getvalue():
    wrong.append(f"the gate on a two-cap SSOT exited {status}: {said.getvalue()!r}")
for line in wrong:
    print(line)
sys.exit(1 if wrong else 0)
PY
