# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_limits_parity.py.
# Claim: the parity gate holds the C++ mirror to the Agda source of truth, so
# a value that drifts there is refused. The header is edited in place and
# restored by the same step that edits it. Non-zero exit: the gate passes on a
# drifted C++ value, the refusal does not name the C++ mirror, or the gate
# does not pass on the tree as it stands.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import subprocess
import sys
from pathlib import Path

header = Path("cpp/include/aletheia/limits.hpp")
gate = [sys.executable, "-m", "tools.check_limits_parity"]
original = header.read_text(encoding="utf-8")
needle = "inline constexpr std::uint64_t max_nesting_depth = 64;"
if needle not in original:
    print("the constant the probe drifts is not in the header")
    raise SystemExit(2)

clean = subprocess.run(gate, capture_output=True, text=True, check=False)
if clean.returncode != 0:
    print(f"the gate refuses the tree as it stands: {clean.stderr}")
    raise SystemExit(1)
if "C++" not in clean.stdout:
    print(f"the gate's summary does not name the C++ mirror: {clean.stdout}")
    raise SystemExit(1)

try:
    header.write_text(
        original.replace(needle, needle.replace("= 64;", "= 63;")), encoding="utf-8"
    )
    drifted = subprocess.run(gate, capture_output=True, text=True, check=False)
finally:
    header.write_text(original, encoding="utf-8")

if drifted.returncode == 0:
    print("a drifted C++ value was accepted")
    raise SystemExit(1)
if "C++ max-constant" not in drifted.stderr:
    print(f"the refusal is not about the C++ mirror: {drifted.stderr}")
    raise SystemExit(1)
PY
