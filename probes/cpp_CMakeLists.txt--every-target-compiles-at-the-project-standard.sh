# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: every translation unit the build compiles from cpp/src, cpp/tests
# and cpp/benchmarks carries the project's language standard. The standard
# reaches most targets transitively through the library's PUBLIC compile
# feature, so a target that links neither the library nor a dependency
# carrying the feature silently falls back to the compiler's default and is
# held to an older language than the rest of the binding. Non-zero exit: at
# least one unit is compiled without -std=gnu++23, or no compile database
# exists to check.
set -u
cd "$(dirname "$0")/.." || exit 2
db=cpp/build/compile_commands.json
[ -f "$db" ] || { echo "no compile database at $db; configure cpp/build first"; exit 1; }
python/.venv/bin/python - "$db" <<'PY'
import json, sys
entries = json.load(open(sys.argv[1]))
want = "-std=gnu++23"
missing = sorted(
    {e["file"] for e in entries
     if any(f"/cpp/{d}/" in e["file"] for d in ("src", "tests", "benchmarks"))
     and want not in e.get("command", "")}
)
for path in missing:
    print(f"compiled without {want}: {path}")
sys.exit(1 if missing else 0)
PY
