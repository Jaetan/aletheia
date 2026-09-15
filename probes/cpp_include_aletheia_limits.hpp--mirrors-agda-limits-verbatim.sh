# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/limits.hpp.
# Claim: every numeric bound in src/Aletheia/Limits.agda has a constant of the
# same value in limits.hpp under its snake_case name, and every wire string
# boundKindCode emits has a bound_kind_ constant with that string; nothing in
# the header is absent from the Agda module. The C++ expressions are
# evaluated, so 64ULL * 1024 * 1024 compares as a number. Non-zero exit: a
# bound or kind is missing on either side or differs in value.
set -u
cd "$(dirname "$0")/.." || exit 2
python/.venv/bin/python - <<'PY'
import re, sys, pathlib
agda = pathlib.Path("src/Aletheia/Limits.agda").read_text()
hpp = pathlib.Path("cpp/include/aletheia/limits.hpp").read_text()
agda_bounds = {m.group(1).replace("-", "_"): int(m.group(2)) for m in re.finditer(r"^(max-[a-z-]+) = (\d+)", agda, re.M)}
agda_kinds = set(re.findall(r'^boundKindCode \w+\s*= "([a-z_]+)"', agda, re.M))
cpp_bounds = {}
for m in re.finditer(r"^inline constexpr std::uint64_t (max_[a-z_]+) = ([^;]+);", hpp, re.M):
    expr = m.group(2).replace("ULL", "").replace("'", "")
    cpp_bounds[m.group(1)] = int(eval(expr, {"__builtins__": {}}))
cpp_kinds = set(re.findall(r'^inline constexpr std::string_view bound_kind_[a-z_]+ =\s*"([a-z_]+)";', hpp, re.M))
status = 0
for name, value in agda_bounds.items():
    if name not in cpp_bounds:
        print(f"missing in limits.hpp: {name} = {value}"); status = 1
    elif cpp_bounds[name] != value:
        print(f"value differs: {name} agda={value} cpp={cpp_bounds[name]}"); status = 1
for name in cpp_bounds:
    if name not in agda_bounds:
        print(f"not in Limits.agda: {name}"); status = 1
for kind in agda_kinds - cpp_kinds:
    print(f"missing bound kind in limits.hpp: {kind}"); status = 1
for kind in cpp_kinds - agda_kinds:
    print(f"bound kind not in Limits.agda: {kind}"); status = 1
print(f"bounds {len(agda_bounds)} kinds {len(agda_kinds)}")
sys.exit(status)
PY
