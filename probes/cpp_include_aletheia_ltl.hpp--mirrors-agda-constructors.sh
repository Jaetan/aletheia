#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/ltl.hpp.
# Claim: the LtlFormulaVariant alternatives are the constructors of the Agda
# `data LTL` in src/Aletheia/LTL/Syntax.agda, one to one (the Agda WNext is
# the C++ WeakNext), and the Predicate alternatives are the constructors of
# the Agda ValuePredicate and DeltaPredicate data types together (the Agda
# SignalPredicate wraps those two), one to one. Non-zero exit: a constructor
# on either side has no counterpart.
set -u
cd "$(dirname "$0")/.." || exit 2
python/.venv/bin/python - <<'PY'
import re, sys, pathlib
def agda_constructors(path, data_name):
    text = pathlib.Path(path).read_text()
    m = re.search(r"^data %s\b.*?\n(.*?)(?=^\S)" % re.escape(data_name), text, re.M | re.S)
    if not m:
        print(f"no data {data_name} in {path}"); sys.exit(1)
    names = []
    for line in m.group(1).splitlines():
        line = line.split("--")[0]
        mm = re.match(r"^  ([A-Z][A-Za-z]*(?: [A-Z][A-Za-z]*)*)\s+:", line)
        if mm:
            names.extend(mm.group(1).split())
    return names
hpp = pathlib.Path("cpp/include/aletheia/ltl.hpp").read_text()
def cpp_alternatives(alias):
    m = re.search(r"using %s =\s*std::variant<(.*?)>;" % alias, hpp, re.S)
    return [x.strip() for x in m.group(1).replace("\n", " ").split(",")]
ltl_agda = agda_constructors("src/Aletheia/LTL/Syntax.agda", "LTL")
ltl_cpp = cpp_alternatives("LtlFormulaVariant")
pred_agda = (agda_constructors("src/Aletheia/LTL/SignalPredicate/Types.agda", "ValuePredicate")
             + agda_constructors("src/Aletheia/LTL/SignalPredicate/Types.agda", "DeltaPredicate"))
pred_cpp = cpp_alternatives("Predicate")
rename = {"WNext": "WeakNext"}
status = 0
for label, agda, cpp in (("LTL", ltl_agda, ltl_cpp), ("predicate", pred_agda, pred_cpp)):
    a = {rename.get(n, n) for n in agda}; c = set(cpp)
    for n in sorted(a - c): print(f"{label} constructor without C++ alternative: {n}"); status = 1
    for n in sorted(c - a): print(f"{label} C++ alternative without Agda constructor: {n}"); status = 1
    print(f"{label}: agda {len(a)} cpp {len(c)}")
sys.exit(status)
PY
