#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the four bindings' predicate builders against the kernel.
# Claim: every predicate the kernel defines has a builder in every binding, and
# the spelling is the constructor's own name in that language's case. The
# kernel's set is read from src/Aletheia/LTL/SignalPredicate/Types.agda, where
# the two predicate families are declared, so a predicate added there fails
# this until every binding can build it. The defect it catches is a binding
# that carries part of the set: a caller then reaches for a struct literal, or
# for a spelling another binding does not have, and the parity matrix reads as
# though the whole family were there.
# Non-zero exit: a binding cannot build a predicate the kernel has.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import ast
import re
import sys

agda = open("src/Aletheia/LTL/SignalPredicate/Types.agda", encoding="utf-8").read()

# The constructors of both predicate families, in declaration order.
kernel = []
for family in ("ValuePredicate", "DeltaPredicate"):
    m = re.search(rf"^data {family} : Set where\n((?:  \S.*\n)+)", agda, re.M)
    if not m:
        print(f"the kernel no longer declares {family} where this reads it")
        raise SystemExit(2)
    kernel += re.findall(r"^  (\w+)\s*:", m.group(1), re.M)
if len(kernel) < 2:
    print("read no predicate constructors from the kernel")
    raise SystemExit(2)


def snake(name):
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


# Python: the methods of the Signal class, read as source rather than imported.
tree = ast.parse(open("python/aletheia/dsl.py", encoding="utf-8").read())
signal = next((n for n in ast.walk(tree) if isinstance(n, ast.ClassDef) and n.name == "Signal"), None)
if signal is None:
    print("python/aletheia/dsl.py no longer defines a Signal class")
    raise SystemExit(2)
python_methods = {n.name for n in signal.body if isinstance(n, ast.FunctionDef)}

cpp = open("cpp/include/aletheia/ltl.hpp", encoding="utf-8").read()
go = open("go/aletheia/ltl.go", encoding="utf-8").read()
rust = open("rust/src/ltl.rs", encoding="utf-8").read()
cpp_functions = set(re.findall(r"inline auto (\w+)\(", cpp))
go_methods = set(re.findall(r"func \(\w+ SignalBuilder\) (\w+)\(", go))
rust_constructors = set(re.findall(r"pub fn (\w+)\(\s*signal:", rust))

missing = []
for name in kernel:
    for binding, have, spelling in (
        ("python", python_methods, snake(name)),
        ("cpp", cpp_functions, snake(name)),
        ("go", go_methods, name),
        ("rust", rust_constructors, snake(name)),
    ):
        if spelling not in have:
            missing.append(f"{binding} cannot build {name}: no {spelling}")

if missing:
    print(f"the kernel has {len(kernel)} predicates and a binding cannot build one:")
    for line in missing:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: all {len(kernel)} kernel predicates have a builder in all 4 bindings")
PY
