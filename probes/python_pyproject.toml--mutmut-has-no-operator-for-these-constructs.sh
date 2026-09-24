#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes python/pyproject.toml, its pinned mutmut, against the Python lane's
# refusals.
# Claim: the pinned mutmut has no operator for a return statement, a raise, a
# condition that is a bare name or call, an f-string, a for loop or a with
# block, and it skips a function under a decorator other than staticmethod or
# classmethod whole, so a defect in any of those is one the Python lane cannot
# see and the record has to say so rather than count them as swept. Shown by
# handing mutmut's own operator table a function written from those constructs
# alone and counting the mutations it yields, which must be zero, while the
# same table over a comparison yields one, so the table is the one the lane
# runs. Non-zero exit: mutmut now mutates one of them, which re-opens the
# refusal, or the control yields nothing. Exits 0 with a note without the
# venv's mutmut, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" -c 'import mutmut' 2> /dev/null || { echo "mutmut not installed in the venv, claim untestable"; exit 0; }
cd python && "$py" - <<'PY'
import libcst as cst
from libcst.metadata import MetadataWrapper
from mutmut.mutation.file_mutation import MutationVisitor
from mutmut.mutation.mutators import mutation_operators
from mutmut.mutation.pragma_handling import IgnoredCode

def mutations(source):
    visitor = MutationVisitor(mutation_operators, IgnoredCode(set(), set(), set()))
    MetadataWrapper(cst.parse_module(source)).visit(visitor)
    return visitor.mutations

refused = '''
def f(items, flag, error):
    for item in items:
        with error:
            if flag:
                raise error
    return f"bad {item}"

@property
def g(self):
    return self.x < self.y
'''
control = '''
def h(a, b):
    return a < b
'''
made = mutations(refused)
status = 0
if made:
    for m in made:
        print("mutmut now mutates:", cst.Module([]).code_for_node(m.original_node).strip()[:60])
    status = 1
if not mutations(control):
    print("the control comparison yields no mutation, so the table is not the one the lane runs"); status = 1
if status == 0:
    print("PASS: no mutation for the refused constructs, and the control comparison yields one")
raise SystemExit(status)
PY
