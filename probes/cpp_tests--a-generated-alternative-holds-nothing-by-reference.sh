#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes every tracked source under cpp/tests.
# Claim: no value a Catch2 generator serves captures anything by reference.
# A generator is built once, on the first entry of its test body, and serves
# its values on the later entries, each of them a fresh frame; the values
# outlive the frame they were built in, so a reference into that frame reads
# a returned frame on every entry after the first. The address sanitizer is
# the only instrument that says so, and nothing in the suite's own run does.
# GENERATE_REF binds its whole list that way by construction and is refused
# for the same reason.
# What it reads is the argument list itself, which leaves it two blind spots:
# a lambda named in the list and defined elsewhere carries its capture out of
# reach, and a by-value default inside a fixture-bound case captures that
# case's `this`, which reads here as no reference at all. The tree has no
# fixture-bound case today.
# Non-zero exit: a lambda inside a GENERATE or GENERATE_COPY argument list
# carries an ampersand in its capture list, or a GENERATE_REF is used.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
files=$(git ls-files -- 'cpp/tests/*.cpp' 'cpp/tests/*.hpp')
[ -n "$files" ] || { echo "no tracked source under cpp/tests"; exit 2; }
# shellcheck disable=SC2086
"$py" - $files <<'PYEOF'
import re
import sys

# Comments and literals are blanked in place, so a parenthesis inside a raw
# string and an ampersand inside a comment neither close an argument list nor
# read as a capture, and every offset still names its own line.
def blank(text: str) -> str:
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "//":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out[i:j] = " " * (j - i)
            i = j
        elif two == "/*":
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text.startswith('R"', i):
            m = re.compile(r'R"([^(\\\s]*)\(').match(text, i)
            if m is None:
                i += 1
                continue
            close = ')' + m.group(1) + '"'
            j = text.find(close, m.end())
            j = n if j < 0 else j + len(close)
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text[i] in '"\'':
            quote = text[i]
            j = i + 1
            while j < n and text[j] != quote:
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def arg_list(text: str, open_paren: int) -> int:
    depth = 0
    for i in range(open_paren, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return i
    return -1


generator = re.compile(r"\bGENERATE(_COPY|_REF)?\s*\(")
capture = re.compile(r"\[([^]\[]*)\]\s*(\(|\{|mutable|->)")
findings = []
for path in sys.argv[1:]:
    with open(path, encoding="utf-8") as handle:
        source = handle.read()
    text = blank(source)
    for match in generator.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        if match.group(1) == "_REF":
            findings.append(f"{path}:{line}: GENERATE_REF binds its list by reference")
            continue
        end = arg_list(text, match.end() - 1)
        if end < 0:
            findings.append(f"{path}:{line}: unterminated generator argument list")
            continue
        for lam in capture.finditer(text, match.end(), end):
            if "&" in lam.group(1):
                at = text.count("\n", 0, lam.start()) + 1
                findings.append(f"{path}:{at}: capture [{lam.group(1)}] inside {match.group(0)[:-1]}")
if findings:
    print("a generated value holds a reference into the frame it was built in:")
    print("\n".join(findings))
    sys.exit(1)
PYEOF
