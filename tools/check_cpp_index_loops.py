# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Refuse a C++ counting loop that ``docs/CPP_INDEX_LOOPS.yaml`` does not already name.

AGENTS/cpp.md cat 27, "no index where a range will do": a loop that counts an
index and subscripts with it states its own bound, and a bound written by hand
can be written wrong, where the same traversal expressed as a range is bounded
by the range itself.  The failure mode is quiet.  A wrong bound reads one past
the end, which the standard library catches only where its container assertions
are compiled in, and the optimised build leaves them out, so such a bound is
found by mutation testing rather than by a test, and only where a fixture
happens to reach the row past the end.

``modernize-loop-convert`` does not cover the class.  It rewrites a loop only
where the index does nothing but subscript one container, which is exactly the
case where no bound is written by hand, so clang-tidy is silent on the loops
that can be wrong.  This gate is what covers them instead.

It is a ratchet, not a ban: the YAML records the counting loops the tree has
today so that a new one fails, and a row leaves the file by the change that
rewrites its loop.  Both directions are enforced, and both have to be, because
a row whose loop is gone is standing permission to reintroduce it:

* a counting loop the YAML does not name fails the gate, which prints the row
  that would allow it.  Adding that row needs user approval, on the same footing
  as a ``NOLINT`` suppression;
* a row naming more loops than the tree holds fails the gate, which prints the
  row to delete.  The change that rewrites a loop deletes its row.

A loop is a counting loop when a variable of its header is stepped (``++``,
``--``, ``+=``, ``-=``, or assigned its own sum or difference) in the condition,
in the increment clause, or in the body: a three-clause ``for`` whose init
declares the variable, and a ``while``
or ``do``/``while`` where any name the condition tests is the one stepped.  All
three spellings are read, because a gate that knew only ``for`` would be passed
by rewriting the header.  Reading the body is what separates the two shapes that
leave the increment clause empty: a scan advancing its index by a variable
amount per turn is a counting loop wherever the step is written, and a loop
draining a stream into a length is not one at all.

Rows are keyed by file and by the loop header's canonical text rather than by a
line number, so an edit elsewhere in the file does not churn the YAML; where one
file holds several identical headers the row carries how many, as the mutation
lane's survivor ledger does.

Run: ``python -m tools.check_cpp_index_loops`` (exit 0 = clean, 1 = violations).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import NamedTuple, NewType

from tools._common import (
    emit,
    git_ls_files,
    git_toplevel,
    match_paren_content,
)
from tools._ratchet import CanonicalText, RatchetRows, RowKey, as_row, read_ratchet_rows

# One clause of a three-clause `for` header: its init, its condition or its
# increment, as `for_clauses` cut it; nothing else mints one.
Clause = NewType("Clause", str)


class Found(NamedTuple):
    """A counting loop the scan found: where its keyword starts, and its header."""

    offset: int
    header: CanonicalText


class FoundDo(NamedTuple):
    """A counting ``do``/``while``: the ``do``, the ``while`` that closes it, and the header.

    The condition offset is what lets the plain-``while`` scan leave that
    ``while`` alone: it is the tail of a ``do``, not a loop of its own.
    """

    offset: int
    condition: int
    header: CanonicalText


class Block(NamedTuple):
    """A braced block, and the offset just past its closing brace."""

    text: str
    end: int


# The ratchet's record, repo-root-relative.
ALLOWLIST = Path("docs") / "CPP_INDEX_LOOPS.yaml"

# What the gate reads.  AGENTS/cpp.md scopes the C++ standards to every source,
# header and test file under cpp/, so the gate reads the same set: a new
# counting loop in a test or a benchmark is one the rule covers too.
CPP_ROOT = "cpp"
CPP_SUFFIXES = (".cpp", ".hpp", ".h", ".cc")

# A variable being stepped, in the condition or the increment clause.
_STEP = re.compile(r"\+\+|--|\+=|-=")
_FOR = re.compile(r"\bfor\s*\(")
_WHILE = re.compile(r"\bwhile\s*\(")
_DO = re.compile(r"\bdo\s*\{")
_IDENT = re.compile(r"[A-Za-z_]\w*")

# init, condition, increment: what a counting loop's header carries and a
# range-based one does not.
_FOR_CLAUSE_COUNT = 3

# Non-code runs, replaced by blanks of their own length so that every offset
# into the blanked text still indexes the original.  Raw strings come first:
# their delimiter makes the inner quotes and backslashes ordinary characters,
# so a later pattern would otherwise cut one short.
_NONCODE = re.compile(
    r"""R"([^()\\\s]{0,16})\((?s:.)*?\)\1"      # raw string literal
      | /\*(?s:.)*?\*/                          # block comment
      | //[^\n]*                                # line comment
      | "(?:[^"\\\n]|\\(?s:.))*"                # string literal
      | '(?:[^'\\\n]|\\(?s:.))*'                # character literal
    """,
    re.VERBOSE,
)


def blank_digit_separators(text: str) -> str:
    """Blank every apostrophe that separates digits, so none can open a literal.

    An apostrophe is a separator when both its neighbours are identifier
    characters and the identifier run to its left begins with a digit, which is
    what tells ``1'000`` from the encoding prefix in ``u8'a'``.  Read as a
    quote instead, a separator opens a literal running to the next apostrophe,
    and every loop in that span disappears from the scan.  The tree states the
    same rule in C++, in the feature-matrix parity test's own lexer.
    """
    out = list(text)
    for index, char in enumerate(text):
        if char != "'" or index == 0 or index + 1 >= len(text):
            continue
        if not (_is_ident_char(text[index - 1]) and _is_ident_char(text[index + 1])):
            continue
        start = index
        while start > 0 and _is_ident_char(text[start - 1]):
            start -= 1
        if text[start].isdigit():
            out[index] = " "
    return "".join(out)


def _is_ident_char(char: str) -> bool:
    """Say whether ``char`` can appear inside an identifier or a number."""
    return char.isalnum() or char == "_"


def blank_noncode(text: str) -> str:
    """Return ``text`` with comments and literals blanked, every offset preserved.

    Newlines inside a blanked run are kept so that the blanked text still has
    the line structure of the original; everything else becomes a space.  The
    result is only ever scanned, never reported: a header's text is read back
    out of the original at the offsets found here.
    """
    return _NONCODE.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), blank_digit_separators(text))


def for_clauses(header: str) -> list[Clause] | None:
    """Split a ``for`` header into its clauses, or None when it is not three-clause.

    Cuts on every ``;`` outside parentheses, angle brackets and braces, keeping
    an empty clause rather than dropping it: the reverse form
    ``for (i = n; i-- > 0;)`` carries its step in the condition and has nothing
    in the increment, and telling that from a range-based ``for`` needs the
    empty clause to survive the split.
    """
    parts: list[Clause] = []
    buf: list[str] = []
    depth = 0
    for ch in header:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == ";" and depth == 0:
            parts.append(Clause("".join(buf)))
            buf = []
        else:
            buf.append(ch)
    parts.append(Clause("".join(buf)))
    return parts if len(parts) == _FOR_CLAUSE_COUNT else None


def init_variable(clause: str) -> str | None:
    """Name the variable an init clause declares, or None when it declares none.

    The name is the last identifier before the initialiser, which is where a
    declaration puts it whatever the type in front: ``std::size_t i = 0`` and
    ``auto const* p = q`` both answer their own variable.
    """
    names = re.findall(r"[A-Za-z_]\w*", clause.split("=", 1)[0])
    return names[-1] if names else None


def body_after(code: str, end: int) -> str:
    """Return the loop body that follows a header ending at ``end``.

    A braced body runs to its matching brace; an unbraced one is the single
    statement up to the next semicolon.  ``code`` is blanked text, so a brace
    or a semicolon inside a comment or a literal cannot cut the body short.
    """
    start = end
    while start < len(code) and code[start].isspace():
        start += 1
    if start >= len(code):
        return ""
    if code[start] != "{":
        stop = code.find(";", start)
        return code[start:] if stop < 0 else code[start : stop + 1]
    depth = 0
    for index in range(start, len(code)):
        if code[index] == "{":
            depth += 1
        elif code[index] == "}":
            depth -= 1
            if depth == 0:
                return code[start : index + 1]
    return code[start:]


def steps_variable(text: str, name: str) -> bool:
    """Say whether ``text`` steps the variable ``name``.

    A step is an increment or decrement operator on the name, a compound
    assignment, or the name assigned its own sum or difference, ``i = i + 1``,
    which is the spelling that would pass a gate reading only the operators.
    """
    word = re.escape(name)
    operators = rf"(?:\+\+|--)\s*\b{word}\b|\b{word}\s*(?:\+\+|--|\+=|-=)"
    own_sum = rf"\b{word}\s*=\s*{word}\s*[+-]"
    return re.search(f"{operators}|{own_sum}", text) is not None


def is_counting_loop(clauses: list[Clause], body: str) -> bool:
    """Say whether a three-clause ``for`` steps its variable, in the header or the body."""
    if _STEP.search(clauses[1]) or _STEP.search(clauses[2]):
        return True
    name = init_variable(clauses[0])
    return name is not None and any(steps_variable(part, name) for part in (*clauses[1:], body))


def condition_is_counted(condition: str, body: str) -> bool:
    """Say whether a name the condition tests is stepped, in the condition or the body.

    This is what makes a ``while`` a counting loop: nothing declares the
    variable in the header, so every name the condition reads is a candidate
    and one of them being stepped is the step the loop runs on.  A loop whose
    condition tests something it never steps, a flag or a queue's emptiness,
    answers no.
    """
    return any(
        steps_variable(condition, name) or steps_variable(body, name)
        for name in set(_IDENT.findall(condition))
    )


def canonical(keyword: str, parts: list[Clause]) -> CanonicalText:
    """Render a loop header as the one text a row is keyed by.

    Whitespace is collapsed and the clauses are rejoined, so reflowing a long
    header across lines, which clang-format does on its own, does not move the
    loop to a different row.
    """
    joined = "; ".join(" ".join(part.split()) for part in parts)
    return CanonicalText(f"{keyword} ({joined})")


def block_after(code: str, start: int) -> Block | None:
    """Return the braced block starting at or after ``start``, and the offset past it."""
    index = start
    while index < len(code) and code[index].isspace():
        index += 1
    if index >= len(code) or code[index] != "{":
        return None
    depth = 0
    for stop in range(index, len(code)):
        if code[stop] == "{":
            depth += 1
        elif code[stop] == "}":
            depth -= 1
            if depth == 0:
                return Block(code[index : stop + 1], stop + 1)
    return None


def for_loops(text: str, code: str) -> list[Found]:
    """Find every counting ``for``."""
    found: list[Found] = []
    for match in _FOR.finditer(code):
        header = match_paren_content(code, match.end())
        if header is None:
            continue
        clauses = for_clauses(text[match.end() : match.end() + len(header)])
        if clauses is None:
            continue
        if is_counting_loop(clauses, body_after(code, match.end() + len(header) + 1)):
            found.append(Found(match.start(), canonical("for", clauses)))
    return found


def do_loops(text: str, code: str) -> list[FoundDo]:
    """Find every counting ``do``/``while``."""
    found: list[FoundDo] = []
    for match in _DO.finditer(code):
        block = block_after(code, match.end() - 1)
        if block is None:
            continue
        body, after = block
        rest = code[after:]
        tail = _WHILE.match(code, after + len(rest) - len(rest.lstrip()))
        if tail is None:
            continue
        condition = match_paren_content(code, tail.end())
        if condition is None:
            continue
        original = text[tail.end() : tail.end() + len(condition)]
        if condition_is_counted(original, body):
            found.append(
                FoundDo(match.start(), tail.start(), canonical("do ... while", [Clause(original)]))
            )
    return found


def while_loops(text: str, code: str, skip: set[int]) -> list[Found]:
    """Find every counting ``while``, skipping the conditions that close a ``do``."""
    found: list[Found] = []
    for match in _WHILE.finditer(code):
        if match.start() in skip:
            continue
        condition = match_paren_content(code, match.end())
        if condition is None:
            continue
        body = body_after(code, match.end() + len(condition) + 1)
        original = text[match.end() : match.end() + len(condition)]
        if condition_is_counted(original, body):
            found.append(Found(match.start(), canonical("while", [Clause(original)])))
    return found


def loops_in(text: str) -> list[CanonicalText]:
    """Return the canonical text of every counting loop in one translation unit."""
    code = blank_noncode(text)
    dos = do_loops(text, code)
    found = for_loops(text, code) + [Found(done.offset, done.header) for done in dos]
    found += while_loops(text, code, {done.condition for done in dos})
    return [loop.header for loop in sorted(found)]


def observed_rows(repo: Path) -> RatchetRows:
    """Count the tree's counting loops, keyed by file and canonical header text."""
    rows: RatchetRows = {}
    for rel in git_ls_files(repo, f"{CPP_ROOT}/"):
        if not rel.endswith(CPP_SUFFIXES):
            continue
        text = (repo / rel).read_text(encoding="utf-8")
        for loop in loops_in(text):
            rows[RowKey(rel, loop)] = rows.get(RowKey(rel, loop), 0) + 1
    return rows


def report(observed: RatchetRows, recorded: RatchetRows) -> int:
    """Print every unrecorded loop and every stale row; return the process exit code."""
    unrecorded = sorted(key for key, n in observed.items() if n > recorded.get(key, 0))
    stale = sorted(key for key, n in recorded.items() if n > observed.get(key, 0))
    for file, text in unrecorded:
        emit(f"{file}: a counting loop the record does not name")
        emit(f"    {text}")
        emit("  Rewrite it as a range (AGENTS/cpp.md cat 27), or, with user approval,")
        emit(f"  add this row to {ALLOWLIST}:")
        emit(as_row(file, text, observed[RowKey(file, text)]))
    for file, text in stale:
        emit(f"{file}: a recorded row names more loops than the file holds")
        emit(f"    {text}")
        emit(f"  Its loop was rewritten: drop the row from {ALLOWLIST}, or lower its count to")
        emit(f"  {observed.get(RowKey(file, text), 0)}, in the change that rewrote it.")
    if unrecorded or stale:
        emit(f"{len(unrecorded)} unrecorded, {len(stale)} stale")
        return 1
    emit(f"C++ counting loops: {sum(observed.values())}, every one recorded")
    return 0


def main() -> int:
    """Compare the tree's counting loops against the record; 0 clean, 1 violations."""
    repo = git_toplevel()
    recorded = read_ratchet_rows(repo, ALLOWLIST, "loops")
    if isinstance(recorded, str):
        emit(recorded)
        return 1
    return report(observed_rows(repo), recorded)


if __name__ == "__main__":
    sys.exit(main())
