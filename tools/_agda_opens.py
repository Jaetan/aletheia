# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
r"""Grammar-complete detection of Agda ``open``/``import`` directives.

This is the substrate for the IWYU gate (:mod:`tools.iwyu`, via its engine
:mod:`tools._iwyu` — both named-import and wildcard analysis): what opens exist,
and how is each classified (which names it lists explicitly, whether it is a
wildcard)?  It finds *every* open the Agda grammar permits, in *every* position
(top-level, ``where``/``let``, non-``import`` ``open M``, open-module-macro),
and classifies it — not just top-level ``open import`` / ``import`` blocks.

Grounding — Agda's concrete grammar, ``src/full/Agda/Syntax/Parser/Parser.y``
(pinned tag ``v2.8.0``, matching the Agda the build uses; BSD-2-Clause).  It is
not vendored; fetch a local, git-ignored working copy on demand with::

    curl -fsSL \
      https://raw.githubusercontent.com/agda/agda/v2.8.0/src/full/Agda/Syntax/Parser/Parser.y \
      -o .agda-reference/Parser.y

The productions that matter — ``ImportDirective`` / ``Open`` / ``ModuleName``:

* ``ImportDirective`` is a free combination, in any order, of ``public`` |
  ``using (names)`` | ``hiding (names)`` | ``renaming (renames)``.  Only
  ``using`` *restricts* to an enumerable list; ``hiding``/``renaming`` are
  wildcard modifiers; ``public`` is orthogonal re-export.  So **an open's
  individually-removable entries are readable from source text iff it carries a
  ``using`` clause** (plus any ``renaming`` destination); every other open is a
  *wildcard* over the opened module's full contents, which only a scope query
  (the ``.agdai`` reader) can enumerate — not this text-level module.

* ``ModuleName = QId`` is a single dotted token with no internal whitespace;
  ``OpenArgs`` / ``{{…}}`` / modifiers all follow whitespace.  So the module
  name is exactly the first whitespace/``(``/``{``-delimited token after the
  keyword — for *every* module expression (qualified, application ``M args``,
  record ``R r``, instance ``M {{…}}``, operator-named).

* ``Open``/``Import``/``Module``/``ModuleMacro`` are ``Declaration``s, and
  declaration blocks nest in ``where`` / ``let`` / ``private`` / ``instance`` /
  ``abstract`` / ``macro`` / ``mutual`` / ``opaque`` / record bodies.  Agda
  keywords are *reserved* (cannot be identifier parts), so a comment/string
  stripped scan for the ``open``/``import`` keyword tokens finds them all,
  regardless of nesting position.

The names a file makes *prunable* — the dead-import gate's candidates — are
:func:`open_check_names`: every ``using`` entry AND every ``renaming``
destination of a non-``public`` open.  A rename destination is prunable even
with no ``using`` clause (delete just the ``a to b`` pair).  The complementary
question — the full set a *wildcard* open injects — is not answered here: it
needs the opened module's contents, which the scope-aware ``.agdai`` reader
(:mod:`tools._iwyu`) enumerates for the IWYU tool :mod:`tools.iwyu`.
"""

from __future__ import annotations

import re
from typing import NamedTuple

from tools._common import match_paren_content, split_top_level_semicolons

# An imported/opened identifier, e.g. "foo", "_∷_", "module Sub".
type Name = str
# A (source, destination) renaming pair from a ``renaming (src to dst)`` clause.
type Rename = tuple[Name, Name]
# A half-open [start, end) char-offset span (0-based) of one open's directive.
type CharRange = tuple[int, int]
# A dotted Agda module path or alias — the key of a scope query — e.g.
# "Data.List.Properties", or an ``open module N = …`` alias "N".
type ModulePath = str

# Directive-modifier keywords (the ``ImportDirective1`` alternatives that are not
# ``public``).  Only ``using`` restricts; the scan matches them as whole tokens.
_RESTRICTING_KW = "using"


def _blank_char(out: list[str], text: str, i: int) -> None:
    """Replace ``out[i]`` with a space unless it is a newline (offset-preserving)."""
    if text[i] != "\n":
        out[i] = " "


def _eat_line_comment(out: list[str], text: str, i: int) -> int:
    """Blank a ``--`` line comment from ``i`` to end of line; return the new index."""
    while i < len(text) and text[i] != "\n":
        out[i] = " "
        i += 1
    return i


def _eat_string(out: list[str], text: str, i: int) -> int:
    """Blank a ``"…"`` string literal starting at ``i``; return the index past it."""
    n = len(text)
    out[i] = " "
    i += 1
    while i < n and text[i] != '"':
        if text[i] == "\\" and i + 1 < n:  # escape: blank both chars
            out[i] = " "
            i += 1
        if i < n:
            _blank_char(out, text, i)
        i += 1
    if i < n:
        out[i] = " "  # closing quote
        i += 1
    return i


def strip_noncode(text: str) -> str:
    """Blank out line/block comments and string/char literals, preserving offsets.

    Returns a string the same length as ``text`` with every comment and string
    character replaced by a space (newlines kept), so byte offsets and line
    numbers are unchanged but the ``open``/``import`` keyword scan never matches
    inside a comment or a string literal.  Block comments nest (Agda allows it).
    """
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if two == "{-":  # block-comment open (nests; also covers {-# pragmas #-})
            out[i] = out[i + 1] = " "
            depth += 1
            i += 2
        elif depth > 0:
            if two == "-}":
                out[i] = out[i + 1] = " "
                depth -= 1
                i += 2
            else:
                _blank_char(out, text, i)
                i += 1
        elif two == "--":
            i = _eat_line_comment(out, text, i)
        elif text[i] == '"':
            i = _eat_string(out, text, i)
        else:
            i += 1
    return "".join(out)


def _clause_names(directive: str, keyword: str) -> list[Name]:
    """Return the semicolon-split names from EVERY ``keyword (...)`` clause.

    ``ImportDirective`` is a list of ``ImportDirective1`` (Parser.y), so a single
    open may carry the same directive keyword more than once — e.g. ``using (a)
    using (b)``.  Reading only the first clause would silently drop the rest
    (a false negative), so every ``keyword (...)`` occurrence is collected.
    """
    names: list[Name] = []
    for match in re.finditer(rf"\b{keyword}\b\s*\(", directive):
        inner = match_paren_content(directive, match.end())
        if inner is not None:
            names.extend(split_top_level_semicolons(inner))
    return names


def _renaming_pairs(directive: str) -> list[Rename]:
    """Parse ``renaming (src to [fixity] dst; ...)`` into (src, dst) pairs.

    The optional ``infix``/``infixl``/``infixr`` fixity annotation before the
    destination (Agda >= 2.6.1) is skipped so ``dst`` is the bare new name.
    """
    pairs: list[Rename] = []
    for seg in _clause_names(directive, "renaming"):
        match = re.match(r"(.+?)\s+to\s+(?:infix[lr]?\s+\S+\s+)?(.+)", seg.strip())
        if match is not None:
            pairs.append((match.group(1).strip(), match.group(2).strip()))
    return pairs


class OpenInfo(NamedTuple):
    """One detected ``open``/``import`` directive and its parsed modifiers.

    ``is_open`` is True when the directive injects unqualified names (any
    ``open`` form); a bare ``import M`` / ``import M as N`` is qualified-only
    (``is_open`` False).  ``has_using`` decides text-vs-scope enumeration:
    with a ``using`` clause the injected set is read from ``using_names`` plus
    the ``renaming`` destinations; otherwise it is the opened module's contents.
    ``has_public`` flags a ``public`` re-export (the names it introduces are
    used downstream, so a per-file gate must not treat them as prunable).
    ``span`` is the directive's [start, end) char offset in the source — used to
    tell an import-clause token from a body reference.
    """

    module: Name  # the QId after the keyword (for a scope query)
    is_open: bool  # injects unqualified names?
    is_import: bool  # has the ``import`` keyword (qualified module binding)?
    has_using: bool  # carries a ``using`` clause (→ enumerable from text)?
    has_public: bool  # carries a ``public`` clause (re-export → not prunable)?
    using_names: list[Name]  # ``using (...)`` entries (may include "module X")
    hiding_names: list[Name]  # ``hiding (...)`` entries
    renaming: list[Rename]  # ``renaming (src to dst)`` pairs
    span: CharRange  # [start, end) char offset of this directive in the source


def _strip_module_prefix(name: Name) -> Name:
    """Drop a leading ``module `` from a ``using (module X)`` entry."""
    return name[len("module ") :].strip() if name.startswith("module ") else name


def find_opens(text: str) -> list[OpenInfo]:
    """Find and classify every ``open``/``import`` directive in ``text``.

    Position-independent: scans the comment/string-stripped source for the
    ``open import`` / ``open`` / ``import`` keyword tokens, so opens nested in
    ``where`` / ``let`` / ``private`` / … blocks are found too.  The directive of
    each is taken as the remainder of its logical line plus indented
    continuation lines (covering a multi-line ``using (...)``).
    """
    code = strip_noncode(text)
    lines = code.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    return [
        _open_at(lines, offsets, m) for m in re.finditer(r"\b(open\s+import|open|import)\b", code)
    ]


def _line_index(offsets: list[int], pos: int) -> int:
    """Return the index of the line containing char offset ``pos``."""
    for idx in range(len(offsets) - 1):
        if offsets[idx] <= pos < offsets[idx + 1]:
            return idx
    return len(offsets) - 2  # last line


def _open_at(lines: list[str], offsets: list[int], keyword_match: re.Match[str]) -> OpenInfo:
    """Build the OpenInfo for one matched ``open``/``import`` keyword token."""
    kw = re.sub(r"\s+", " ", keyword_match.group(1))
    li = _line_index(offsets, keyword_match.start())
    directive, end_line = _gather_directive(lines, offsets, li, keyword_match.end())
    return _classify(
        directive,
        span=(keyword_match.start(), offsets[end_line]),
        is_open=kw.startswith("open"),
        is_import="import" in kw,
    )


def _gather_directive(lines: list[str], offsets: list[int], li: int, start: int) -> tuple[str, int]:
    """Collect a directive: rest of its line plus indented continuation lines.

    Returns the directive text and the line index just past it, so the caller
    can read the directive's end char offset (``offsets[end_line]``).
    """
    chunks = [lines[li][start - offsets[li] :] if start - offsets[li] < len(lines[li]) else ""]
    base_indent = len(lines[li]) - len(lines[li].lstrip())
    j = li + 1
    while j < len(lines):
        stripped = lines[j].strip()
        indent = len(lines[j]) - len(lines[j].lstrip())
        if (
            stripped
            and indent > base_indent
            and not re.match(r"(open|import|module|record|data|postulate|infix)\b", stripped)
        ):
            chunks.append(lines[j])
            j += 1
        else:
            break
    return "".join(chunks), j


def _classify(directive: str, *, span: CharRange, is_open: bool, is_import: bool) -> OpenInfo:
    """Parse a directive's module name and modifiers into an OpenInfo."""
    dstrip = directive.lstrip()
    modifiers = directive
    if is_open and dstrip.startswith("module "):
        # open-module-macro: ``open module N <binds> = ModExpr <ImportDirective>``.
        # N is a real module alias (a scope query resolves it); the directive
        # modifiers sit AFTER the ``=``.
        after = dstrip[len("module") :].lstrip()
        name_match = re.match(r"([^\s(){};=]+)", after)
        module = name_match.group(1) if name_match else ""
        eq = directive.find("=")
        modifiers = directive[eq + 1 :] if eq >= 0 else directive
    else:
        name_match = re.match(r"\s*([^\s(){};]+)", directive)
        module = name_match.group(1) if name_match else ""
    has_using = re.search(r"\busing\b", modifiers) is not None
    return OpenInfo(
        module=module,
        is_open=is_open,
        is_import=is_import,
        has_using=has_using,
        has_public=re.search(r"\bpublic\b", modifiers) is not None,
        using_names=_clause_names(modifiers, _RESTRICTING_KW) if has_using else [],
        hiding_names=_clause_names(modifiers, "hiding"),
        renaming=_renaming_pairs(modifiers),
        span=span,
    )


def _using_names(open_info: OpenInfo) -> set[Name]:
    """Return the names ``open_info`` introduces by an *explicit* source entry.

    These are the individually-prunable names: the ``using (...)`` entries (with
    any ``module `` prefix stripped) plus every ``renaming`` destination.  A
    rename destination is prunable even with no ``using`` clause — deleting just
    the ``a to b`` pair leaves the rest of the (wildcard) open intact — so this
    is well-defined for a renaming-only open too.
    """
    names = {_strip_module_prefix(n) for n in open_info.using_names}
    names |= {dst for _src, dst in open_info.renaming}
    return names


def _has_explicit_entries(open_info: OpenInfo) -> bool:
    """Return True iff ``open_info`` injects names via an explicit source entry.

    That is: it is an ``open`` carrying a ``using`` clause or a ``renaming``
    destination — the per-name removable units.  A bare wildcard ``open import
    M`` has no such entry (its only removable unit is the whole import).
    """
    return open_info.is_open and (open_info.has_using or bool(open_info.renaming))


def _is_candidate_open(open_info: OpenInfo) -> bool:
    """Return True iff ``open_info``'s explicit entries are per-file prunable.

    A candidate open has explicit entries and is not a ``public`` re-export
    (those names are used downstream — a per-file gate must not flag them).
    """
    return _has_explicit_entries(open_info) and not open_info.has_public


def open_check_names(opens: list[OpenInfo]) -> set[Name]:
    """Return every prunable unqualified name across all opens (the gate's set).

    The names that, if unused or redundant, can be dropped: the ``using (...)``
    entries and ``renaming`` destinations of every candidate open
    (:func:`_is_candidate_open`).  Derived from *all* opens — not just top-level
    ``open import`` — so an unused name in ``open Syntax using (decodeStart)`` or
    a local ``where open import M using (foo)`` is flaggable, and a renaming-only
    ``open import M renaming (a to b)`` contributes its destination ``b``.
    ``public`` re-exports are excluded (their names are used downstream).
    """
    names: set[Name] = set()
    for open_info in opens:
        if _is_candidate_open(open_info):
            names |= _using_names(open_info)
    return names


def public_open_names(opens: list[OpenInfo]) -> set[Name]:
    """Return the prunable-shaped names introduced by a ``public`` re-export.

    These are the ``using``/``renaming`` names of ``public`` opens — reported
    (and counted as providers for duplicate detection) but never flagged as
    candidates, since removing one changes the file's exported surface and could
    break a downstream consumer the per-file gate cannot see.
    """
    names: set[Name] = set()
    for open_info in opens:
        if _has_explicit_entries(open_info) and open_info.has_public:
            names |= _using_names(open_info)
    return names
