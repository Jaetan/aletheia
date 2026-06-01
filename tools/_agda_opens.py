"""Grammar-complete detection of Agda ``open``/``import`` directives.

This is the substrate for the dead-import gate's "what does each open inject?"
question.  Unlike :func:`tools.prune_unused_imports.parse_imports` (which only
recognises top-level ``open import`` / ``import`` blocks), this module finds
*every* open the Agda grammar permits, in *every* position, and classifies it.

Grounding (Agda ``src/full/Agda/Syntax/Parser/Parser.y``):

* ``ImportDirective`` is a free combination, in any order, of ``public`` |
  ``using (names)`` | ``hiding (names)`` | ``renaming (renames)``.  Only
  ``using`` *restricts* to an enumerable list; ``hiding``/``renaming`` are
  wildcard modifiers; ``public`` is orthogonal re-export.  So **an open injects
  an enumerable set that is readable from source text iff it carries a ``using``
  clause**; every other open is a *wildcard* whose set is the opened module's
  contents (read from ``show_module_contents``), minus ``hiding`` and with
  ``renaming`` applied.

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

The unqualified-name set an open injects is :func:`provided_set`; the names a
file makes prunable (the gate's candidates) is :func:`open_check_names` — both
derived uniformly from every open, which is what makes the gate FN-complete.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, NamedTuple

from tools._common import match_paren_content, split_top_level_semicolons

if TYPE_CHECKING:
    from collections.abc import Mapping

# An imported/opened identifier, e.g. "foo", "_∷_", "module Sub".
type Name = str
# A (source, destination) renaming pair from a ``renaming (src to dst)`` clause.
type Rename = tuple[Name, Name]

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
    """Return the semicolon-split names inside ``keyword (...)``, or [] if absent."""
    match = re.search(rf"\b{keyword}\b\s*\(", directive)
    if match is None:
        return []
    inner = match_paren_content(directive, match.end())
    if inner is None:
        return []
    return split_top_level_semicolons(inner)


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
    """

    module: Name  # the QId after the keyword (for a scope query)
    is_open: bool  # injects unqualified names?
    is_import: bool  # has the ``import`` keyword (qualified module binding)?
    has_using: bool  # carries a ``using`` clause (→ enumerable from text)?
    using_names: list[Name]  # ``using (...)`` entries (may include "module X")
    hiding_names: list[Name]  # ``hiding (...)`` entries
    renaming: list[Rename]  # ``renaming (src to dst)`` pairs


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
    offsets: list[int] = []
    acc = 0
    for line in lines:
        offsets.append(acc)
        acc += len(line)
    offsets.append(acc)

    def line_index(pos: int) -> int:
        for idx in range(len(offsets) - 1):
            if offsets[idx] <= pos < offsets[idx + 1]:
                return idx
        return len(lines) - 1

    results: list[OpenInfo] = []
    for keyword_match in re.finditer(r"\b(open\s+import|open|import)\b", code):
        kw = re.sub(r"\s+", " ", keyword_match.group(1))
        is_open = kw.startswith("open")
        is_import = "import" in kw
        li = line_index(keyword_match.start())
        directive = _gather_directive(lines, offsets, li, keyword_match.end())
        results.append(_classify(directive, is_open=is_open, is_import=is_import))
    return results


def _gather_directive(lines: list[str], offsets: list[int], li: int, start: int) -> str:
    """Collect a directive: rest of its line plus indented continuation lines."""
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
    return "".join(chunks)


def _classify(directive: str, *, is_open: bool, is_import: bool) -> OpenInfo:
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
        using_names=_clause_names(modifiers, _RESTRICTING_KW) if has_using else [],
        hiding_names=_clause_names(modifiers, "hiding"),
        renaming=_renaming_pairs(modifiers),
    )


def provided_set(
    open_info: OpenInfo, module_contents: Mapping[str, list[Name]]
) -> set[Name] | None:
    """Return the unqualified names ``open_info`` injects, or None if unresolvable.

    The unified rule, by case on the directive (grammar-grounded):

    * not an open (``import M`` / ``import M as N``) → injects nothing → ``set()``.
    * has ``using`` → exactly the ``using`` entries plus the ``renaming``
      destinations, read from source text (no scope query needed).
    * otherwise a wildcard → the opened module's contents (from
      ``module_contents``, i.e. ``show_module_contents``), minus ``hiding`` and
      with ``renaming`` applied.

    Returns ``None`` when a wildcard's module is absent from ``module_contents``
    (a module defined in a local scope that a top-level scope query cannot
    resolve): the caller must treat that file conservatively (confirm every
    in-scope import), never as an empty set — that is what keeps the gate from a
    silent false negative.
    """
    if not open_info.is_open:
        return set()
    if open_info.has_using:
        return _using_names(open_info)
    if open_info.module not in module_contents:
        return None  # wildcard whose module a top-level scope query can't resolve
    base = set(module_contents[open_info.module])
    base -= set(open_info.hiding_names)
    if open_info.renaming:
        base -= {src for src, _dst in open_info.renaming}
        base |= {dst for _src, dst in open_info.renaming}
    return base


def _using_names(open_info: OpenInfo) -> set[Name]:
    """Return the names a ``using``-carrying open introduces (read from text)."""
    names = {_strip_module_prefix(n) for n in open_info.using_names}
    names |= {dst for _src, dst in open_info.renaming}
    return names


def redundant_names(opens: list[OpenInfo], module_contents: Mapping[str, list[Name]]) -> set[Name]:
    """Return ``using``-introduced names that ANOTHER open also provides.

    The redundancy half of the gate's candidate generation: a name brought in by
    ``using`` is removable if some *other* open in scope supplies it too.  This
    is decided by set membership against each other open's :func:`provided_set`
    — a scope question, no recompile — so its cost is independent of proof size
    (fast for any tree).  Membership is a *candidate* signal, not a verdict: a
    local ``where``/``let`` open supplies a name only locally, so the gate's
    confirm step (remove-and-recompile) still arbitrates every name returned.

    An *unresolvable* other open (a wildcard whose module a top-level scope query
    cannot enumerate — ``provided_set`` is None) is treated as possibly
    supplying any name, so its presence makes every using-name a candidate: the
    sound, no-false-negative fallback (confirm then decides).
    """
    provided = [provided_set(o, module_contents) for o in opens]
    out: set[Name] = set()
    for i, open_info in enumerate(opens):
        if not open_info.is_open or not open_info.has_using:
            continue
        for name in _using_names(open_info):
            for j, other_provided in enumerate(provided):
                if j != i and (other_provided is None or name in other_provided):
                    out.add(name)
                    break
    return out


def open_check_names(opens: list[OpenInfo]) -> set[Name]:
    """Return every prunable unqualified name introduced by a ``using`` clause.

    These are the gate's candidates — the names that, if unused or redundant,
    can be dropped.  Derived from *all* opens (not just top-level
    ``open import``), so an unused name in ``open Syntax using (LTL; decodeStart)``
    or a local ``where open import M using (foo)`` is flaggable.  ``renaming``
    destinations are included (the new name is what is in scope and prunable).
    """
    names: set[Name] = set()
    for open_info in opens:
        if open_info.is_open and open_info.has_using:
            names |= _using_names(open_info)
    return names
