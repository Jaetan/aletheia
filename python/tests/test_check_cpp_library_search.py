# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The library-search gate: one candidate list, in the search, and every caller calls it."""

from __future__ import annotations

from tools._common import RelPath
from tools._hosted_markdown import SourceText
from tools.check_cpp_library_search import CALLERS, SEARCH, scan_file

_OTHER = RelPath("cpp/src/other.cpp")
_CANDIDATE = SourceText('auto const p = "../build/libaletheia-ffi.so";\n')


def test_a_path_literal_outside_the_search_is_refused_on_its_line() -> None:
    """A candidate in another source is a second search."""
    findings = scan_file(_OTHER, SourceText("int x;\n" + _CANDIDATE))
    assert len(findings) == 1, findings
    assert findings[0].startswith("cpp/src/other.cpp:2: "), findings


def test_the_search_holds_the_candidates() -> None:
    """The search's own candidate list is the one allowed."""
    assert not scan_file(SEARCH, _CANDIDATE)


def test_a_message_naming_the_library_is_not_a_candidate() -> None:
    """A literal holding whitespace is a message, not a path."""
    text = SourceText('fail("library path is empty: pass the path of libaletheia-ffi.so");\n')
    assert not scan_file(_OTHER, text)


def test_a_caller_not_calling_the_search_is_refused() -> None:
    """A caller whose code never calls the search is named; a comment naming it is no call."""
    findings = scan_file(CALLERS[0], SourceText("// find_ffi_library() is called elsewhere\n"))
    assert findings == [f"{CALLERS[0]}: does not call find_ffi_library, the binding's one search"]


def test_a_caller_calling_the_search_passes() -> None:
    """The call is what the arm reads."""
    assert not scan_file(CALLERS[0], SourceText("auto const lib = aletheia::find_ffi_library();\n"))
