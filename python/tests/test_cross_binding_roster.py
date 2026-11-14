# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every Go cross-binding case has its sibling in the C++ and the Python trees.

AGENTS/go.md cat 33(d) makes a case one binding carries and another lacks a
finding, and the siblings are scattered across files, so a case deleted or
renamed in one tree leaves the other two saying nothing.  The roster below is
the one table that reads the three trees together: one row per Go case of
``go/aletheia/cross_binding_integration_test.go``, naming the C++ case (a
``TEST_CASE`` title, matched as text) and the Python test that assert the same
thing.  A Go case the roster does not name fails too, so a new case cannot be
added without saying where its siblings are.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Final, NamedTuple, NewType

import pytest

from aletheia.common_types import Prose

_REPO_ROOT: Final = Path(__file__).resolve().parents[2]
_GO_FILE: Final = _REPO_ROOT / "go" / "aletheia" / "cross_binding_integration_test.go"
_CPP_CROSS: Final = Path("cpp/tests/test_cross_binding_integration.cpp")
_CPP_INTEGRATION: Final = Path("cpp/tests/integration_tests.cpp")
_CPP_GEOMETRY: Final = Path("cpp/tests/integration_tests_geometry.cpp")
_PY_CROSS: Final = Path("python/tests/test_cross_binding_integration.py")
_PY_BOUNDS: Final = Path("python/tests/test_input_bounds.py")
_PY_TEXT: Final = Path("python/tests/test_parse_dbc_text.py")

# A Go test function's name, a C++ TEST_CASE title and a Python test function's name.
GoCase = NewType("GoCase", str)
CppCase = NewType("CppCase", str)
PyCase = NewType("PyCase", str)


class Siblings(NamedTuple):
    """One Go case and where its C++ and Python siblings stand."""

    go_case: GoCase
    cpp_file: Path
    cpp_case: CppCase
    py_file: Path
    py_case: PyCase


_ROSTER: Final = (
    Siblings(
        GoCase("TestCrossBinding_ParseDBCResponseShape"),
        _CPP_CROSS,
        CppCase("ParsedDBC response has documented shape"),
        _PY_CROSS,
        PyCase("test_parse_dbc_response_shape"),
    ),
    Siblings(
        GoCase("TestCrossBinding_ValidateDBCResponseShape"),
        _CPP_CROSS,
        CppCase("ValidationResult response has documented shape"),
        _PY_CROSS,
        PyCase("test_validate_dbc_response_shape"),
    ),
    Siblings(
        GoCase("TestCrossBinding_SendFrameAck"),
        _CPP_CROSS,
        CppCase("send_frame ack response has documented shape"),
        _PY_CROSS,
        PyCase("test_send_frame_ack_response_shape"),
    ),
    Siblings(
        GoCase("TestCrossBinding_SendFrameViolation"),
        _CPP_CROSS,
        CppCase("send_frame violation response has documented shape"),
        _PY_CROSS,
        PyCase("test_send_frame_violation_response_shape"),
    ),
    Siblings(
        GoCase("TestCrossBinding_SendFrameMultiEvent"),
        _CPP_CROSS,
        CppCase("send_frame multi-event batch"),
        Path("python/tests/test_classify_satisfied_complete.py"),
        PyCase("test_multi_event_frame_satisfaction_plus_violation"),
    ),
    Siblings(
        GoCase("TestCrossBinding_CANIDRefusedAtTheTypeBoundary"),
        _CPP_CROSS,
        CppCase("invalid CAN ID is rejected at type boundary"),
        _PY_CROSS,
        PyCase("test_send_frame_error_response_shape"),
    ),
    Siblings(
        GoCase("TestCrossBinding_SendFrameBrsEsiPassthrough"),
        _CPP_CROSS,
        CppCase("send_frame with BRS / ESI passthrough"),
        Path("python/tests/test_unified_client_canfd_mux.py"),
        PyCase("test_canfd_brs_esi_passthrough"),
    ),
    Siblings(
        GoCase("TestCrossBinding_IdentifierAtMaxLengthAccepted"),
        _CPP_CROSS,
        CppCase("identifier at max length is accepted"),
        _PY_BOUNDS,
        PyCase("test_identifier_at_max_length_accepted"),
    ),
    Siblings(
        GoCase("TestCrossBinding_IdentifierOverMaxRejected"),
        _CPP_CROSS,
        CppCase("identifier over max length is rejected"),
        _PY_BOUNDS,
        PyCase("test_identifier_over_max_rejected_where_it_starts"),
    ),
    Siblings(
        GoCase("TestCrossBinding_GeometryGateRefusesOutOfFrameStartBit"),
        _CPP_GEOMETRY,
        CppCase("out-of-frame start bit"),
        _PY_TEXT,
        PyCase("test_text_route_refuses_out_of_frame_start_bit"),
    ),
    Siblings(
        GoCase("TestCrossBinding_MotorolaFullFrameClosure"),
        _CPP_GEOMETRY,
        CppCase("text-loaded Motorola full-frame signal is accepted back by the JSON route"),
        _PY_TEXT,
        PyCase("test_text_loaded_motorola_rounds_through_json_surface"),
    ),
    Siblings(
        GoCase("TestCrossBinding_NestingDepthLiftsToInputBoundExceeded"),
        _CPP_CROSS,
        CppCase("nesting depth over limit lifts to InputBoundExceeded"),
        _PY_BOUNDS,
        PyCase("test_nested_at_depth_63_rejected"),
    ),
    Siblings(
        GoCase("TestCrossBinding_BinaryExtractionReasonParity"),
        _CPP_INTEGRATION,
        CppCase("binary extraction decodes values, wire reasons, and absent exactly"),
        Path("python/tests/test_binary_extraction.py"),
        PyCase("test_known_code_surfaces_wire_reason_verbatim"),
    ),
    Siblings(
        GoCase("TestCrossBinding_ExtractionWireRangeRefusalBothPaths"),
        _CPP_INTEGRATION,
        CppCase("binary and JSON extraction refuse a value whose component is past the wire range"),
        Path("python/tests/test_extraction_wire_range.py"),
        PyCase("test_both_components_past_the_bound_refused_on_both_paths"),
    ),
)

_GO_CASE: Final = re.compile(r"^func (TestCrossBinding_\w+)\(", re.MULTILINE)


def _missing(row: Siblings) -> list[Prose]:
    """Each sibling of ``row`` its tree does not hold, one line each."""
    found: list[Prose] = []
    if not re.search(rf"^func {row.go_case}\(", _GO_FILE.read_text(encoding="utf-8"), re.MULTILINE):
        found.append(Prose(f"{row.go_case}: not in {_GO_FILE.relative_to(_REPO_ROOT)}"))
    if row.cpp_case not in (_REPO_ROOT / row.cpp_file).read_text(encoding="utf-8"):
        found.append(
            Prose(f'{row.go_case}: its C++ sibling "{row.cpp_case}" is not in {row.cpp_file}')
        )
    if not re.search(
        rf"def {row.py_case}\(", (_REPO_ROOT / row.py_file).read_text(encoding="utf-8")
    ):
        found.append(
            Prose(f"{row.go_case}: its Python sibling {row.py_case} is not in {row.py_file}")
        )
    return found


@pytest.mark.parametrize("row", _ROSTER, ids=[row.go_case for row in _ROSTER])
def test_every_roster_case_has_its_siblings(row: Siblings) -> None:
    """The Go case, its C++ case and its Python test each stand where the roster says."""
    missing = _missing(row)
    assert not missing, missing


def test_every_go_case_is_in_the_roster() -> None:
    """A Go cross-binding case the roster does not name has no siblings anyone checks."""
    named = {row.go_case for row in _ROSTER}
    cases = [GoCase(name) for name in _GO_CASE.findall(_GO_FILE.read_text(encoding="utf-8"))]
    assert cases, f"{_GO_FILE} holds no TestCrossBinding_ case, so the roster checks nothing"
    unnamed = [case for case in cases if case not in named]
    assert not unnamed, unnamed
