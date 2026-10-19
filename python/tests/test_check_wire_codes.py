# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_wire_codes``: the kernel and shim ↔ ``docs/WIRE_CODES.yaml`` parity gate.

The gate exists because every binding deliberately passes unknown wire codes
through at runtime (the forward-compatibility channel), so a new kernel or shim
code would otherwise reach production without any CI failure.  Per the
gate-teeth rule, every test here proves the gate reports a failure mode: a YAML
row nothing emits, a kernel arm or a shim code with no row, a duplicate on
either side, order drift (a shim row ahead of the kernel's included), and each
vacuous-input class (a missing YAML, Agda or shim source, zero codes parsed
from the Agda or the shim source, malformed YAML).
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_wire_codes import (
    SourceText,
    collect_arm_literals,
    collect_shim_codes,
    compare_vocabulary,
    main,
)

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

# Minimal kernel snippets: two literal arms per vocabulary, plus the shapes
# the parser must skip (type signatures and delegating arms).
RESPONSE_FORMAT_SNIPPET = """\
formatIssueCode : IssueCode → String
formatIssueCode DuplicateMessageId = "duplicate_message_id"
formatIssueCode SignalOverlap      = "signal_overlap"
"""

ERROR_SNIPPET = """\
parseErrorCode : ParseError → String
parseErrorCode (MissingField _)          = "parse_missing_field"
parseErrorCode (InContext _ inner)       = parseErrorCode inner
handlerErrorCode NoDBC                   = "handler_no_dbc"
"""

# The shim's envelope writer, mkErrorJson in haskell-shim/src/AletheiaFFI/Marshal.hs,
# its line wrapped before the concatenation: the code sits in a Haskell string
# literal whose quotes are escaped.
SHIM_SNIPPET = """\
mkErrorJson :: String -> String
mkErrorJson msg =
    "{\\"status\\":\\"error\\",\\"code\\":\\"ffi_validation_error\\",\\"message\\":"
        ++ jsonString msg ++ "}"
"""

SHIM_ROW = (
    "  - name: ffi_validation_error\n    description: The shim refused an entry's arguments.\n"
)

YAML_MATCHING = (
    """\
issue_codes:
  - name: duplicate_message_id
    description: Two messages share the same CAN ID.
  - name: signal_overlap
    description: Two signals occupy overlapping bit positions.
error_codes:
  - name: parse_missing_field
    description: A required JSON field is absent.
  - name: handler_no_dbc
    description: The operation requires a loaded DBC.
"""
    + SHIM_ROW
)


def _write_agda_tree(tmp_path: Path) -> Path:
    """Create a minimal Agda root carrying both vocabulary sources."""
    agda_root = tmp_path / "src"
    protocol_dir = agda_root / "Aletheia" / "Protocol"
    protocol_dir.mkdir(parents=True)
    _ = (protocol_dir / "ResponseFormat.agda").write_text(RESPONSE_FORMAT_SNIPPET, encoding="utf-8")
    _ = (agda_root / "Aletheia" / "Error.agda").write_text(ERROR_SNIPPET, encoding="utf-8")
    _ = (tmp_path / "Marshal.hs").write_text(SHIM_SNIPPET, encoding="utf-8")
    return agda_root


def _write_yaml(tmp_path: Path, content: str = YAML_MATCHING) -> Path:
    """Write a WIRE_CODES.yaml fixture and return its path."""
    yaml_path = tmp_path / "WIRE_CODES.yaml"
    _ = yaml_path.write_text(content, encoding="utf-8")
    return yaml_path


def _run(monkeypatch: pytest.MonkeyPatch, agda_root: Path, yaml_path: Path) -> int:
    """Invoke the gate's ``main`` against the fixture tree via its DI seams.

    The shim's source sits beside the Agda root, where :func:`_write_agda_tree`
    writes it.
    """
    shim_source = agda_root.parent / "Marshal.hs"
    monkeypatch.setattr(
        "sys.argv",
        [
            "check_wire_codes",
            "--agda-root",
            str(agda_root),
            "--shim-source",
            str(shim_source),
            "--yaml",
            str(yaml_path),
        ],
    )
    return main()


def test_collect_arm_literals_skips_signatures_and_delegating_arms() -> None:
    """Only literal-RHS arms mint codes; signatures and delegations drop."""
    assert collect_arm_literals(ERROR_SNIPPET, ("parseErrorCode", "handlerErrorCode")) == [
        "parse_missing_field",
        "handler_no_dbc",
    ]


def test_compare_vocabulary_reports_both_directions() -> None:
    """A kernel-only code AND a YAML-only code both surface as divergences."""
    diffs = compare_vocabulary("issue_codes", ["a", "b"], ["b", "c"])
    assert len(diffs) == 2
    assert any("'a'" in d and "no row" in d for d in diffs)
    assert any("'c'" in d and "nothing emits it" in d for d in diffs)


def test_matching_fixture_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A YAML exactly mirroring the kernel arms exits 0."""
    assert _run(monkeypatch, _write_agda_tree(tmp_path), _write_yaml(tmp_path)) == 0


def test_real_tree_passes(monkeypatch: pytest.MonkeyPatch) -> None:
    """The gate passes against the actual repository (default paths)."""
    monkeypatch.setattr("sys.argv", ["check_wire_codes"])
    assert main() == 0


def test_phantom_yaml_row_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a YAML row no kernel arm emits must fail, naming the code."""
    yaml_path = _write_yaml(
        tmp_path,
        YAML_MATCHING + "  - name: phantom_code\n    description: Phantom.\n",
    )
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 1
    assert "phantom_code" in capsys.readouterr().err


def test_missing_kernel_arm_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a kernel arm with no YAML row must fail, naming the code."""
    agda_root = _write_agda_tree(tmp_path)
    error_agda = agda_root / "Aletheia" / "Error.agda"
    _ = error_agda.write_text(
        ERROR_SNIPPET + 'dispatchErrorCode MissingTypeField = "dispatch_missing_type_field"\n',
        encoding="utf-8",
    )
    assert _run(monkeypatch, agda_root, _write_yaml(tmp_path)) == 1
    assert "dispatch_missing_type_field" in capsys.readouterr().err


def test_order_drift_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: the same code set in a different order fails (order is promised)."""
    row_dup = (
        "  - name: duplicate_message_id\n    description: Two messages share the same CAN ID.\n"
    )
    row_overlap = (
        "  - name: signal_overlap\n    description: Two signals occupy overlapping bit positions.\n"
    )
    reordered = YAML_MATCHING.replace(row_dup + row_overlap, row_overlap + row_dup)
    assert reordered != YAML_MATCHING  # the replace really rewrote the fixture
    assert _run(monkeypatch, _write_agda_tree(tmp_path), _write_yaml(tmp_path, reordered)) == 1
    assert "order" in capsys.readouterr().err


def test_missing_yaml_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: no SSOT file = COULD-NOT-CHECK (exit 2), never a silent pass."""
    absent = tmp_path / "absent.yaml"
    assert _run(monkeypatch, _write_agda_tree(tmp_path), absent) == 2


def test_missing_agda_source_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a missing kernel source is COULD-NOT-CHECK (exit 2).

    The shim's source is written beside the absent Agda root, so the exit
    status says the gate refused the missing Agda source.
    """
    _ = _write_agda_tree(tmp_path)
    assert _run(monkeypatch, tmp_path / "no-src", _write_yaml(tmp_path)) == 2


def test_zero_parsed_codes_is_vacuous(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: an Agda source yielding zero codes (regex/layout drift) exits 2."""
    agda_root = _write_agda_tree(tmp_path)
    _ = (agda_root / "Aletheia" / "Protocol" / "ResponseFormat.agda").write_text(
        "-- no formatter arms here\n", encoding="utf-8"
    )
    assert _run(monkeypatch, agda_root, _write_yaml(tmp_path)) == 2


def test_malformed_yaml_section_exits_2(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a YAML missing one section is COULD-NOT-CHECK, not a partial pass."""
    yaml_path = _write_yaml(
        tmp_path,
        "issue_codes:\n  - name: duplicate_message_id\n    description: D.\n",
    )
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 2


def test_entry_missing_description_exits_2(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a row without a description violates the schema: exit 2."""
    yaml_path = _write_yaml(
        tmp_path,
        YAML_MATCHING.replace("    description: The operation requires a loaded DBC.\n", ""),
    )
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 2


def test_duplicate_yaml_row_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a duplicated YAML row fails; set comparison must not mask it."""
    yaml_path = _write_yaml(
        tmp_path,
        YAML_MATCHING + "  - name: handler_no_dbc\n    description: Duplicate row.\n",
    )
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 1
    assert "duplicate" in capsys.readouterr().err


def test_shim_code_repeating_a_kernel_code_is_a_duplicate() -> None:
    """TEETH: a code the shim writes that a kernel arm also emits is a duplicate.

    The emitted codes are the kernel's, then the shim's, as the gate composes
    them.  Every one has its row and the YAML lists each once, so the duplicate
    on the emitter side is the one divergence.
    """
    repeated = SHIM_SNIPPET.replace("ffi_validation_error", "handler_no_dbc")
    emitted = [
        *collect_arm_literals(ERROR_SNIPPET, ("parseErrorCode", "handlerErrorCode")),
        *collect_shim_codes(SourceText(SHIM_SNIPPET + repeated)),
    ]
    rows = ["parse_missing_field", "handler_no_dbc", "ffi_validation_error"]
    assert compare_vocabulary("error_codes", emitted, rows) == [
        "error_codes: duplicate code 'handler_no_dbc' on the emitter side"
    ]


def test_collect_shim_codes_reads_the_escaped_literal() -> None:
    """The shim's code is read out of the Haskell string literal that writes it."""
    assert collect_shim_codes(SourceText(SHIM_SNIPPET)) == ["ffi_validation_error"]


def test_missing_shim_row_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a code the shim writes with no YAML row must fail.

    The fixture differs from the matching one by that row alone, so the exit
    status says the gate read the shim's source.
    """
    yaml_path = _write_yaml(tmp_path, YAML_MATCHING.replace(SHIM_ROW, ""))
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 1


def test_shim_row_before_the_kernel_rows_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """TEETH: the shim's code follows the kernel's; a row moved ahead of them fails."""
    head = "error_codes:\n"
    moved = YAML_MATCHING.replace(SHIM_ROW, "").replace(head, head + SHIM_ROW)
    assert moved != YAML_MATCHING  # the replace really moved the row
    assert _run(monkeypatch, _write_agda_tree(tmp_path), _write_yaml(tmp_path, moved)) == 1


def test_missing_shim_source_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a missing shim source is COULD-NOT-CHECK (exit 2)."""
    agda_root = _write_agda_tree(tmp_path)
    (tmp_path / "Marshal.hs").unlink()
    assert _run(monkeypatch, agda_root, _write_yaml(tmp_path)) == 2


def test_zero_shim_codes_is_vacuous(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a shim source yielding no code (pattern or layout drift) exits 2."""
    agda_root = _write_agda_tree(tmp_path)
    _ = (tmp_path / "Marshal.hs").write_text("-- no envelope here\n", encoding="utf-8")
    assert _run(monkeypatch, agda_root, _write_yaml(tmp_path)) == 2
