# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_wire_codes`` — the kernel ↔ ``docs/WIRE_CODES.yaml`` parity gate.

The gate exists because every binding deliberately passes unknown wire codes
through at runtime (the forward-compatibility channel), so a new kernel code
would otherwise reach production without any CI failure.  Per the gate-teeth
rule, every test here proves a failure mode actually fails: a phantom YAML
row, a phantom / missing kernel arm, order drift, and each vacuous-input
class (missing file, zero parsed codes, malformed YAML) all exit non-zero.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_wire_codes import collect_arm_literals, compare_vocabulary, main

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

YAML_MATCHING = """\
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


def _write_agda_tree(tmp_path: Path) -> Path:
    """Create a minimal Agda root carrying both vocabulary sources."""
    agda_root = tmp_path / "src"
    protocol_dir = agda_root / "Aletheia" / "Protocol"
    protocol_dir.mkdir(parents=True)
    _ = (protocol_dir / "ResponseFormat.agda").write_text(RESPONSE_FORMAT_SNIPPET, encoding="utf-8")
    _ = (agda_root / "Aletheia" / "Error.agda").write_text(ERROR_SNIPPET, encoding="utf-8")
    return agda_root


def _write_yaml(tmp_path: Path, content: str = YAML_MATCHING) -> Path:
    """Write a WIRE_CODES.yaml fixture and return its path."""
    yaml_path = tmp_path / "WIRE_CODES.yaml"
    _ = yaml_path.write_text(content, encoding="utf-8")
    return yaml_path


def _run(monkeypatch: pytest.MonkeyPatch, agda_root: Path, yaml_path: Path) -> int:
    """Invoke the gate's ``main`` against the fixture tree via its DI seams."""
    monkeypatch.setattr(
        "sys.argv",
        ["check_wire_codes", "--agda-root", str(agda_root), "--yaml", str(yaml_path)],
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
    assert any("'c'" in d and "no kernel formatter arm" in d for d in diffs)


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
    """TEETH: a missing kernel source is COULD-NOT-CHECK (exit 2)."""
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
    """TEETH: a row without a description violates the schema — exit 2."""
    yaml_path = _write_yaml(
        tmp_path,
        YAML_MATCHING.replace("    description: The operation requires a loaded DBC.\n", ""),
    )
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 2


def test_duplicate_yaml_row_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a duplicated YAML row fails — set comparison must not mask it."""
    yaml_path = _write_yaml(
        tmp_path,
        YAML_MATCHING + "  - name: handler_no_dbc\n    description: Duplicate row.\n",
    )
    assert _run(monkeypatch, _write_agda_tree(tmp_path), yaml_path) == 1
    assert "duplicate" in capsys.readouterr().err
