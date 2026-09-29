# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The hint lens reads every hint a module or a probe holds, and judges each the same way.

A hint is imprecise when it holds ``Any`` or ``object``, a ``str``, ``int``,
``float`` or ``bytes`` anywhere, or three nested subscripts; an alias is judged
by its right side however it is spelled.  Each case below is one of those
claims, or one of the forms a precise hint takes that the lens must pass, since
a lens that refused them would be a gate nobody could satisfy.  A probe's
Python is read wherever an interpreter is handed it, and a run the lens cannot
read fails it, so no Python goes unread.
"""

from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path
from typing import NamedTuple

import pytest

from tools._common import RelPath, find_executable
from tools._ratchet import CanonicalText, RatchetRows, RowKey
from tools.check_precise_hints import (
    CLEAN,
    OUT_OF_STEP,
    UNREADABLE,
    Fault,
    LineNumber,
    Observed,
    PythonSource,
    ShellSource,
    hints_in,
    hints_of,
    in_scope,
    probe_python,
    report,
)

from aletheia.common_types import ExitStatus, Prose


def _judged(source: PythonSource) -> dict[CanonicalText, frozenset[Fault]]:
    """Map each imprecise hint of a module to its faults."""
    return {hint.text: hint.faults for hint in hints_in(source)}


@pytest.mark.parametrize(
    ("annotation", "fault"),
    [
        ("Any", Fault.UNSEEN),
        ("object", Fault.UNSEEN),
        ("typing.Any", Fault.UNSEEN),
        ("dict", Fault.UNSEEN),
        ("Callable", Fault.UNSEEN),
        ("str", Fault.PRIMITIVE),
        ("int | None", Fault.PRIMITIVE),
        ("list[float]", Fault.PRIMITIVE),
        ("dict[str, Path]", Fault.PRIMITIVE),
        ("dict[Path, bytes]", Fault.PRIMITIVE),
        ("Callable[[str], None]", Fault.PRIMITIVE),
        ("Final[int]", Fault.PRIMITIVE),
        ("list[dict[Key, list[Key]]]", Fault.NESTED),
    ],
)
def test_an_imprecise_hint_is_found_with_its_fault(annotation: CanonicalText, fault: Fault) -> None:
    """Each kind of fault, wherever in the hint it sits."""
    assert _judged(PythonSource(f"x: {annotation}\n")) == {annotation: frozenset({fault})}


@pytest.mark.parametrize(
    "annotation",
    [
        "Key",
        "list[Path]",
        "dict[Key, list[Path]]",
        'Literal["str", "int"]',
        'Annotated[Key, "int"]',
        "Key | None",
        "bool",
    ],
)
def test_a_precise_hint_passes(annotation: CanonicalText) -> None:
    """A named type, two subscripts, a Literal's values and an Annotated's note hold nothing."""
    assert _judged(PythonSource(f"x: {annotation}\n")) == {}


def test_a_quoted_hint_is_read_as_the_hint_it_quotes() -> None:
    """A forward reference is keyed and judged by the expression inside the quotes."""
    assert _judged(PythonSource('def f() -> "dict[str, Key]": ...\n')) == {
        CanonicalText("dict[str, Key]"): frozenset({Fault.PRIMITIVE})
    }
    assert _judged(PythonSource('x: list["list[list[Key]]"]\n')) == {
        CanonicalText("list['list[list[Key]]']"): frozenset({Fault.NESTED})
    }


def test_every_place_a_hint_is_written_is_read() -> None:
    """Every argument kind, the return, a field, a module variable and a nested function."""
    source = PythonSource(
        textwrap.dedent("""\
            def f(a: str, /, b: str, *c: str, d: str, **e: str) -> str:
                def g(h: str) -> str: ...
            class C:
                field: str
            async def k(m: str) -> None: ...
            n: str = 'x'
            """)
    )
    hints = hints_in(source)
    assert len(hints) == 11
    assert {hint.line for hint in hints} == {LineNumber(line) for line in (1, 2, 4, 5, 6)}


@pytest.mark.parametrize(
    "statement",
    [
        "type Pair = tuple[int, Key]",
        "Pair: TypeAlias = tuple[int, Key]",
        'Pair = TypeAliasType("Pair", tuple[int, Key])',
        'Pair = TypeAliasType("Pair", value=tuple[int, Key])',
        "Pair = tuple[int, Key]",
    ],
)
def test_an_alias_is_judged_by_its_right_side_however_it_is_spelled(
    statement: PythonSource,
) -> None:
    """Every spelling is keyed the one way."""
    assert _judged(PythonSource(statement + "\n")) == {
        CanonicalText("type Pair = tuple[int, Key]"): frozenset({Fault.PRIMITIVE})
    }


def test_the_type_a_cast_names_is_a_hint() -> None:
    """A cast asserts a type the checker then trusts, so it is judged, quoted or not."""
    source = PythonSource(
        "x = cast('dict[str, Key]', y)\n"
        + "z = typing.cast(list[Key], y)\n"
        + "w = cast(typ=object, val=y)\n"
    )
    assert _judged(source) == {
        CanonicalText("dict[str, Key]"): frozenset({Fault.PRIMITIVE}),
        CanonicalText("object"): frozenset({Fault.UNSEEN}),
    }


def test_a_newtype_over_a_shape_is_judged_by_the_shape() -> None:
    """A NewType renames a shape without narrowing it; over a name it is the fix."""
    assert _judged(PythonSource("Rows = NewType('Rows', dict[str, Key])\n")) == {
        CanonicalText("NewType('Rows', dict[str, Key])"): frozenset({Fault.PRIMITIVE})
    }


def test_a_value_assigned_at_module_level_is_not_an_alias() -> None:
    """A subscript of a table, a union of flags and a union of names naming nothing primitive."""
    assert _judged(PythonSource("VALUE = table[3]\nFLAGS = A | B\nPair = Key | Path\n")) == {}
    assert _judged(PythonSource("Key = NewType('Key', str)\n")) == {}


_PROBE = ShellSource("""\
#!/usr/bin/env bash
py=python/.venv/bin/python
"$py" - "$arg" << 'EOF'
def run(a: str) -> None:
    print('"$py" -c is text here, not a run')
EOF
cat << 'DATA'
"$py" -c 'data, not a run'
DATA
"$py" -c 'def k(z: int): pass'
value=$("$py" -c "print(len('$base'))")
""")


def test_a_probe_hands_its_interpreter_heredocs_and_inline_python() -> None:
    """Each run's Python is read; a data heredoc and text quoted in Python are not runs."""
    pieces = probe_python(_PROBE)
    assert not isinstance(pieces, str)
    assert [piece.line for piece in pieces] == [LineNumber(4), LineNumber(10), LineNumber(11)]
    assert pieces[2].source == "print(len('$base'))"


def test_a_probe_hint_carries_the_probe_line_it_stands_on() -> None:
    """Line numbers are the probe's, so a diagnostic points into the file under edit."""
    hints = hints_of(RelPath("probes/x.sh"), _PROBE)
    assert not isinstance(hints, str)
    assert [(hint.text, hint.line) for hint in hints] == [
        (CanonicalText("str"), LineNumber(4)),
        (CanonicalText("int"), LineNumber(10)),
    ]


@pytest.mark.parametrize(
    "probe",
    [
        '"$py" - < script.py\n',
        'printf "%s" "$code" | python3 -\n',
    ],
)
def test_python_handed_in_a_form_the_lens_cannot_read_fails_it(probe: ShellSource) -> None:
    """A run the lens cannot read is an error, never Python skipped."""
    assert isinstance(probe_python(probe), str)


def test_a_heredoc_that_never_ends_fails_the_lens() -> None:
    """An unterminated heredoc is reported, never read to the end of the file."""
    assert isinstance(probe_python(ShellSource("\"$py\" - << 'EOF'\nx: str\n")), str)


def test_python_that_does_not_parse_is_reported_with_its_file() -> None:
    """A syntax error names the file and the line."""
    result = hints_of(RelPath("tools/broken.py"), PythonSource("def f(:\n"))
    assert isinstance(result, str)
    assert result.startswith("tools/broken.py: line 1")


@pytest.mark.parametrize(
    "rel", [RelPath("tools/x.py"), RelPath("python/tests/test_x.py"), RelPath("probes/x--y.sh")]
)
def test_the_lens_reads_python_outside_the_archive_and_every_probe(rel: RelPath) -> None:
    """Every tracked Python file but the archive's is read, and every probe."""
    assert in_scope(rel)


@pytest.mark.parametrize(
    "rel",
    [RelPath("tools/build_python.sh"), RelPath(".archive/reviews/x.py"), RelPath("docs/X.md")],
)
def test_the_lens_leaves_the_archive_and_other_shell_scripts(rel: RelPath) -> None:
    """History, a shell script that is not a probe, and prose are not read."""
    assert not in_scope(rel)


def _observed(rows: RatchetRows) -> Observed:
    """Stand for a tree holding exactly ``rows``."""
    return Observed(
        rows,
        {key: [LineNumber(1)] * count for key, count in rows.items()},
        {key: frozenset({Fault.PRIMITIVE}) for key in rows},
    )


_ROW = RowKey(RelPath("tools/x.py"), CanonicalText("str"))
_OTHER = RowKey(RelPath("tools/y.py"), CanonicalText("int"))


def test_a_hint_the_record_does_not_allow_fails_the_gate() -> None:
    """One more of a recorded hint than the record allows is a rise."""
    assert report(_observed({_ROW: 2}), {_ROW: 1}) == OUT_OF_STEP
    assert report(_observed({_ROW: 1}), {_ROW: 1}) == CLEAN


def test_a_row_naming_more_than_the_file_holds_fails_the_gate() -> None:
    """A stale row is standing permission to write the hint back."""
    assert report(_observed({_ROW: 1}), {_ROW: 2}) == OUT_OF_STEP


def test_one_file_under_edit_is_held_to_its_rows_alone() -> None:
    """A fall in the file, or anything in another file, is not the edit's to refuse."""
    files = {_ROW.file}
    assert report(_observed({_ROW: 1}), {_ROW: 2, _OTHER: 1}, files=files) == CLEAN
    assert report(_observed({_ROW: 3}), {_ROW: 2}, files=files) == OUT_OF_STEP


_REPO = Path(__file__).resolve().parents[2]


class _GateRun(NamedTuple):
    """What the gate answered over another tree: its exit status, and what it printed."""

    status: ExitStatus
    output: Prose


def _gate_over(root: Path, record: Path | None) -> _GateRun:
    """Run the gate from this repository over another tree, with its record where one is given."""
    held = ["--root", str(root)] + (["--record", str(record)] if record is not None else [])
    run = subprocess.run(
        [sys.executable, "-m", "tools.check_precise_hints", *held],
        cwd=_REPO,
        capture_output=True,
        text=True,
        check=False,
        env={"PATH": "/usr/bin:/bin", "HOME": str(root)},
    )
    return _GateRun(ExitStatus(run.returncode), Prose(run.stdout))


def test_another_tree_is_held_to_its_own_record(tmp_path: Path) -> None:
    """--root and --record judge every tracked file under another tree, keyed from its root."""
    git = find_executable("git")
    _ = subprocess.run([git, "init", "-q", str(tmp_path)], check=True)
    _ = (tmp_path / "kit.py").write_text("def f(a: str) -> None: ...\n")
    _ = subprocess.run([git, "-C", str(tmp_path), "add", "kit.py"], check=True)
    record = tmp_path / "RECORD.yaml"
    _ = record.write_text("hints: []\n")
    refused = _gate_over(tmp_path, record)
    assert refused.status == OUT_OF_STEP
    assert "file: kit.py" in refused.output
    _ = record.write_text('hints:\n  - file: kit.py\n    text: "str"\n    count: 1\n')
    assert _gate_over(tmp_path, record).status == CLEAN


def test_a_tree_without_its_record_is_refused_before_it_is_read(tmp_path: Path) -> None:
    """--root and --record come together; one alone is an error, never the repository's record."""
    assert _gate_over(tmp_path, None).status == UNREADABLE
