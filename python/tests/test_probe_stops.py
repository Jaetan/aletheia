# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A probe that cannot reach its claim exits 2, never 0.

``probes/README.md``: a probe exits 2 when a build, a tool or a library it needs is
missing, and the runner reads it as UNRUN; a probe that exits 0 there reads as a pass.
Every probe in the store is read two ways:

- a shell guard, ``COND || { ... }``, whose block runs ``exit 0``, whatever it prints and
  however many lines it spans; quoted text and heredoc bodies, which are another
  program's source, are not read as the probe's own statements;
- a message saying the claim cannot be reached here (``untestable``, ``not installed``,
  ``not built``, ``not configured``) with a zero exit (``exit 0``, ``sys.exit(0)``,
  ``SystemExit(0)``) on its line or the next, which reads a stop in an ``if`` branch or in
  the Python a probe runs.

Not held: such a stop worded otherwise, since a bare zero exit in a branch is also how
several probes pass; a probe in parts that prints such a message and runs on to a zero
exit at its end.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import NamedTuple, NewType

import pytest

from aletheia.common_types import Prose

# A probe's source text, as the store holds it.
ProbeText = NewType("ProbeText", str)
# One line of a probe's source, or the word closing a heredoc it opens.
ProbeLine = NewType("ProbeLine", str)
# A line's number in its probe, from 1.
LineNumber = NewType("LineNumber", int)


class Statement(NamedTuple):
    """One of a probe's own lines: its number, and its text with quoted text blanked."""

    number: LineNumber
    bare: ProbeLine


STORE = Path(__file__).resolve().parents[2] / "probes"
_STOP = re.compile(r"untestable|not installed|not built|not configured")
_ZERO = re.compile(r"\bexit 0\b|\bsys\.exit\(0\)|\bSystemExit\(0\)")
_QUOTED = re.compile(r"'[^']*'|\"(?:[^\"\\]|\\.)*\"")
# A heredoc's opening, ``<<WORD``, ``<<-WORD`` or ``<<'WORD'``; a here-string ``<<<`` is not one.
_HEREDOC = re.compile(r"(?<!<)<<-?(?!<)\s*['\"]?([A-Za-z_]\w*)")
_GUARD = re.compile(r"\|\|\s*\{")
_EXIT_ZERO = re.compile(r"(?:^|[\s;{])exit 0\s*(?:;|\}|$)")


def zero_after_stop(text: ProbeText) -> list[Prose]:
    """Each line of ``text`` saying its claim cannot be reached and exiting 0 there or next."""
    lines = text.splitlines()
    return [
        Prose(f"{number}: {line.strip()}")
        for number, line in enumerate(lines, start=1)
        if _STOP.search(line) and any(_ZERO.search(near) for near in lines[number - 1 : number + 1])
    ]


def _statements(text: ProbeText) -> list[Statement]:
    """Keep the probe's own lines, quoted text blanked, comments and heredoc bodies left out."""
    kept: list[Statement] = []
    closing: ProbeLine | None = None
    for number, line in enumerate(text.splitlines(), start=1):
        if closing is not None:
            closing = None if line.strip() == closing else closing
            continue
        if line.lstrip().startswith("#"):
            continue
        kept.append(Statement(LineNumber(number), ProbeLine(_QUOTED.sub("''", line))))
        opened = _HEREDOC.search(line)
        if opened is not None:
            closing = ProbeLine(opened[1])
    return kept


def guard_exits_zero(text: ProbeText) -> list[Prose]:
    """Each shell guard, ``COND || { ... }``, of ``text`` whose block runs ``exit 0``."""
    lines = text.splitlines()
    statements = _statements(text)
    found: list[Prose] = []
    for index, (number, bare) in enumerate(statements):
        opened = _GUARD.search(bare)
        if opened is None:
            continue
        block = [bare[opened.end() :]]
        if "}" not in block[0]:
            for later in statements[index + 1 :]:
                block.append(later.bare)
                if later.bare.strip() == "}":
                    break
        if any(_EXIT_ZERO.search(part) for part in block):
            found.append(Prose(f"{number}: {lines[number - 1].strip()}"))
    return found


def stops_passing(text: ProbeText) -> list[Prose]:
    """Each line of ``text`` that either reading reports, once."""
    return sorted({*guard_exits_zero(text), *zero_after_stop(text)})


def test_no_probe_passes_where_it_cannot_reach_its_claim() -> None:
    """No probe in the store exits 0 from a guard, or after saying its claim cannot be reached."""
    probes = sorted(STORE.glob("*.sh"))
    assert len(probes) > 1, f"no probe read under {STORE}"
    found = [
        Prose(f"{probe.name}:{hit}")
        for probe in probes
        for hit in stops_passing(ProbeText(probe.read_text(encoding="utf-8")))
    ]
    assert not found, "a probe exits 0 where it cannot reach its claim:\n" + "\n".join(found)


@pytest.mark.parametrize(
    "probe",
    [
        ProbeText('[ -f db.json ] || { echo "no compile database; configure it"; exit 0; }\n'),
        ProbeText('command -v cc || {\n    echo "no compiler"\n    rm -f x\n    exit 0\n}\n'),
        ProbeText("grep -q x <<<word\n[ -d t ] || { exit 0; }\n"),
        ProbeText("cat > a <<'EOF'\nexit 1\nEOF\n[ -d t ] || { echo \"no tree\"; exit 0; }\n"),
        ProbeText("# writes <<EOF\n[ -d t ] || { exit 0; }\n"),
    ],
)
def test_a_guard_exiting_zero_is_found(probe: ProbeText) -> None:
    """A guard whose block runs ``exit 0`` is reported, however worded, past a heredoc."""
    assert len(stops_passing(probe)) == 1


@pytest.mark.parametrize(
    "probe",
    [
        ProbeText('[ -f db.json ] || { echo "no compile database"; exit 2; }\n'),
        ProbeText('[ -f a ] || { echo "run: exit 0; then retry"; exit 1; }\n'),
        ProbeText("[ -f a ] || { soft_exit 0; exit 2; }\n"),
        ProbeText("cat > p <<'SH'\npgrep -f j || { kill \"$m\"; exit 0; }\nSH\n"),
        ProbeText('if [ -f a ]; then\n    echo "PASS: a is there"\n    exit 0\nfi\n'),
        ProbeText('[ -f a ] || {\n    echo "no a"\n    exit 2\n}\n[ -f b ] && exit 0\n'),
        ProbeText('# [ -f a ] || { echo "skipped"; exit 0; }\n'),
    ],
)
def test_a_guard_exiting_otherwise_is_not_found(probe: ProbeText) -> None:
    """A guard exiting non-zero, ``exit 0`` quoted, in a word, in a heredoc or after the block."""
    assert not stops_passing(probe)


@pytest.mark.parametrize(
    "probe",
    [
        ProbeText('if ! command -v x; then\n    echo "x untestable"\n    exit 0\nfi\n'),
        ProbeText('if which(MULL) is None:\n    print("Mull not installed")\n    sys.exit(0)\n'),
        ProbeText('if not tree:\n    print("tree not built")\n    raise SystemExit(0)\n'),
        ProbeText('if not tree:\n    print("tree not configured"); sys.exit(0)\n'),
    ],
)
def test_a_zero_exit_after_a_stop_is_found(probe: ProbeText) -> None:
    """A stop message followed by a zero exit, on its line or the next, is reported."""
    assert len(stops_passing(probe)) == 1


@pytest.mark.parametrize(
    "probe",
    [
        ProbeText('if not tool:\n    print("tool not installed")\n    sys.exit(2)\n'),
        ProbeText('echo "PASS: every exit is 0"\nexit 0\n'),
        ProbeText('echo "ccache not installed"\nstatus=1\nexit 0\n'),
    ],
)
def test_a_stop_with_another_exit_is_not_found(probe: ProbeText) -> None:
    """A stop exiting 2, a pass, or a zero exit two lines on, is not reported."""
    assert not stops_passing(probe)
