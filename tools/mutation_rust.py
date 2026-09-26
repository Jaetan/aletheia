# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Rust lane: cargo-mutants over the crate's hot path, swept in place.

cargo-mutants rewrites one function at a time, builds the crate's tests and
runs them, and writes each mutant's verdict to ``mutants.out/outcomes.json``
under the directory ``--output`` names; the lane reads that file rather than
the console, which prints only what was missed.  Which files it mutates and
which features it turns on are ``rust/.cargo/mutants.toml``, read from the
crate, so a sweep at the terminal and the lane's sweep make one set.

The sweep runs in the source tree (``--in-place``) rather than in the copy
cargo-mutants makes by default: the suite includes the DBC corpus and the
parity snapshots under ``python/`` at compile time and reads the documents
under ``docs/`` at run time, so a copy of the crate alone does not build.  In
place, one mutant runs at a time, cargo-mutants restores the file after each
and on an interrupt, and a process killed outright leaves the mutant in the
tree, where ``git diff rust/src`` shows it.  Nothing else may build or test
the crate while a sweep runs.

The tool is pinned to the version ``docs/MUTATION_BENCH.yaml`` records and
refused at any other, because two releases generate different mutant sets
and a baseline is a count of one set.

A survivor is keyed as the C++ ledger keys one: the mutation cargo-mutants
names, less its position, the repository-relative file, and the text of the
line the mutation starts on.
"""

from __future__ import annotations

import collections
import json
import os
import re
from pathlib import Path
from typing import TYPE_CHECKING, cast

from tools._common import find_executable, run_capture, run_streaming
from tools.mutation_report import MutationReport, load_spec

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

    from tools.mutation_report import SurvivorKey

REPO_ROOT = Path(__file__).resolve().parent.parent
CRATE = REPO_ROOT / "rust"

# Where the sweep's own report directory lands under the run's artifact
# directory: ``<artifact_dir>/rust/mutants.out/``.
RUST_OUTPUT_DIR = "rust"
OUTCOMES = Path(RUST_OUTPUT_DIR) / "mutants.out" / "outcomes.json"

# ``cargo mutants --version`` prints the tool's name and its version.
_VERSION_RE = re.compile(r"cargo-mutants\s+(\d+\.\d+\.\d+)")
# A mutant's name opens on its position, ``src/file.rs:LINE:COL: ``, and the
# rest names the mutation; the ledger keys on the rest.
_POSITION_RE = re.compile(r"^[^:]+:\d+:\d+:\s*")


def cargo_mutants_version(text: str) -> str | None:
    """Read the version out of ``cargo mutants --version``, or None where it is not one."""
    match = _VERSION_RE.search(text)
    return match.group(1) if match else None


def _check_rust_tools(pinned: str | None) -> tuple[str, Path] | str:
    """Return ``(cargo, lib)`` when the Rust lane can run, else an error string."""
    try:
        cargo = find_executable("cargo")
    except RuntimeError as exc:
        return str(exc)
    version = run_capture([cargo, "mutants", "--version"])
    found = cargo_mutants_version(version.stdout) if version.returncode == 0 else None
    if found is None:
        return "cargo-mutants is not installed: cargo install cargo-mutants --locked"
    if pinned is not None and found != pinned:
        return f"cargo-mutants {found} is installed where the record pins {pinned}"
    lib = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not lib.is_file():
        return f"libaletheia-ffi.so not found at {lib}; run `cabal run shake -- build` first"
    return (cargo, lib)


def _pinned_version() -> str | None:
    """Read the cargo-mutants version the record pins, or None where it pins none."""
    spec = load_spec().get("bindings", {}).get("rust", {})
    version = cast("Mapping[str, object]", spec).get("version")
    return version if isinstance(version, str) else None


def run_rust(artifact_dir: Path) -> MutationReport:
    """Sweep the crate's hot path with cargo-mutants and read its outcomes."""
    checked = _check_rust_tools(_pinned_version())
    if isinstance(checked, str):
        return MutationReport("rust", "cargo-mutants", 0, 0, "", error=checked)
    cargo, lib = checked
    # The suite loads the kernel through ALETHEIA_LIB, as every other run of it
    # does; the path is absolute because cargo-mutants runs the tests from
    # the crate.
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(lib)
    output = artifact_dir / RUST_OUTPUT_DIR
    output.mkdir(parents=True, exist_ok=True)
    # Streams, so a sweep killed by a wall clock still leaves the log of how
    # far it got.  Colours off, so the archived log is the text it printed.
    proc = run_streaming(
        [cargo, "mutants", "--in-place", "--colors", "never", "--output", str(output)],
        cwd=CRATE,
        env=env,
    )
    raw = proc.stdout
    (artifact_dir / "rust.raw.txt").write_text(raw)
    outcomes_path = artifact_dir / OUTCOMES
    if not outcomes_path.is_file():
        return MutationReport(
            "rust",
            "cargo-mutants",
            0,
            0,
            raw,
            error=f"cargo mutants wrote no outcomes (exit {proc.returncode}; see rust.raw.txt)",
        )
    outcomes = cast("Mapping[str, object]", json.loads(outcomes_path.read_text(encoding="utf-8")))
    return parse_outcomes(outcomes, raw, f"exit {proc.returncode}")


def parse_outcomes(outcomes: Mapping[str, object], raw: str, where: str) -> MutationReport:
    """Read a sweep's ``outcomes.json`` into a report.

    The file carries the four buckets every mutant lands in exactly one of:
    caught, missed, timed out and unviable.  Caught is killed and missed is
    survived; a timed-out mutant is neither, and the drift gate reads that
    count against the record's ceiling; an unviable mutant did not build, a
    property of the source the record carries beside the total.  A sweep that
    reached no mutant, because the unmutated baseline failed, is an error
    rather than a clean run of nothing.
    """
    counts = {name: outcomes.get(name) for name in ("caught", "missed", "timeout", "unviable")}
    if not all(isinstance(value, int) for value in counts.values()):
        return MutationReport(
            "rust",
            "cargo-mutants",
            0,
            0,
            raw,
            error=f"outcomes.json carries no counts (see rust.raw.txt; {where})",
        )
    caught, missed, timeout, unviable = (cast("int", counts[k]) for k in counts)
    if caught + missed + timeout + unviable == 0:
        return MutationReport(
            "rust",
            "cargo-mutants",
            0,
            0,
            raw,
            error=f"the sweep tested no mutant (see rust.raw.txt; {where})",
        )
    return MutationReport("rust", "cargo-mutants", caught, missed, raw, timeouts=timeout)


def outcomes_survivor_rows(
    outcomes: Mapping[str, object], read_line: Callable[[str, int], str]
) -> dict[SurvivorKey, int]:
    """Collect the survivors of an ``outcomes.json`` into rows.

    Each outcome's ``scenario`` is the mutant, with its ``name``, its file
    relative to the crate and the span it replaces; ``summary`` is its
    bucket.  ``read_line(file, line)`` supplies the source line, stripped
    before it keys the row.
    """
    rows: dict[SurvivorKey, int] = collections.Counter()
    for outcome in cast("list[Mapping[str, object]]", outcomes.get("outcomes", [])):
        if outcome.get("summary") != "MissedMutant":
            continue
        scenario = cast("Mapping[str, Mapping[str, object]]", outcome["scenario"])
        mutant = scenario["Mutant"]
        file = f"rust/{mutant['file']}"
        span = cast("Mapping[str, Mapping[str, int]]", mutant["span"])
        line = span["start"]["line"]
        mutator = _POSITION_RE.sub("", str(mutant["name"]))
        rows[(mutator, file, read_line(file, line).strip())] += 1
    return rows


def repo_line(file: str, line: int) -> str:
    """Read the ``line``-th line (1-based) of ``file`` under the repository root."""
    with (REPO_ROOT / file).open(encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


def rust_survivor_rows(artifact_dir: Path) -> dict[SurvivorKey, int] | None:
    """Read the Rust sweep's survivor rows from its outcomes, if it wrote them."""
    path = artifact_dir / OUTCOMES
    if not path.is_file():
        return None
    outcomes = cast("Mapping[str, object]", json.loads(path.read_text(encoding="utf-8")))
    return outcomes_survivor_rows(outcomes, repo_line)
