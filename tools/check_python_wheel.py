# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Build the Python binding's wheel as the bundle stages it, and hold it to carrying its licence.

The release bundle stages the binding with the pathspecs of the dist rule's
``stageBinding "python"`` call, and a consumer, the runtime image among them,
builds and installs it from there.  The suite runs on ``python/.venv``,
installed once, so nothing in it rebuilds the package: an edit to
``python/pyproject.toml`` that a build backend refuses passes it.  This writes
the files those pathspecs name, as the index holds them, into a scratch
directory, builds the wheel there with this Python's own setuptools and no
network (``pip wheel --no-build-isolation --no-deps --no-index``), holding the
build system's requirements to what this Python has installed
(``--check-build-dependencies``, which an isolated build would install), and
holds the wheel's ``.dist-info`` to carrying ``licenses/LICENSE.md``, byte for
byte the binding's ``LICENSE.md``.

Exit 0 when held; 1 when the wheel does not build, or builds without the
binding's licence; 2 when it cannot check: this Python has no setuptools, the
build program names no pathspecs for the binding, or git cannot read the
index.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import tempfile
import zipfile
from pathlib import Path, PurePosixPath
from typing import NamedTuple, NewType

from tools._common import emit, find_executable, read_shake_program, run_capture
from tools.bundle_licences import LicenceText
from tools.check_dist_staging import DistStagingError, parse_stage_bindings

from aletheia.common_types import ExitStatus, Prose

REPO = Path(__file__).resolve().parent.parent
HELD, FOUND, UNCHECKED = ExitStatus(0), ExitStatus(1), ExitStatus(2)
BINDING = "python"
LICENCE = Path(BINDING) / "LICENSE.md"
# Where a wheel carries a licence file, below its ``.dist-info`` directory.
CARRIED = ("licenses", "LICENSE.md")

# A git pathspec as the dist rule writes it: ``python/aletheia``, ``:(exclude)...``.
Pathspec = NewType("Pathspec", str)
# A path from the repository's root, as git lists a tracked file.
TrackedPath = NewType("TrackedPath", str)


class Built(NamedTuple):
    """What one wheel build did: whether pip built it, and what pip said."""

    ok: bool
    said: Prose


class WheelUncheckedError(Exception):
    """The binding cannot be staged for its wheel to be built."""


def binding_pathspecs(program: Prose) -> list[Pathspec]:
    """Return the pathspecs the dist rule stages the Python binding with, as written."""
    spec = next(b for b in parse_stage_bindings(program) if b.name == BINDING)
    return [Pathspec(word) for word in spec.raw]


def stage_binding(repo: Path, pathspecs: list[Pathspec], into: Path) -> list[TrackedPath]:
    """Write each tracked file ``pathspecs`` name, as the index holds it, under ``into``."""
    git = find_executable("git")
    listed = run_capture([git, "ls-files", "-z", "--", *pathspecs], cwd=repo)
    if listed.returncode != 0:
        message = f"git ls-files cannot read the index: {listed.stderr.strip()}"
        raise WheelUncheckedError(message)
    files = [TrackedPath(name) for name in listed.stdout.split("\0") if name]
    if not files:
        message = f"the binding's pathspecs {pathspecs} name no tracked file"
        raise WheelUncheckedError(message)
    wrote = run_capture([git, "checkout-index", f"--prefix={into}/", "--", *files], cwd=repo)
    if wrote.returncode != 0:
        message = f"git checkout-index cannot write the binding: {wrote.stderr.strip()}"
        raise WheelUncheckedError(message)
    return files


def build_wheel(source: Path, out: Path) -> Built:
    """Build the wheel of the package at ``source`` into ``out``, offline, with this Python."""
    done = run_capture(
        [
            sys.executable,
            "-m",
            "pip",
            "wheel",
            "--no-build-isolation",
            "--check-build-dependencies",
            "--no-deps",
            "--no-index",
            "--no-cache-dir",
            "--wheel-dir",
            str(out),
            str(source),
        ]
    )
    return Built(done.returncode == 0, Prose(done.stdout + done.stderr))


def wheel_findings(out: Path, licence: LicenceText | None) -> list[Prose]:
    """Return a finding unless ``out`` holds one wheel whose .dist-info carries ``licence``."""
    wheels = sorted(out.glob("*.whl"))
    if len(wheels) != 1:
        return [Prose(f"the build left {len(wheels)} wheels, not one")]
    with zipfile.ZipFile(wheels[0]) as wheel:
        carried = [
            name
            for name in wheel.namelist()
            if PurePosixPath(name).parts[0].endswith(".dist-info")
            and PurePosixPath(name).parts[1:] == CARRIED
        ]
        if not carried:
            return [Prose(f"{wheels[0].name}: its .dist-info carries no {'/'.join(CARRIED)}")]
        if licence is None or wheel.read(carried[0]) != licence:
            return [Prose(f"{wheels[0].name}: its {'/'.join(CARRIED)} is not {LICENCE}")]
    return []


def main() -> ExitStatus:
    """Build the binding's wheel from the index and report what keeps it from holding."""
    _ = argparse.ArgumentParser(
        description="Build the Python binding's wheel offline and hold it to its licence."
    ).parse_args()
    if importlib.util.find_spec("setuptools") is None:
        emit(
            "python-wheel: this Python has no setuptools (the venv's [dev] extras carry it); "
            + "the wheel is unbuilt"
        )
        return UNCHECKED
    with tempfile.TemporaryDirectory(prefix="python-wheel-") as scratch:
        source, out = Path(scratch) / "source", Path(scratch) / "wheel"
        try:
            pathspecs = binding_pathspecs(Prose(read_shake_program(REPO)))
            _ = stage_binding(REPO, pathspecs, source)
        except (OSError, RuntimeError, DistStagingError, WheelUncheckedError) as exc:
            emit(f"python-wheel: {exc}; the wheel is unbuilt")
            return UNCHECKED
        built = build_wheel(source / BINDING, out)
        if not built.ok:
            emit("python-wheel: the binding does not build; pip says:")
            for line in built.said.splitlines():
                emit(f"  {line}")
            return FOUND
        licence = source / LICENCE
        text = LicenceText(licence.read_bytes()) if licence.is_file() else None
        found = wheel_findings(out, text)
    for finding in found:
        emit(f"python-wheel: {finding}")
    if found:
        return FOUND
    emit(f"python-wheel: the binding builds offline and its wheel carries {LICENCE}")
    return HELD


if __name__ == "__main__":
    sys.exit(main())
