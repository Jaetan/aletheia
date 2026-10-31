# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Build the distribution guide's C example with each of its recipes against a bundle, and run it.

A C host follows ``docs/development/DISTRIBUTION.md`` section ``### C``: the
recipe of ``#### Compile and link``, which names the unpacked bundle by
``/path/to/aletheia``; the recipe of ``#### Relative RPATH (relocatable
binary)``, run beside the bundle unpacked as ``aletheia/``; and the program of
``#### Minimal C example``.  Each subsection holds one fence of its language,
``bash`` for a recipe and ``c`` for the program, read as CommonMark reads it
(``tools._markdown``).  The reader takes that fence opened with backticks or
tildes; ``tools.check_fence_marks`` holds it to three backticks, the mark of a
fence a harness runs.

This gate unpacks a distribution tarball (``cabal run shake -- dist``) and
builds the program with each recipe as the guide writes it, the placeholder
replaced by the bundle's path and the compiler word by ``--c-compiler``.  It
runs each build with no ``LD_LIBRARY_PATH``, so the RPATH the recipe writes is
what finds the libraries, and holds it to printing one success reply.  It is
the C consumer of the bundle validation, apart from ``tools.bundle_validate``
because it reads the guide through the Markdown reader, which that tool, run by
an interpreter holding the standard library alone, cannot import.
``tools.check_dist_staging`` holds the recipe the dist rule prints to the first
recipe, line for line, through the reader here.

Exit codes: 0, both builds ran and each printed a success reply; 1, a build, a
run or a reply failed, each named with its output; 2, could not check: the
tarball, the compiler or the guide's C section is not there.

Usage:
  python -m tools.bundle_c_example dist/aletheia.tar.gz --c-compiler clang-23
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple, TypedDict, cast

from tools._common import CommandWord, RelPath, emit, find_executable
from tools._markdown import FencedBlock, Section, fenced_blocks, sections
from tools.bundle_validate import (
    BUNDLE_DIR_NAME,
    REPO_ROOT,
    BundleValidationError,
    run_step,
    unpack_bundle,
)

from aletheia.common_types import ExitStatus, Prose

GUIDE = RelPath("docs/development/DISTRIBUTION.md")

# Where the first recipe writes the unpacked bundle's absolute path.
PLACEHOLDER = Prose("/path/to/aletheia")

# The word each recipe opens with, the compiler, which --c-compiler replaces.
RECIPE_COMPILER = CommandWord("gcc")

COULD_NOT_CHECK = ExitStatus(2)

_SECTION = Prose("### C")
_LINK = Prose("#### Compile and link")
_RELOCATABLE = Prose("#### Relative RPATH (relocatable binary)")
_EXAMPLE = Prose("#### Minimal C example")

# The file each recipe compiles, which the gate writes the example to.
_SOURCE = "main.c"

# The program a recipe writes: the one word after its -o.
_OUTPUT = re.compile(r"(?:^|\s)-o\s+(\S+)")


class CGuideError(Exception):
    """The guide's C section is not in the shape this reader takes."""


class CGuide(NamedTuple):
    """The guide's two C recipes and its example program, each the text of its fence."""

    link: Prose
    relocatable: Prose
    example: Prose


class CGuideFences(NamedTuple):
    """The fence of each of the guide's two C recipes and of its example program."""

    link: FencedBlock
    relocatable: FencedBlock
    example: FencedBlock


class Build(NamedTuple):
    """One recipe of the guide, the subsection naming it, and the directory it runs in."""

    name: Prose
    recipe: Prose
    cwd: Path


class _Reply(TypedDict):
    """The field of a kernel reply this gate reads."""

    status: Prose


@dataclass(frozen=True)
class Config:
    """One run's inputs, as parsed from the command line."""

    tarball: Path
    guide: Path
    compiler: CommandWord
    keep_work: bool = False


# ── The guide's C section (pure logic; unit-tested) ─────────────────────────


def _within(text: Prose, outer: Section, heading: Prose) -> Section:
    """Return the one section ``heading`` opens inside ``outer``."""
    found = [
        inner for inner in sections(text, heading) if outer.first <= inner.heading.line < outer.end
    ]
    if len(found) != 1:
        message = f"{len(found)} {heading!r} sections under {_SECTION!r}, not one"
        raise CGuideError(message)
    return found[0]


def _fence(text: Prose, where: Section, language: Prose) -> FencedBlock:
    """Return the one ``language`` fence of ``where``, opened with backticks or tildes."""
    found = [
        block
        for block in fenced_blocks(text)
        if block.fence.info == language and where.first <= block.fence.line < where.end
    ]
    if len(found) != 1:
        message = f"{len(found)} {language} fences under {where.heading.source!r}, not one"
        raise CGuideError(message)
    return found[0]


def c_guide_fences(text: Prose) -> CGuideFences:
    """Return the fence of each recipe and of the example of the guide's C section.

    ``tools.check_fence_marks`` holds each of these fences to opening with three
    backticks, the mark of a fence a harness runs.

    Raises:
        CGuideError: The section, one of its subsections, or the one fence of a
            subsection is missing or not alone.

    """
    match sections(text, _SECTION):
        case [outer]:
            pass
        case found:
            message = f"{len(found)} {_SECTION!r} sections, not one"
            raise CGuideError(message)
    bash, c = Prose("bash"), Prose("c")
    return CGuideFences(
        link=_fence(text, _within(text, outer, _LINK), bash),
        relocatable=_fence(text, _within(text, outer, _RELOCATABLE), bash),
        example=_fence(text, _within(text, outer, _EXAMPLE), c),
    )


def read_c_guide(text: Prose) -> CGuide:
    """Return the two recipes and the example of the guide's C section.

    Raises:
        CGuideError: ``c_guide_fences`` does not find each fence alone.

    """
    found = c_guide_fences(text)
    return CGuide(
        link=found.link.content,
        relocatable=found.relocatable.content,
        example=found.example.content,
    )


def read_guide_file(path: Path) -> CGuide:
    """Read the guide at ``path`` and return its C section.

    Raises:
        CGuideError: The file cannot be read as UTF-8 text, or its C section is
            not in the shape ``read_c_guide`` takes.

    """
    try:
        text = Prose(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError) as error:
        message = f"{path} is not read: {error}"
        raise CGuideError(message) from error
    try:
        return read_c_guide(text)
    except CGuideError as error:
        message = f"{path}: {error}"
        raise CGuideError(message) from error


# ── A recipe as the gate runs it (pure logic; unit-tested) ──────────────────


def recipe_command(recipe: Prose, bundle: Path, compiler: CommandWord) -> Prose:
    """Return ``recipe`` with ``compiler`` for its compiler word, ``bundle`` for its placeholder."""
    opening = f"{RECIPE_COMPILER} "
    if not recipe.startswith(opening):
        message = f"the recipe does not open with {opening!r}: {recipe!r}"
        raise BundleValidationError(message)
    where = str(bundle)
    if shlex.quote(where) != where:
        message = f"the bundle path {where!r} needs quoting, which the recipe's placeholder lacks"
        raise BundleValidationError(message)
    rest = recipe.removeprefix(opening).replace(PLACEHOLDER, where)
    return Prose(f"{shlex.quote(compiler)} {rest}")


def recipe_output(recipe: Prose) -> Path:
    """Return the program ``recipe`` writes, relative to the directory it runs in."""
    found = _OUTPUT.findall(recipe)
    if len(found) != 1:
        message = f"the recipe names {len(found)} outputs after -o, not one: {recipe!r}"
        raise BundleValidationError(message)
    return Path(found[0])


def reply_problem(stdout: Prose) -> Prose | None:
    """Say why ``stdout`` is not one success reply of the kernel, or None when it is."""
    try:
        status = cast("_Reply", json.loads(stdout))["status"]
    except json.JSONDecodeError, TypeError, KeyError:
        return Prose(f"printed {stdout!r}, not one JSON reply")
    if status != "success":
        return Prose(f"answered {stdout.strip()!r}, not a success reply")
    return None


def lay_out(guide: CGuide, work: Path) -> tuple[Build, Build]:
    """Lay out the directory each recipe runs in under ``work``, the example in each.

    ``work`` holds the unpacked bundle.  The first recipe names the bundle by its
    path, so it runs in a directory of its own.  The second runs beside the
    bundle, ``aletheia/``, and writes into ``bin/``, whose ``../lib`` holds the
    bundle's libraries, as the guide's deploy tree does.
    """
    link = work / "c-link"
    deploy = work / "c-deploy"
    for where in (link, deploy):
        where.mkdir()
        _ = (where / _SOURCE).write_text(guide.example, encoding="utf-8")
    (deploy / "bin").mkdir()
    (deploy / BUNDLE_DIR_NAME).symlink_to(work / BUNDLE_DIR_NAME, target_is_directory=True)
    (deploy / "lib").symlink_to(Path(BUNDLE_DIR_NAME) / "lib", target_is_directory=True)
    return (
        Build(Prose("Compile and link"), guide.link, link),
        Build(Prose("Relative RPATH"), guide.relocatable, deploy),
    )


# ── Running ─────────────────────────────────────────────────────────────────


def run_build(build: Build, bundle: Path, compiler: CommandWord) -> None:
    """Build the example with ``build``'s recipe, run it, and hold it to a success reply."""
    env = {name: value for name, value in os.environ.items() if name != "LD_LIBRARY_PATH"}
    command = recipe_command(build.recipe, bundle, compiler)
    _ = run_step(
        f"c: {build.name}: build", [find_executable("bash"), "-c", command], cwd=build.cwd, env=env
    )
    program = build.cwd / recipe_output(build.recipe)
    ran = run_step(f"c: {build.name}: run", [str(program)], cwd=build.cwd, env=env)
    problem = reply_problem(Prose(ran.stdout))
    if problem is not None:
        message = f"c: {build.name}: the example {problem}"
        raise BundleValidationError(message)


def _check_in(cfg: Config, guide: CGuide, work: Path) -> list[Prose]:
    """Unpack the bundle under ``work`` and run every build; return each failure."""
    bundle = unpack_bundle(cfg.tarball, work).resolve()
    failures: list[Prose] = []
    for build in lay_out(guide, work):
        try:
            run_build(build, bundle, cfg.compiler)
        except BundleValidationError as failure:
            failures.append(Prose(str(failure)))
    return failures


def check(cfg: Config) -> ExitStatus:
    """Run both builds of the guide's example against the bundle; return the exit status."""
    if shutil.which(cfg.compiler) is None:
        emit(f"c example: COULD NOT CHECK, {cfg.compiler} is not in PATH")
        return COULD_NOT_CHECK
    if not cfg.tarball.is_file():
        emit(f"c example: COULD NOT CHECK, no tarball at {cfg.tarball}")
        return COULD_NOT_CHECK
    try:
        guide = read_guide_file(cfg.guide)
    except CGuideError as error:
        emit(f"c example: COULD NOT CHECK, {error}")
        return COULD_NOT_CHECK
    work = Path(tempfile.mkdtemp(prefix="aletheia-c-example-"))
    try:
        failures = _check_in(cfg, guide, work)
    except BundleValidationError as error:
        failures = [Prose(str(error))]
    finally:
        if cfg.keep_work:
            emit(f"[c example] work tree kept at {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)
    if failures:
        emit("c example: FAIL")
        for failure in failures:
            emit(f"  - {failure}")
        return ExitStatus(1)
    emit(f"c example: PASS, both recipes of {cfg.guide} built it with {cfg.compiler}, each run ok")
    return ExitStatus(0)


# ── CLI ─────────────────────────────────────────────────────────────────────


def parse_args() -> Config:
    """Parse the command line into a Config."""
    parser = argparse.ArgumentParser(prog="bundle_c_example", description=__doc__)
    _ = parser.add_argument(
        "tarball", type=Path, help="distribution tarball built by `cabal run shake -- dist`"
    )
    _ = parser.add_argument(
        "--guide", type=Path, default=REPO_ROOT / GUIDE, help="the guide whose C section is run"
    )
    _ = parser.add_argument(
        "--c-compiler",
        default=RECIPE_COMPILER,
        help=f"the compiler each recipe runs with, in place of its {RECIPE_COMPILER!r}",
    )
    _ = parser.add_argument(
        "--keep-work", action="store_true", help="keep the temporary work tree for debugging"
    )
    args = parser.parse_args()
    return Config(
        tarball=args.tarball,
        guide=args.guide,
        compiler=CommandWord(args.c_compiler),
        keep_work=bool(args.keep_work),
    )


def main() -> ExitStatus:
    """CLI entry point."""
    return check(parse_args())


if __name__ == "__main__":
    sys.exit(main())
