# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Build the bundle validator's consumers against the tree's bindings.

``tools/bundle_validate.py`` builds three consumer programs against a release
bundle, one each for Go, C++ and Rust (``tools/bundle_validation/``), but only
the weekly bundle validation and a release run it, so a binding change that
breaks a consumer went unseen until then.  This gate builds each against the
tree, in the lane of its binding, where the branch moves that binding, its
consumer or the gate:

* Go: the consumer, its import pointed at ``go/go.mod``'s module path, in a
  module of its own that replaces that module with ``go/``, built with
  ``go build``;
* C++: the consumer's source syntax-checked by ``clang++-23 -std=c++23``
  against ``cpp/include``;
* Rust: the crate staged as the dist step stages it (``Cargo.toml`` written by
  ``tools/bundle_rust_manifest.py``, ``Cargo.lock``, ``src/``) checked as a
  package of its own with ``cargo check --locked``, as the release image builds
  it, then the consumer checked against it with the crate's ``Cargo.lock``, so
  its dependencies resolve at the versions the crate is checked at.

Run: ``python -m tools.check_bundle_consumers --binding go|cpp|rust``.  Exits 0
when the consumer builds or the branch reaches none of what it reads, 1 when a
build fails, its output printed.
"""

from __future__ import annotations

import argparse
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Literal, NamedTuple, NewType, cast

from tools._branch_diff import branch_changes
from tools._common import CommandWord, RelPath, emit, find_executable, run_capture
from tools._progress import reporting
from tools.bundle_rust_manifest import ManifestText, staged_manifest
from tools.bundle_validate import (
    DEPENDENCIES_PLACEHOLDER,
    FIXTURE_DIR,
    GO_MODULE_LINE,
    retarget_go_consumer,
)

from aletheia.common_types import ExitStatus, Prose

# A Go module path, as a go.mod's `module` line declares it.
GoModule = NewType("GoModule", str)

REPO_ROOT = Path(__file__).resolve().parent.parent
type Binding = Literal["go", "cpp", "rust"]
BINDINGS: tuple[Binding, ...] = ("go", "cpp", "rust")

# What each binding's consumer build reads besides the gate itself.
_COMMON_SCOPE = (
    RelPath("tools/check_bundle_consumers.py"),
    RelPath("tools/bundle_validate.py"),
    RelPath("tools/_ci_consumer_steps.py"),
)
SCOPE_PATHS: dict[Binding, tuple[RelPath, ...]] = {
    "go": (RelPath("go/"), RelPath("tools/bundle_validation/consumer_go/"), *_COMMON_SCOPE),
    "cpp": (
        RelPath("cpp/include/"),
        RelPath("tools/bundle_validation/consumer_cpp/"),
        *_COMMON_SCOPE,
    ),
    "rust": (
        RelPath("rust/"),
        RelPath("tools/bundle_validation/consumer_rust/"),
        RelPath("tools/bundle_rust_manifest.py"),
        RelPath("shake/Rules/Dist.hs"),
        *_COMMON_SCOPE,
    ),
}
# The files the dist step stages for the Rust binding beside its manifest and src/.
_RUST_STAGED = ("Cargo.lock", "README.md", "LICENSE.md")


class Step(NamedTuple):
    """One command of the gate, what it does, and where it runs."""

    label: Prose
    argv: list[CommandWord]
    cwd: Path


def in_scope(binding: Binding, changes: list[RelPath] | None) -> bool:
    """Whether the branch reaches ``binding``'s consumer; no diff to read, or an empty one, does."""
    return not changes or any(path.startswith(SCOPE_PATHS[binding]) for path in changes)


def _words(*parts: Path | CommandWord) -> list[CommandWord]:
    """Return ``parts`` as the words of a command line."""
    return [CommandWord(str(part)) for part in parts]


def go_module() -> GoModule:
    """Return the module path ``go/go.mod`` declares."""
    found = GO_MODULE_LINE.findall((REPO_ROOT / "go" / "go.mod").read_text(encoding="utf-8"))
    if len(found) != 1:
        message = f"go/go.mod declares {len(found)} module paths, not one"
        raise RuntimeError(message)
    return GoModule(found[0])


def go_steps(work: Path) -> list[Step]:
    """Write the Go consumer under ``work``; return the commands building it against ``go/``."""
    module = go_module()
    src = work / "consumer_go"
    src.mkdir()
    fixture = (FIXTURE_DIR / "consumer_go" / "main.go").read_text(encoding="utf-8")
    _ = (src / "main.go").write_text(retarget_go_consumer(fixture, module), encoding="utf-8")
    go = CommandWord(find_executable("go"))
    word = CommandWord
    return [
        Step(Prose("go mod init"), _words(go, word("mod"), word("init"), word("consumer")), src),
        Step(
            Prose("go mod edit -replace"),
            _words(go, word("mod"), word("edit"), word(f"-replace={module}={REPO_ROOT / 'go'}")),
            src,
        ),
        Step(Prose("go get"), _words(go, word("get"), word(f"{module}/aletheia")), src),
        Step(
            Prose("go build"),
            _words(go, word("build"), word("-o"), work / "consumer", word(".")),
            src,
        ),
    ]


def cpp_steps(work: Path) -> list[Step]:
    """Return the command syntax-checking the C++ consumer against ``cpp/include``."""
    word = CommandWord
    return [
        Step(
            Prose("clang++-23 -fsyntax-only"),
            _words(
                word(find_executable("clang++-23")),
                word("-std=c++23"),
                word("-fsyntax-only"),
                word(f"-I{REPO_ROOT / 'cpp' / 'include'}"),
                FIXTURE_DIR / "consumer_cpp" / "main.cpp",
            ),
            work,
        )
    ]


def rust_steps(work: Path) -> list[Step]:
    """Stage the crate and the consumer under ``work``; return the commands checking both."""
    crate = work / "bindings" / "rust"
    crate.mkdir(parents=True)
    manifest = ManifestText((REPO_ROOT / "rust" / "Cargo.toml").read_text(encoding="utf-8"))
    _ = (crate / "Cargo.toml").write_text(staged_manifest(manifest), encoding="utf-8")
    for name in _RUST_STAGED:
        _ = shutil.copy(REPO_ROOT / "rust" / name, crate / name)
    _ = shutil.copytree(REPO_ROOT / "rust" / "src", crate / "src")
    consumer = work / "consumer_rust"
    (consumer / "src").mkdir(parents=True)
    template = (FIXTURE_DIR / "consumer_rust" / "Cargo.toml.in").read_text(encoding="utf-8")
    # The block the bundle's install.sh prints, pointed at the staged crate.
    dependency = f'[dependencies]\naletheia = {{ path = "{crate}" }}'
    _ = (consumer / "Cargo.toml").write_text(
        template.replace(DEPENDENCIES_PLACEHOLDER, dependency), encoding="utf-8"
    )
    _ = shutil.copy(FIXTURE_DIR / "consumer_rust" / "src" / "main.rs", consumer / "src" / "main.rs")
    # The crate's lock, so the consumer resolves every dependency at the version
    # the crate is checked at rather than the newest crates.io serves that day:
    # cargo reads no dependency's lock file, and the consumer has none of its own.
    _ = shutil.copy(crate / "Cargo.lock", consumer / "Cargo.lock")
    cargo = CommandWord(find_executable("cargo"))
    word = CommandWord
    return [
        Step(
            Prose("cargo check --locked (the staged crate)"),
            _words(cargo, word("check"), word("--locked")),
            crate,
        ),
        Step(Prose("cargo check (the consumer)"), _words(cargo, word("check")), consumer),
    ]


_STEPS = {"go": go_steps, "cpp": cpp_steps, "rust": rust_steps}


def main(argv: list[CommandWord] | None = None) -> ExitStatus:
    """Build the named binding's consumer against the tree where the branch reaches it."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("--binding", choices=BINDINGS, required=True)
    args = parser.parse_args(argv)
    binding = cast("Binding", args.binding)
    if not in_scope(binding, branch_changes(REPO_ROOT)):
        emit(f"check_bundle_consumers: no change on the branch reaches the {binding} consumer")
        return ExitStatus(0)
    with tempfile.TemporaryDirectory(prefix=f"aletheia-bundle-consumer-{binding}-") as scratch:
        work = Path(scratch)
        env = os.environ | {"CARGO_TARGET_DIR": str(work / "target"), "CGO_ENABLED": "1"}
        for step in _STEPS[binding](work):
            run = run_capture(step.argv, cwd=step.cwd, env=env)
            if run.returncode != 0:
                emit(f"check_bundle_consumers: {binding}: {step.label} failed ({run.returncode}):")
                emit(run.stdout + run.stderr)
                return ExitStatus(1)
    emit(f"check_bundle_consumers: the {binding} consumer builds against the tree's binding")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("check-bundle-consumers")))
