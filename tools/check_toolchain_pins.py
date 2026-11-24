# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the machine this runs on to the Go, Rust and clang the tree pins.

Every build of the tree uses one Go, one Rust and one clang. Go is the version
``.go-version`` names, which every workflow's ``actions/setup-go`` step reads.
Rust is the channel ``rust-toolchain.toml`` names, which rustup takes for a run
inside the tree and ``tools/install_rust_toolchain.sh`` installs and makes the
default on a runner. clang is the LLVM upstream ``cpp/toolchain/check_upstream.sh``
records, which every runner's toolchain step holds its install to.

The gate reads ``go version``, ``rustc --version`` inside the tree and outside it
(a program built outside, as the bundle validation builds its consumers, takes
rustup's default), and ``clang-23 --version``. A Go or a Rust other than the
pinned one is refused, as is one missing from PATH. A clang of another upstream
is reported without failing: this machine's clang comes from its distribution,
which does not carry every LLVM release the runners' archive does.

Run: ``python -m tools.check_toolchain_pins``. Exits 0 when Go and Rust are the
pinned ones, 1 when either differs or is missing, 2 when a pin cannot be read.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import tempfile
import tomllib
from pathlib import Path
from typing import Literal, NewType

from tools._common import CommandWord, emit, run_capture
from tools._progress import reporting

from aletheia.common_types import ExitStatus, Prose

# A compiler's version as the pin and the compiler's own report spell it.
CompilerVersion = NewType("CompilerVersion", str)
# A compiler the gate asks for its version.
type Compiler = Literal["go", "rustc", "clang-23"]

REPO_ROOT = Path(__file__).resolve().parent.parent
GO_PIN = REPO_ROOT / ".go-version"
RUST_PIN = REPO_ROOT / "rust-toolchain.toml"
CLANG_PIN = REPO_ROOT / "cpp" / "toolchain" / "check_upstream.sh"
# The check's record of LLVM: the source package, then its upstream version.
_LLVM_ROW = re.compile(r'"llvm-toolchain-23 ([0-9][0-9A-Za-z.+-]*)"')
_RELEASE = re.compile(r"\d+\.\d+\.\d+")
# Each compiler's version argument, and where its report gives the version.
_ASKED = {
    "go": ("version", re.compile(r"^go version go(\S+) ")),
    "rustc": ("--version", re.compile(r"^rustc (\S+) ")),
    "clang-23": ("--version", re.compile(r"clang version (\d+\.\d+\.\d+)")),
}


class PinError(Exception):
    """A pin file that cannot be read."""


def go_pin() -> CompilerVersion:
    """Return the Go version ``.go-version`` names."""
    try:
        text = GO_PIN.read_text(encoding="utf-8").strip()
    except OSError as error:
        message = f"{GO_PIN.name}: {error}"
        raise PinError(message) from error
    if not _RELEASE.fullmatch(text):
        message = f"{GO_PIN.name} names no Go release: {text!r}"
        raise PinError(message)
    return CompilerVersion(text)


def rust_pin() -> CompilerVersion:
    """Return the Rust channel ``rust-toolchain.toml`` names."""
    try:
        record = tomllib.loads(RUST_PIN.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        message = f"{RUST_PIN.name}: {error}"
        raise PinError(message) from error
    channel = record.get("toolchain", {}).get("channel")
    if not isinstance(channel, str) or not _RELEASE.fullmatch(channel):
        message = f"{RUST_PIN.name} names no Rust release as its channel: {channel!r}"
        raise PinError(message)
    return CompilerVersion(channel)


def clang_pin() -> CompilerVersion:
    """Return the LLVM upstream ``check_upstream.sh`` records."""
    shown = CLANG_PIN.relative_to(REPO_ROOT)
    try:
        found = _LLVM_ROW.findall(CLANG_PIN.read_text(encoding="utf-8"))
    except OSError as error:
        message = f"{shown}: {error}"
        raise PinError(message) from error
    if len(found) != 1:
        message = f"{shown} records {len(found)} LLVM upstreams, not one"
        raise PinError(message)
    return CompilerVersion(found[0])


def reported(compiler: Compiler, cwd: Path) -> CompilerVersion | None:
    """Return the version ``compiler`` reports run from ``cwd``, or None when it reports none."""
    resolved = shutil.which(compiler)
    if resolved is None:
        return None
    argument, pattern = _ASKED[compiler]
    result = run_capture([resolved, argument], cwd=cwd)
    found = pattern.search(result.stdout)
    return None if result.returncode != 0 or found is None else CompilerVersion(found.group(1))


def main(argv: list[CommandWord] | None = None) -> ExitStatus:
    """Compare each compiler with its pin; print what differs; return the exit code."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args(argv)
    try:
        go, rust, clang = go_pin(), rust_pin(), clang_pin()
    except PinError as refusal:
        emit(f"check-toolchain-pins: {refusal}")
        return ExitStatus(2)
    with tempfile.TemporaryDirectory() as outside:
        found = {
            "go": (reported("go", REPO_ROOT), go),
            "rustc in the tree": (reported("rustc", REPO_ROOT), rust),
            "rustc outside the tree": (reported("rustc", Path(outside)), rust),
        }
    refused = [
        f"{name} is {have or 'missing from PATH'}, and the tree pins {want}"
        for name, (have, want) in found.items()
        if have != want
    ]
    have_clang = reported("clang-23", REPO_ROOT)
    if have_clang != clang:
        emit(
            f"check-toolchain-pins: note: clang-23 is upstream {have_clang or 'missing from PATH'},"
            + f" and the runners' is {clang}; reported, not refused"
        )
    for line in refused:
        emit(f"check-toolchain-pins: {line}")
    if found["go"][0] != go:
        emit(f"check-toolchain-pins: install Go {go} from go.dev first on PATH")
    if any(found[name][0] != rust for name in ("rustc in the tree", "rustc outside the tree")):
        emit(
            f"check-toolchain-pins: run `rustup toolchain install {rust} --component clippy"
            + f" --component rustfmt` and `rustup default {rust}`"
        )
    if refused:
        return ExitStatus(1)
    emit(f"check-toolchain-pins: go {go}, and rustc {rust} in the tree and outside it, as pinned")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("check-toolchain-pins")))
