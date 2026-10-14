# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold ``cpp/.clang-format`` to the decisions it lists and to the configuration it gives.

Three claims, each read off what the pinned clang-format dumps, the binary the
format gate runs (``python/.venv/bin/clang-format``):

* The effective configuration is the recorded one: the dump's digest is
  ``RECORDED_DIGEST``.  The file lists only what the project decides, and a
  value it leaves to the base style is right only while the base style keeps
  giving it, so the whole dump is pinned rather than the file's own lines: a
  release that moves any option is caught at the next run instead of absorbed.
  An option that moved for a good reason is accepted by recording the new
  digest here, in a commit that says which option moved and why.
* Every key the file sets decides something: its value differs from the one
  the base style (``--style=LLVM``) gives, ``Language`` and ``BasedOnStyle``
  aside.
* Every key the file sets is one the tool knows by that name: the dump carries
  it, so no option rides on an alias a later release can drop, changing the
  enforced style with no diff here.

The tool is pinned to a range of releases (``python/pyproject.toml``), so the
release a fresh install takes can move with no diff, and the gate runs on every
run rather than only when the pin moves.

Exits 0 when the three hold, 1 naming each refusal, and 2 when the venv carries
no clang-format.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path
from typing import NewType

from tools._common import emit, git_toplevel, run_capture

from aletheia.common_types import ExitStatus, Prose

# An option name of the configuration, the dump of one, an option's whole value
# (nested lines included), and the dump's SHA-256 in hex.
ConfigKey = NewType("ConfigKey", str)
DumpText = NewType("DumpText", str)
OptionValue = NewType("OptionValue", str)
Digest = NewType("Digest", str)

# The digest of the configuration cpp/.clang-format gives under clang-format 23.1.3.
RECORDED_DIGEST = Digest("f60007f6fbec9d4cf84ee06061de48fbf8b913fbf44841a21ecc5d7bbc3cced7")

# The file's keys that choose a configuration rather than set an option of it.
_LANGUAGE = ConfigKey("Language")
_BASE_STYLE = ConfigKey("BasedOnStyle")
_BASE_STYLE_NAME = "LLVM"

# A top-level key and the rest of its line.
_KEY_LINE = re.compile(r"^([A-Za-z0-9_]+):(.*)$")


def option_values(dump: DumpText) -> dict[ConfigKey, OptionValue]:
    """Return each top-level option of a dumped configuration with its whole value."""
    values: dict[ConfigKey, list[Prose]] = {}
    key: ConfigKey | None = None
    for line in dump.split("\n"):
        match = _KEY_LINE.match(line)
        if match:
            key = ConfigKey(match.group(1))
            values[key] = [Prose(match.group(2).strip())]
        elif key is not None and line.startswith(" "):
            values[key].append(Prose(line))
    return {name: OptionValue("\n".join(lines)) for name, lines in values.items()}


def own_keys(config: Prose) -> list[ConfigKey]:
    """Return the top-level keys a ``.clang-format`` file sets, in its order."""
    return [
        ConfigKey(match.group(1))
        for match in (_KEY_LINE.match(line) for line in config.split("\n"))
        if match
    ]


def digest(dump: DumpText) -> Digest:
    """Return the SHA-256 of a dump as clang-format prints it."""
    return Digest(hashlib.sha256(dump.encode("utf-8")).hexdigest())


def config_refusals(config: Prose, effective: DumpText, base: DumpText) -> list[Prose]:
    """Return what the file and the configuration it gives break of the three claims."""
    refusals: list[Prose] = []
    measured = digest(effective)
    if measured != RECORDED_DIGEST:
        refusals.append(
            Prose(
                f"the effective configuration is not the recorded one: recorded {RECORDED_DIGEST},"
                + f" measured {measured}"
            )
        )
    keys = own_keys(config)
    mine = option_values(effective)
    given = option_values(base)
    restated = [
        key
        for key in keys
        if key not in {_LANGUAGE, _BASE_STYLE} and key in given and mine.get(key) == given[key]
    ]
    if restated:
        refusals.append(Prose(f"these keys restate the base style: {' '.join(restated)}"))
    unknown = [key for key in keys if key != _BASE_STYLE and key not in mine]
    if unknown:
        refusals.append(
            Prose(f"the tool does not dump these keys under that name: {' '.join(unknown)}")
        )
    return refusals


def check(cpp_dir: Path) -> ExitStatus:
    """Check the ``.clang-format`` of ``cpp_dir`` against the three claims."""
    binary = Path(sys.executable).parent / "clang-format"
    if not binary.is_file():
        emit(f"check-clang-format-config: no clang-format at {binary}; install the venv's [dev]")
        return ExitStatus(2)
    dumped = run_capture([str(binary), "--dump-config"], cwd=cpp_dir, check=True)
    effective = DumpText(dumped.stdout)
    dumped = run_capture(
        [str(binary), f"--style={_BASE_STYLE_NAME}", "--dump-config"], cwd=cpp_dir, check=True
    )
    base = DumpText(dumped.stdout)
    config = Prose((cpp_dir / ".clang-format").read_text(encoding="utf-8"))
    refusals = config_refusals(config, effective, base)
    for refusal in refusals:
        emit(f"check-clang-format-config: {refusal}")
    if digest(effective) != RECORDED_DIGEST:
        emit("the configuration now in force:")
        emit(effective)
    return ExitStatus(1 if refusals else 0)


def main() -> ExitStatus:
    """Check the tree's C++ format configuration, or the one ``--cpp-dir`` names."""
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "--cpp-dir",
        type=Path,
        help="the directory whose .clang-format is held (default: the tree's cpp/)",
    )
    args = parser.parse_args()
    return check(Path(args.cpp_dir) if args.cpp_dir is not None else git_toplevel() / "cpp")


if __name__ == "__main__":
    sys.exit(main())
