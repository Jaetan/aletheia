# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold three facts about the installed Mull plugin that the mutation build is written on.

The plugin ``~/.local/bin/mull-ir-frontend-23`` is the Mull release
``tools/build_mull.sh`` builds with the patches under ``tools/mull/``, and the
mutation build of ``cpp/CMakeLists.txt`` and the sweep of ``tools/mutation_cpp.py``
rest on what that plugin does.  Each fact is shown by running the toolchain's
clang with the plugin, so the gate runs when the plugin's release or patches,
the configuration naming its mutators, the line of the build that withholds a
flag from it, or the toolchain moves (``tools/pin_scope.py``).

* The plugin crashes clang under ``-ffile-prefix-map``: it resolves the mapped
  source path against the compiler's working directory, which no build
  directory holds, so the build withholds the flag from the mutation tree.
  Shown by compiling ``cpp/src/types.cpp`` from a scratch directory with the
  flag: the compile ends by the compiler's signal, status 139, or the driver
  reports that exit code.  A compile that succeeds refuses the fact, and the
  build can apply the flag.
* Every mutant identifier the plugin emits names one clone: it carries a
  seventh part, a hash of the function's mangled name and an ordinal, and no
  identifier is stored by two trampolines, so two mutations of one statement
  or two instantiations of one template never share a name.  Shown from the
  IR of ``cpp/src/json_parse.cpp``, a unit whose functions carry mutants of
  several mutators, under the whole configuration ``cpp/mull.yml``.
* The call mutators reach a call through a function pointer, which is how the
  backend calls every kernel entry.  Shown from the IR of
  ``cpp/src/ffi_backend.cpp``: the void-call mutator has a mutant on the line
  that closes the kernel state, the scalar-call mutator on the line that
  builds a frame, and the pointer-call mutator on the line that processes a
  command.

The IR is emitted with the compile command a configured mutation tree records
for the unit, the first of ``cpp/build-mutation`` and its three slices holding
``compile_commands.json``, with ``MULL_CONFIG`` naming the whole configuration
so every mutator fires whatever tree the command came from.

Exits 0 when every fact holds or nothing it rests on moved, 1 naming each fact
that no longer holds, and 2 when a fact cannot be reached: clang++-23 or the
plugin is absent, no mutation tree is configured, a compile fails for another
reason (which a plugin built without its patches does too, its scalar-call
mutator aborting clang on a bool-returning call, so a lost patch reads as this
and not as a refusal), the IR holds no mutant, or a source line the third fact
names no longer exists.  Every finding is printed before the exit.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import signal
import sys
import tempfile
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

from tools._common import RelPath, emit, find_executable, git_toplevel, run_capture
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping

# The text of a compiled unit's LLVM IR, and what a compile printed.
IrText = NewType("IrText", str)
ToolOutput = NewType("ToolOutput", str)
# A mutant identifier as the plugin spells it, a mutator's name, which is its
# first part, and the name of a function the IR defines.
MutantId = NewType("MutantId", str)
MutatorName = NewType("MutatorName", str)
FunctionName = NewType("FunctionName", str)
# A line's number in a source file, from 1, and a regular expression over a line.
LineNumber = NewType("LineNumber", int)
LinePattern = NewType("LinePattern", str)
# A source file's text, and a unit's file name under cpp/src/.
SourceText = NewType("SourceText", str)
UnitName = NewType("UnitName", str)
# The compiler's path on this host, one word of a compile command, a whole
# command as one string, and the directory a command runs from.
CompilerPath = NewType("CompilerPath", str)
CompileArg = NewType("CompileArg", str)
CommandLine = NewType("CommandLine", str)
DirectoryName = NewType("DirectoryName", str)

GATE = "check-mull-plugin-facts"
CLANG = "clang++-23"
# A compiler the kernel ended with SIGSEGV, as the shell reports it, 128 plus the
# signal, and as a Python parent reads it, the signal negated.
CRASHED = ExitStatus(139)
CRASHED_SIGNAL = ExitStatus(-signal.SIGSEGV)
REFUSAL = ExitStatus(1)
NO_ANSWER = ExitStatus(2)
# How many of a compile's last lines a finding carries.
TAIL_LINES = 8

PREFIX_MAP_UNIT = RelPath("cpp/src/types.cpp")
IDENTIFIERS_UNIT = UnitName("json_parse.cpp")
REACH_UNIT = UnitName("ffi_backend.cpp")
MULL_CONFIG = RelPath("cpp/mull.yml")
# The configured trees, in the order one is taken.
MUTATION_TREES = (
    RelPath("cpp/build-mutation"),
    RelPath("cpp/build-mutation-1"),
    RelPath("cpp/build-mutation-2"),
    RelPath("cpp/build-mutation-3"),
)
COMPILE_DATABASE = "compile_commands.json"

# A mutant identifier: mutator, path, start line and column, end line and
# column, then the seventh part, the function's hash and the mutant's ordinal.
IDENTIFIER_SHAPE = re.compile(r"^[a-z_]+:.+:\d+:\d+:\d+:\d+:[0-9a-f]{1,8}\.\d+$")
# The mutator and the source line of an identifier a trampoline stores, in one unit.
_SITE = r'store ptr @"(cxx_[a-z_]+|negate_mutator):[^"]*?/cpp/src/{unit}:(\d+):(\d+):'
# The lines of the backend the call mutators must reach, by the mutator that reaches each.
REACHED_CALLS: Mapping[MutatorName, LinePattern] = {
    MutatorName("cxx_remove_void_call"): LinePattern(r"fns_\.close\(state\)"),
    MutatorName("cxx_replace_scalar_call"): LinePattern(r"fns_\.build_frame_bin\("),
    MutatorName("cxx_replace_pointer_call_null"): LinePattern(r"fns_\.process\(state"),
}


class Finding(NamedTuple):
    """What an arm found: a refusal or no answer, and the line saying which."""

    status: ExitStatus
    message: Prose


class CompileEntry(TypedDict):
    """One compile database entry, as CMake writes it: where the command runs and what it is."""

    directory: DirectoryName
    file: RelPath
    command: CommandLine


def plugin_path() -> Path:
    """Return where the mutation lane and the build look for the plugin."""
    return Path.home() / ".local" / "bin" / "mull-ir-frontend-23"


def _tail(output: ToolOutput) -> Prose:
    """Return the last lines of what a compile printed."""
    return Prose("\n".join(output.splitlines()[-TAIL_LINES:]))


def prefix_map_verdict(status: ExitStatus, output: ToolOutput) -> ExitStatus:
    """Read the ending of the compile under ``-ffile-prefix-map``.

    The compiler's crash is the fact: 0 is the refusal, the SIGSEGV ending or
    ``exit code 139`` from the driver is the fact, and any other ending is no
    answer.
    """
    if status == 0:
        return REFUSAL
    if status in {CRASHED, CRASHED_SIGNAL} or f"exit code {CRASHED}" in output:
        return ExitStatus(0)
    return NO_ANSWER


def identifier_owners(ir_text: IrText) -> Mapping[MutantId, frozenset[FunctionName]]:
    """Map every identifier a function body stores to the functions storing it.

    A function's body runs from its ``define`` line to the ``}`` closing it;
    a store outside any body belongs to no function and is not counted.
    """
    owners: dict[MutantId, set[FunctionName]] = {}
    current: FunctionName | None = None
    for line in ir_text.split("\n"):
        if line.startswith("define "):
            current = FunctionName(line.split("@", 1)[1].split("(")[0].strip('"'))
        elif line == "}":
            current = None
        elif current is not None and 'store ptr @"cxx_' in line:
            identifier = MutantId(line.split('@"', 1)[1].split('"', 1)[0])
            owners.setdefault(identifier, set()).add(current)
    return {identifier: frozenset(names) for identifier, names in owners.items()}


def identifier_findings(owners: Mapping[MutantId, frozenset[FunctionName]]) -> list[Finding]:
    """Refuse an identifier off its shape or stored by two functions; none at all is no answer."""
    if not owners:
        return [
            Finding(
                NO_ANSWER, Prose(f"no mutant identifier in the IR of cpp/src/{IDENTIFIERS_UNIT}")
            )
        ]
    findings = [
        Finding(REFUSAL, Prose(f"no seventh part: {identifier}"))
        for identifier in sorted(owners)
        if not IDENTIFIER_SHAPE.match(identifier)
    ]
    findings.extend(
        Finding(REFUSAL, Prose(f"shared by {len(names)} trampolines: {identifier}"))
        for identifier, names in sorted(owners.items())
        if len(names) > 1
    )
    return findings


def mutant_sites(ir_text: IrText, unit: UnitName) -> set[tuple[MutatorName, LineNumber]]:
    """Return the mutator and source line of every identifier stored for ``unit``."""
    site = re.compile(_SITE.format(unit=re.escape(unit)))
    return {
        (MutatorName(match.group(1)), LineNumber(int(match.group(2))))
        for match in site.finditer(ir_text)
    }


def lines_matching(source: SourceText, pattern: LinePattern) -> set[LineNumber]:
    """Return the numbers of the lines of ``source`` that ``pattern`` matches."""
    return {
        LineNumber(number)
        for number, text in enumerate(source.split("\n"), start=1)
        if re.search(pattern, text)
    }


def reach_findings(
    sites: Iterable[tuple[MutatorName, LineNumber]], source: SourceText
) -> list[Finding]:
    """Check that each call mutator has a mutant on the line its pattern names.

    A pattern matching no line of the source is the gate's own staleness, so
    it is no answer rather than a refusal; a line found with no such mutant
    refuses.
    """
    reached = set(sites)
    findings: list[Finding] = []
    for mutator, pattern in REACHED_CALLS.items():
        wanted = lines_matching(source, pattern)
        if not wanted:
            findings.append(
                Finding(NO_ANSWER, Prose(f"no line of cpp/src/{REACH_UNIT} matches {pattern}"))
            )
        elif not any((mutator, line) in reached for line in wanted):
            findings.append(
                Finding(
                    REFUSAL,
                    Prose(
                        f"no {mutator} mutant on line(s) {sorted(wanted)} of cpp/src/{REACH_UNIT}"
                    ),
                )
            )
    return findings


def verdict(findings: Iterable[Finding]) -> ExitStatus:
    """Return the gate's exit: a refusal outranks no answer, and nothing found passes."""
    statuses = {finding.status for finding in findings}
    if REFUSAL in statuses:
        return REFUSAL
    if statuses:
        return NO_ANSWER
    return ExitStatus(0)


def unit_entries(database: Prose, unit: UnitName) -> list[CompileEntry]:
    """Return the entries of a compile database compiling ``unit`` under cpp/src/."""
    entries = cast("list[CompileEntry]", json.loads(database))
    return [entry for entry in entries if entry["file"].endswith(f"/cpp/src/{unit}")]


def ir_command(entry: CompileEntry, ir_path: Path) -> list[CompileArg]:
    """Turn an entry's compile command into one emitting the unit's IR at ``ir_path``."""
    kept: list[CompileArg] = []
    skip = False
    for word in shlex.split(entry["command"]):
        if skip:
            skip = False
        elif word == "-o":
            skip = True
        elif word != "-c":
            kept.append(CompileArg(word))
    added = [CompileArg("-S"), CompileArg("-emit-llvm"), CompileArg("-o"), CompileArg(str(ir_path))]
    return [*kept, *added]


def configured_tree(repo_root: Path) -> Path | None:
    """Return the first mutation tree holding a compile database, or None."""
    for tree in MUTATION_TREES:
        if (repo_root / tree / COMPILE_DATABASE).is_file():
            return repo_root / tree
    return None


def prefix_map_arm(
    repo_root: Path, clang: CompilerPath, plugin: Path, scratch: Path
) -> list[Finding]:
    """Compile one library source under the plugin and the flag, from the scratch directory."""
    ran = run_capture(
        [
            clang,
            "-std=c++23",
            f"-fpass-plugin={plugin}",
            "-g",
            "-O0",
            f"-ffile-prefix-map={repo_root}=.",
            f"-fcrash-diagnostics-dir={scratch}",
            f"-I{repo_root / 'cpp' / 'include'}",
            f"-I{repo_root / 'cpp' / 'src'}",
            "-c",
            str(repo_root / PREFIX_MAP_UNIT),
            "-o",
            str(scratch / "types.o"),
        ],
        cwd=scratch,
    )
    output = ToolOutput(ran.stdout + ran.stderr)
    status = ExitStatus(ran.returncode)
    read = prefix_map_verdict(status, output)
    if read == REFUSAL:
        return [
            Finding(
                REFUSAL,
                Prose(
                    "the plugin now accepts -ffile-prefix-map;"
                    + " cpp/CMakeLists.txt can apply it to the mutation build"
                ),
            )
        ]
    if read == NO_ANSWER:
        return [
            Finding(
                NO_ANSWER,
                Prose(
                    f"{CLANG} ended with status {status} compiling {PREFIX_MAP_UNIT} under the"
                    + f" plugin, neither 0 nor SIGSEGV:\n{_tail(output)}"
                ),
            )
        ]
    return []


def emit_ir(repo_root: Path, tree: Path, unit: UnitName, scratch: Path) -> IrText | Finding:
    """Emit ``unit``'s IR with the tree's compile command under the whole configuration."""
    database = tree / COMPILE_DATABASE
    entries = unit_entries(Prose(database.read_text(encoding="utf-8")), unit)
    if len(entries) != 1:
        return Finding(
            NO_ANSWER, Prose(f"{database} names /cpp/src/{unit} {len(entries)} times, not once")
        )
    ir_path = scratch / f"{unit}.ll"
    ran = run_capture(
        [*ir_command(entries[0], ir_path)],
        cwd=Path(entries[0]["directory"]),
        env=os.environ | {"MULL_CONFIG": str(repo_root / MULL_CONFIG)},
    )
    if ran.returncode != 0:
        return Finding(
            NO_ANSWER,
            Prose(
                f"{CLANG} could not emit the IR of cpp/src/{unit} (status {ran.returncode});"
                + " a plugin built without the patches under tools/mull/ ends this way too,"
                + " its scalar-call mutator aborting clang on a bool-returning call:\n"
                + _tail(ToolOutput(ran.stdout + ran.stderr))
            ),
        )
    return IrText(ir_path.read_text(encoding="utf-8", errors="replace"))


def identifiers_arm(repo_root: Path, tree: Path, scratch: Path) -> list[Finding]:
    """Check every identifier of the reader unit's IR for its shape and its one owner."""
    ir_text = emit_ir(repo_root, tree, IDENTIFIERS_UNIT, scratch)
    if isinstance(ir_text, Finding):
        return [ir_text]
    return identifier_findings(identifier_owners(ir_text))


def reach_arm(repo_root: Path, tree: Path, scratch: Path) -> list[Finding]:
    """Check that the call mutators reach the backend's calls through its function pointers."""
    ir_text = emit_ir(repo_root, tree, REACH_UNIT, scratch)
    if isinstance(ir_text, Finding):
        return [ir_text]
    source = SourceText((repo_root / "cpp" / "src" / REACH_UNIT).read_text(encoding="utf-8"))
    return reach_findings(mutant_sites(ir_text, REACH_UNIT), source)


def check(repo_root: Path) -> ExitStatus:
    """Run the three arms in order, print every finding, and return the verdict."""
    try:
        clang = CompilerPath(find_executable(CLANG))
    except RuntimeError as missing:
        emit(f"{GATE}: {missing}")
        return NO_ANSWER
    plugin = plugin_path()
    if not plugin.is_file():
        emit(f"{GATE}: Mull plugin not found at {plugin}; tools/build_mull.sh installs it")
        return NO_ANSWER
    findings: list[Finding] = []
    with tempfile.TemporaryDirectory(prefix="mull-plugin-facts-") as scratch_name:
        scratch = Path(scratch_name)
        findings.extend(prefix_map_arm(repo_root, clang, plugin, scratch))
        tree = configured_tree(repo_root)
        if tree is None:
            findings.append(
                Finding(
                    NO_ANSWER,
                    Prose(
                        f"no configured mutation tree: none of {', '.join(MUTATION_TREES)} under"
                        + f" {repo_root} holds {COMPILE_DATABASE}"
                    ),
                )
            )
        else:
            findings.extend(identifiers_arm(repo_root, tree, scratch))
            findings.extend(reach_arm(repo_root, tree, scratch))
    for finding in findings:
        emit(f"{GATE}: {finding.message}")
    return verdict(findings)


def main() -> ExitStatus:
    """Check the plugin facts when the branch moves what they rest on."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.MULL_PLUGIN_FACTS, repo_root):
        return ExitStatus(0)
    return check(repo_root)


if __name__ == "__main__":
    sys.exit(main())
