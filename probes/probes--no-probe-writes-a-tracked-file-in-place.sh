#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the store itself, every probe under probes/.
# Claim: no probe writes a tracked file in place. A probe that appends a
# fixture to a source and restores it on exit is invisible to git status
# between the two, and a sweep, a hook or a commit reading the tree meanwhile
# takes the fixture for the user's change; the store has no lock and the
# sweep takes none, so a probe's only safe write is to a scratch path. Each
# probe is read for the constructs that write: at the shell level a
# redirection, sed -i, cp, mv, install, tee, touch, truncate, chmod or rm;
# in an inline Python body write_text, write_bytes, open for writing, unlink,
# touch, rename, replace, shutil's copies and moves and os's removes and
# renames. Each target is resolved through a literal, a variable the same
# probe assigns a literal, or a Path built from one, one hop through a for
# loop over a tuple; a target that resolves to a path git tracks is the
# finding. A path that reaches the write through an argument list or a
# computed name is outside the lens, which is why a probe spells every write
# under its scratch variable. The lens is first run over a scratch store of
# probes written in each shape, so a lens that reported nothing could not pass.
# Non-zero exit: a probe writes a tracked path in place, or the lens misses
# one of the shapes it is written to see, or reports a scratch write.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/store" || exit 2

# Each shape once, against paths git tracks; none of these is ever run.
cat > "$work/store/a--appends-through-a-variable.sh" <<'SH'
subject=cpp/src/enrich.cpp
cat >> "$subject" << 'CPP'
int x;
CPP
SH
cat > "$work/store/b--edits-a-literal-in-place.sh" <<'SH'
sed -i 's|^old$|new|' docs/MUTATION_BENCH.yaml
SH
cat > "$work/store/c--restores-by-copy.sh" <<'SH'
header=cpp/benchmarks/measure.hpp
cp "$work/header" "$header"
SH
cat > "$work/store/d--writes-a-path-literal.sh" <<'SH'
python3 - <<'PY'
from pathlib import Path
header = Path("cpp/include/aletheia/limits.hpp")
header.write_text("", encoding="utf-8")
PY
SH
cat > "$work/store/e--writes-through-a-loop.sh" <<'SH'
python3 - <<'PY'
from pathlib import Path
INJECTIONS = (
    (Path("cpp/src/types.cpp"), "marker"),
    (Path("cpp/tests/unit_tests_dbc.cpp"), "marker"),
)
for source, marker in INJECTIONS:
    source.write_text(marker, encoding="utf-8")
PY
SH
cat > "$work/store/f--prints-into-a-variable.sh" <<'SH'
record=docs/CPP_INDEX_LOOPS.yaml
printf '%s\n' "$original" > "$record"
SH
cat > "$work/store/h--silences-the-write.sh" <<'SH'
header=cpp/benchmarks/measure.hpp
cp "$work/header" "$header" 2> /dev/null
sed -i 's/a/b/' "$header" > /dev/null 2>&1
SH
cat > "$work/store/g--writes-only-scratch.sh" <<'SH'
work=$(mktemp -d)
tree=$work/tree
subject=cpp/src/enrich.cpp
cat >> "$tree/$subject" << 'CPP'
int x;
CPP
sed -i 's|^old$|new|' "$tree/docs/MUTATION_BENCH.yaml"
cp "$work/subject" "$tree/$subject"
python3 - "$tree" <<'PY'
import sys
from pathlib import Path
tree = Path(sys.argv[1])
INJECTIONS = ((tree / "cpp/src/types.cpp", "marker"),)
for source, marker in INJECTIONS:
    source.write_text(marker, encoding="utf-8")
header = tree / "cpp/include/aletheia/limits.hpp"
header.write_text("", encoding="utf-8")
open(f"{tree}/program.rs", "w", encoding="utf-8").write("")
PY
echo "PASS" > "$work/out.txt" 2>&1
SH

"$py" - "$work/store" probes <<'PY'
import re
import shlex
import subprocess
import sys
from pathlib import Path

tracked = set(
    subprocess.run(["git", "ls-files", "-z"], capture_output=True, text=True, check=True)
    .stdout.split("\0")
) - {""}
SHELL_LAST = {"sed", "cp", "mv", "install"}
SHELL_EVERY = {"tee", "touch", "truncate", "chmod", "rm"}
SEPARATORS = {";", "&&", "||", "|", "(", ")", "{", "}", "&"}
REDIRECTS = {">", ">>", ">&", "&>", "<", "<<", "<<<", "<&"}
HEREDOC = re.compile(r"<<-?\s*['\"]?(\w+)['\"]?")
ASSIGN = re.compile(r"^\s*(\w+)=(.*)$")
PY_WRITE = re.compile(r"(?:(\w+)|Path\(\"([^\"]+)\"\))\.(?:write_text|write_bytes)\(")
PY_PATH_OP = re.compile(r"(?:(\w+)|Path\(\"([^\"]+)\"\))\.(?:unlink|touch|rename|replace)\(")
PY_OPEN = re.compile(r"(?<![\w.])open\(\s*(?:\"([^\"]+)\"|(\w+))\s*,\s*[\"'][wax]")
PY_MODULE = re.compile(r"(?:shutil\.(?:copy|copy2|copyfile|move)|os\.(?:remove|unlink|replace|rename))\(([^)]*)\)")


def is_tracked(path: str) -> bool:
    path = path.removeprefix("./").rstrip("/")
    return path in tracked or any(t.startswith(path + "/") for t in tracked)


def shell_value(name: str, lines: list[str]) -> str | None:
    """The literal a probe assigns to a variable, or None when it is computed."""
    for line in lines:
        m = ASSIGN.match(line)
        if m and m.group(1) == name:
            value = m.group(2).strip()
            try:
                parts = shlex.split(value)
            except ValueError:
                return None
            if len(parts) != 1 or any(c in parts[0] for c in "$`("):
                return None
            return parts[0]
    return None


def resolve_shell(token: str, lines: list[str]) -> str | None:
    m = re.match(r"^\$\{?(\w+)\}?(.*)$", token)
    if m:
        value = shell_value(m.group(1), lines)
        if value is None:
            return None
        token = value + m.group(2)
    return None if "$" in token else token


def resolve_python(name: str, body: str, paths_only: bool = False) -> list[str]:
    """The literals a name is bound to, through one assignment or one for loop."""
    m = re.search(rf"^\s*{name}\s*=\s*(?:Path\(\"([^\"]+)\"\)|\"([^\"]+)\")\s*$", body, re.M)
    if m:
        return [m.group(1)] if m.group(1) else [] if paths_only else [m.group(2)]
    m = re.search(rf"^\s*for\s+[\w, ]*\b{name}\b[\w, ]*\s+in\s+(\w+)\s*:", body, re.M)
    if m:
        block = re.search(rf"^\s*{m.group(1)}\s*=\s*\(.*?^\)", body, re.M | re.S)
        if block:
            return re.findall(r"Path\(\"([^\"]+)\"\)", block.group(0))
    return []


def python_writes(body: str) -> list[tuple[str, str]]:
    found = []
    for m in PY_WRITE.finditer(body):
        for path in ([m.group(2)] if m.group(2) else resolve_python(m.group(1), body)):
            found.append((m.group(0).rstrip("("), path))
    for m in PY_PATH_OP.finditer(body):
        for path in ([m.group(2)] if m.group(2) else resolve_python(m.group(1), body, paths_only=True)):
            found.append((m.group(0).rstrip("("), path))
    for m in PY_OPEN.finditer(body):
        for path in ([m.group(1)] if m.group(1) else resolve_python(m.group(2), body)):
            found.append(("open for writing", path))
    for m in PY_MODULE.finditer(body):
        for arg in m.group(1).split(","):
            arg = arg.strip()
            literal = re.fullmatch(r"\"([^\"]+)\"", arg)
            for path in ([literal.group(1)] if literal else resolve_python(arg, body) if arg.isidentifier() else []):
                found.append((m.group(0).split("(")[0], path))
    return found


def scan(probe: Path) -> list[str]:
    lines = probe.read_text(encoding="utf-8").splitlines()
    findings = []
    shell = []
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        tag = HEREDOC.search(line)
        shell.append(line)
        if not tag or "<<<" in line:
            continue
        body = []
        while i < len(lines) and lines[i].strip() != tag.group(1):
            body.append(lines[i])
            i += 1
        i += 1
        for construct, path in python_writes("\n".join(body)):
            if is_tracked(path):
                findings.append(f"{probe.name}: {construct} writes {path}")
    for line in shell:
        if line.lstrip().startswith("#"):
            continue
        lexer = shlex.shlex(line, posix=True, punctuation_chars=True)
        lexer.whitespace_split = True
        try:
            tokens = list(lexer)
        except ValueError:
            continue
        command = []
        skip = False
        for index, token in enumerate(tokens + [";"]):
            if skip:
                skip = False
            elif token in SEPARATORS:
                if command and command[0] in SHELL_LAST | SHELL_EVERY:
                    targets = command[-1:] if command[0] in SHELL_LAST else [t for t in command[1:] if not t.startswith("-")]
                    if command[0] == "sed" and not any(t.startswith("-i") for t in command):
                        targets = []
                    for target in targets:
                        path = resolve_shell(target, shell)
                        if path and is_tracked(path):
                            findings.append(f"{probe.name}: {command[0]} writes {path}")
                command = []
            elif token in REDIRECTS:
                # A redirection and its word are not the command's arguments,
                # nor is the descriptor digit that may precede it.
                if command and command[-1].isdigit():
                    command.pop()
                skip = True
                target = tokens[index + 1] if token in (">", ">>") and index + 1 < len(tokens) else None
                path = resolve_shell(target, shell) if target else None
                if path and is_tracked(path):
                    findings.append(f"{probe.name}: {token} writes {path}")
            else:
                command.append(token)
    return findings


def store(directory: str, skip: set[str]) -> list[str]:
    found = []
    for probe in sorted(Path(directory).glob("*.sh")):
        if probe.name not in skip:
            found.extend(scan(probe))
    return found


expected = {
    "a--appends-through-a-variable.sh: >> writes cpp/src/enrich.cpp",
    "b--edits-a-literal-in-place.sh: sed writes docs/MUTATION_BENCH.yaml",
    "c--restores-by-copy.sh: cp writes cpp/benchmarks/measure.hpp",
    "d--writes-a-path-literal.sh: header.write_text writes cpp/include/aletheia/limits.hpp",
    "e--writes-through-a-loop.sh: source.write_text writes cpp/src/types.cpp",
    "e--writes-through-a-loop.sh: source.write_text writes cpp/tests/unit_tests_dbc.cpp",
    "f--prints-into-a-variable.sh: > writes docs/CPP_INDEX_LOOPS.yaml",
    "h--silences-the-write.sh: cp writes cpp/benchmarks/measure.hpp",
    "h--silences-the-write.sh: sed writes cpp/benchmarks/measure.hpp",
}
rehearsal = set(store(sys.argv[1], set()))
if rehearsal != expected:
    print("the lens does not read the shapes it is written to see:")
    for line in sorted(expected - rehearsal):
        print(f"  missed   {line}")
    for line in sorted(rehearsal - expected):
        print(f"  unexpected {line}")
    sys.exit(1)

findings = store(sys.argv[2], {"run_all.sh", "probes--no-probe-writes-a-tracked-file-in-place.sh"})
if findings:
    print("a probe writes a tracked file in place:")
    for line in dict.fromkeys(findings):
        print(f"  {line}")
    sys.exit(1)
print("PASS: every write a probe spells lands outside the tracked tree")
PY
