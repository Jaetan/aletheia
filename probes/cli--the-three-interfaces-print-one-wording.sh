#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/cmd/aletheia/main.go, cpp/src/cli/cli.cpp and python/aletheia/cli.py.
# Claim: the sentences all three command-line interfaces print for one question
# are one wording. Three of them are carried in three places and nothing else
# holds them together: the message header of mux-query, the line for a message
# that is not multiplexed, and the line for one multiplexor value. The Go and
# the C++ usage screens are a fourth, identical but for the tool name and the
# binding label.
# The comparison is of what the binaries print, not of their source, the three
# languages spelling a format string three ways. Python's own layout is left
# out of it: its summary opens a blank line and a multiplexor roster the other
# two do not print, and its selector lists each signal with its bit range, so
# blank lines and the roster are dropped before comparing and the selector is
# compared on its first two lines.
# The binaries are built, never found: one left over from before a wording
# change would compare against itself.
# Non-zero exit: an interface has drifted from the shared wording.
# Exits 2 without Go, without a configured C++ tree, without the venv, or
# without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/go-cli" ./cmd/aletheia) || exit 2
cmake --build cpp/build --target aletheia-cli > /dev/null 2>&1 || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
"$py" - "$work" <<'PY'
import subprocess
import sys
from pathlib import Path

work = Path(sys.argv[1])
mux = str(Path("python/tests/fixtures/dbc_corpus/multiplexing.dbc").resolve())
plain = str(Path("python/tests/fixtures/dbc_corpus/minimal.dbc").resolve())
bad = []


def run(binding, args, cwd=None):
    argv = {"go": [str(work / "go-cli")],
            "cpp": ["cpp/build/aletheia-cli"],
            "python": [".venv/bin/python", "-m", "aletheia"]}[binding]
    r = subprocess.run(argv + args, capture_output=True, text=True, check=False,
                       cwd=cwd or ("python" if binding == "python" else None))
    if r.returncode != 0:
        bad.append(f"{binding} {' '.join(args)} exited {r.returncode}: {r.stderr.strip()[:200]}")
        return []
    return r.stdout.split("\n")


def shared(lines):
    """The lines all three print: Python's blanks and its roster are its own."""
    return [ln for ln in lines if ln.strip() and not ln.strip().startswith("Multiplexors:")]


def agree(label, per_binding):
    first = next(iter(per_binding.values()))
    for binding, got in per_binding.items():
        if got != first:
            bad.append(f"{label}: {binding} prints\n      " + "\n      ".join(got)
                       + "\n    where another prints\n      " + "\n      ".join(first))
            return


agree("the mux-query summary of a multiplexed message",
      {b: shared(run(b, ["mux-query", "--dbc", mux, "0x64"])) for b in ("go", "cpp", "python")})
agree("the mux-query summary of a message that is not multiplexed",
      {b: shared(run(b, ["mux-query", "--dbc", plain, "0x100"])) for b in ("go", "cpp", "python")})
agree("the mux-query selector's first two lines",
      {b: shared(run(b, ["mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"]))[:2]
       for b in ("go", "cpp", "python")})

# The usage screens, which Python does not have in this shape: it is argparse's,
# and argparse writes its own. Go and C++ carry one text between them.
def usage(binding):
    argv = {"go": [str(work / "go-cli")], "cpp": ["cpp/build/aletheia-cli"]}[binding]
    out = subprocess.run(argv, capture_output=True, text=True, check=False)
    text = (out.stdout + out.stderr).replace("aletheia-cli", "aletheia")
    return text.replace("(C++ CLI)", "(CLI)").replace("(Go CLI)", "(CLI)").split("\n")


agree("the usage screen", {b: usage(b) for b in ("go", "cpp")})

if bad:
    print("the command-line interfaces do not print one wording:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print("PASS: the shared sentences are one wording across the three interfaces")
PY
