#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_ci_steps.py.
# Claim: the clang-format step's file list is every tracked C++ source of the
# whole tree, so no build tree can enter it however many of them exist and no
# tracked source sits outside it. Two C++ sources live outside the binding, and
# a listing taken from the binding's directory never saw them.
# Non-zero exit: the step's command walks the filesystem instead of asking git,
# its list misses a tracked source, it picks up a file under a build tree, or it
# does not name the style, which the sources outside the binding have no
# configuration above them to supply. Exits 2 when the step cannot be read.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
cmd=$("$py" - <<'PY'
import re
from pathlib import Path
text = Path("tools/_ci_steps.py").read_text(encoding="utf-8")
match = re.search(r"clang_format_cmd = \(\n(.*?)\n    \)\n", text, re.S)
print(match.group(1) if match else "")
PY
)
[ -n "$cmd" ] || { echo "the clang-format command could not be read"; exit 2; }
case $cmd in
    *"git ls-files"*) ;;
    *) echo "the command does not ask git for its file list: $cmd"; exit 1 ;;
esac
case $cmd in
    *find\ .*) echo "the command still walks the filesystem: $cmd"; exit 1 ;;
esac

case $cmd in
    *--style=file:cpp/.clang-format*) ;;
    *) echo "the command does not name the style: $cmd"; exit 1 ;;
esac

# The list git gives and the list the gate must cover are the same set, and a
# build tree is in neither.
tracked=$(git ls-files -- '*.cpp' '*.hpp' | wc -l)
[ "$tracked" -gt 0 ] || { echo "git lists no C++ source"; exit 1; }
git ls-files -- '*.cpp' '*.hpp' | grep -q '/build' && {
    echo "a build tree is tracked, so the list cannot exclude one"
    exit 1
}
git ls-files -- '*.cpp' | grep -qx 'cpp/src/types.cpp' || {
    echo "the list misses a source in the binding"
    exit 1
}
# The two outside the binding are the reason this gate was widened.
outside=$(git ls-files -- '*.cpp' '*.hpp' | grep -cv '^cpp/')
[ "$outside" -gt 0 ] || {
    echo "no tracked C++ source lives outside the binding, so this widening has no subject"
    exit 1
}
# And every one of them conforms, which a listing from the binding never checked.
git ls-files -z -- '*.cpp' '*.hpp' |
    xargs -0 -r clang-format-22 --style=file:cpp/.clang-format --dry-run --Werror || {
    echo "a tracked C++ source does not conform"
    exit 1
}
echo "PASS: the gate covers all $tracked tracked C++ sources, $outside of them outside the binding"
exit 0
