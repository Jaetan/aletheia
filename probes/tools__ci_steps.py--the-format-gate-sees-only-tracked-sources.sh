# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_ci_steps.py.
# Claim: the clang-format step's file list comes from what the repository
# tracks, so no build tree can enter it however many of them exist, while an
# unformatted tracked source is still seen. Non-zero exit: the step's command
# walks the filesystem instead of asking git, or its list misses a tracked
# source, or it picks up a file under a build tree. Exits 2 when the step
# cannot be read.
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

# The list git gives and the list the gate must cover are the same set, and a
# build tree is in neither.
tracked=$(git ls-files -- 'cpp/*.cpp' 'cpp/*.hpp' | wc -l)
[ "$tracked" -gt 0 ] || { echo "git lists no C++ source under cpp/"; exit 1; }
git ls-files -- 'cpp/*.cpp' 'cpp/*.hpp' | grep -q '/build' && {
    echo "a build tree is tracked, so the list cannot exclude one"
    exit 1
}
git ls-files -- 'cpp/*.cpp' | grep -qx 'cpp/src/types.cpp' || {
    echo "the list misses a source the gate must cover"
    exit 1
}
exit 0
