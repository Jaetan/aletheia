#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md.
# Claim: every pip extra the README names in a bracketed token such as `[can]`
# is an extra python/pyproject.toml defines, so a reader who follows the
# install sentence pulls a loader that exists.
# Non-zero exit: the README names an extra the manifest does not define.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import re, sys, tomllib
extras = set(tomllib.load(open("python/pyproject.toml", "rb"))["project"]["optional-dependencies"])
text = open("README.md", encoding="utf-8").read()
named = set(re.findall(r"`\[([a-z,]+)\]`", text)) | set(re.findall(r"\.\[([a-z,]+)\]'", text))
named = {n for group in named for n in group.split(",")}
if not named:
    print("README.md names no extra; the probe would pass vacuously"); sys.exit(2)
missing = sorted(named - extras)
if missing:
    print(f"README.md names extras pyproject does not define: {missing}"); sys.exit(1)
print(f"PASS: all {len(named)} extras the README names exist: {sorted(named)}")
PY
