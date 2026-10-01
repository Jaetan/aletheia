#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the Haskell toolchain steps of .github/workflows/.
# Claim: every job that installs Agda sets up GHC and the cabal store one way.
# GHC is restored from one key into the directory ghcup installs it to, named
# by ghcup itself, installed by ghcup only where the restore missed and checked
# to have landed there, saved under the same key, and that directory's bin/ is
# put on PATH. A kernel library restored from the build-tree cache names GHC's
# library directory in its RUNPATH, so a compiler cached anywhere else leaves
# it unable to load its runtime. The store is restored and saved under one
# key that hashes shake.cabal, the restore falls back to the key's prefix, the
# package index is refreshed only where nothing was restored, and the shake
# executable's dependencies are built between the Agda install and the save,
# so the store a job saves holds them. A job set up another way pays the
# install the cache exists to skip, or saves a store the next job compiles
# into again.
# Non-zero exit: a job that installs Agda departs from any of that, or no such
# job is found. Exits 2 when the interpreter or its YAML reader is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
exec "$py" - <<'PY'
import sys
from pathlib import Path

import yaml

GHC_DIR = "${{ env.GHC_DIR }}"
GHC_KEY = "ghc${{ env.GHC_VERSION }}-noble-v2"
GHC_BASE = 'ghc_dir="$(ghcup whereis basedir)/ghc/${GHC_VERSION}"'
GHC_ENV = 'echo "GHC_DIR=${ghc_dir}" >> "${GITHUB_ENV}"'
GHC_PATH_LINE = 'echo "${ghc_dir}/bin"'
GHC_INSTALL = 'ghcup install ghc "${GHC_VERSION}" --set'
GHC_LANDED = '[ "${installed}" = "${GHC_DIR}/bin" ]'
STORE_PREFIX = "cabal-${{ runner.os }}-ghc${{ env.GHC_VERSION }}-agda${{ env.AGDA_VERSION }}-"
STORE_KEY = STORE_PREFIX + "${{ hashFiles('shake.cabal') }}-v3"
SHAKE_DEPS = "cabal build --only-dependencies aletheia-build:exe:shake"
AGDA_INSTALL = 'cabal install "Agda-${AGDA_VERSION}"'

faults = []
jobs = 0
for path in sorted(Path(".github/workflows").glob("*.yml")):
    doc = yaml.safe_load(path.read_text(encoding="utf-8"))
    for name, job in (doc.get("jobs") or {}).items():
        steps = job.get("steps") or []
        runs = [str(step.get("run", "")) for step in steps]
        agda = [i for i, run in enumerate(runs) if AGDA_INSTALL in run]
        if not agda:
            continue
        jobs += 1
        where = f"{path.name}:{name}"

        def fault(text, where=where):
            faults.append(f"{where}: {text}")

        def cache_steps(kind, key_start):
            return [
                (i, step) for i, step in enumerate(steps)
                if f"actions/cache/{kind}@" in str(step.get("uses", ""))
                and str((step.get("with") or {}).get("key", "")).startswith(key_start)
            ]

        setup = [
            i for i, run in enumerate(runs)
            if GHC_BASE in run and GHC_ENV in run and GHC_PATH_LINE in run and '>> "${GITHUB_PATH}"' in run
        ]
        if len(setup) != 1:
            fault("does not name GHC's directory from ghcup and put its bin/ on PATH, once")
        ghc_restore = cache_steps("restore", "ghc")
        ghc_save = cache_steps("save", "ghc")
        installs = [i for i, run in enumerate(runs) if "ghcup install ghc" in run]
        if any(GHC_INSTALL not in runs[i] or GHC_LANDED not in runs[i] for i in installs):
            fault("installs GHC other than with ghcup's own layout, checked to land under GHC_DIR")
        if len(ghc_restore) != 1 or len(ghc_save) != 1 or len(installs) != 1:
            fault("does not restore, install on a miss and save GHC exactly once each")
        else:
            (r, restore), (s, save) = ghc_restore[0], ghc_save[0]
            for step in (restore, save):
                if step["with"].get("path") != GHC_DIR or step["with"].get("key") != GHC_KEY:
                    fault(f"caches GHC as {step['with'].get('path')} under {step['with'].get('key')}")
            gate = f"steps.{restore.get('id')}.outputs.cache-hit != 'true'"
            for i in (installs[0], s):
                if gate not in str(steps[i].get("if", "")):
                    fault(f"step {steps[i].get('name')!r} runs whatever the GHC restore found")
            if not (len(setup) == 1 and setup[0] < r < installs[0] < s < agda[0]):
                fault("does not name, restore, install and save GHC, in that order, ahead of the Agda install")

        store_restore = cache_steps("restore", "cabal-")
        store_save = cache_steps("save", "cabal-")
        deps = [i for i, run in enumerate(runs) if SHAKE_DEPS in run]
        if len(store_restore) != 1 or len(store_save) != 1 or len(deps) != 1:
            fault("does not restore, fill with shake's dependencies and save the store exactly once each")
            continue
        (r, restore), (s, save) = store_restore[0], store_save[0]
        for step in (restore, save):
            if step["with"].get("key") != STORE_KEY:
                fault(f"keys the store as {step['with'].get('key')}")
        if str(restore["with"].get("restore-keys", "")).strip() != STORE_PREFIX:
            fault("restores no store under the key's prefix")
        if not r < agda[0] < deps[0] < s:
            fault("does not build shake's dependencies between the Agda install and the store save")
        refresh = [i for i, run in enumerate(runs) if run.strip() == "cabal update"]
        matched = f"steps.{restore.get('id')}.outputs.cache-matched-key == ''"
        if len(refresh) != 1 or matched not in str(steps[refresh[0]].get("if", "")):
            fault("refreshes the package index where a store was restored")

for line in faults:
    print(line)
if jobs == 0:
    print("no job installs Agda")
    sys.exit(1)
if faults:
    sys.exit(1)
print(f"PASS: {jobs} jobs set up GHC and the store one way")
PY
