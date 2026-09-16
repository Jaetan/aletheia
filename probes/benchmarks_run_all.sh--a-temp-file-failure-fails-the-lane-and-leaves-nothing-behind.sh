#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: a lane whose scratch file cannot be created is reported as FAIL, the
# run exits non-zero, and no scratch file is left in the results directory:
# in particular, when the first of a lane's two temp files is created and the
# second is not, the first is removed. Runs the harness with an mktemp that
# refuses the second template. Non-zero exit: a lane survived the failure, the
# run exited zero, or a scratch file was orphaned. Exits 2 when the kernel
# library, the venv or cpp/build is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
[ -f python/.venv/bin/activate ] || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
mkdir -p "$dir/bin"
real=$(command -v mktemp) || exit 2
cat > "$dir/bin/mktemp" <<SHIM
#!/bin/sh
case "\$*" in *.err.*) echo "probe: mktemp refused" >&2; exit 1 ;; esac
exec "$real" "\$@"
SHIM
chmod +x "$dir/bin/mktemp"
out=$(PATH="$dir/bin:$PATH" ALETHEIA_BENCH_RESULTS_DIR="$dir/results" \
    bash benchmarks/run_all.sh --frames 1 --runs 1 --bench throughput 2>&1)
rc=$?
status=0
[ "$rc" -ne 0 ] || { echo "the run exited zero with every scratch file refused"; status=1; }
grep -q "could not create a temp file" <<< "$out" || { echo "the refusal was not reported"; status=1; }
grep -q "Saved:" <<< "$out" && { echo "a lane saved a result without its scratch files"; status=1; }
left=$(find "$dir/results" -name '.*' -type f 2>/dev/null)
[ -z "$left" ] || { echo "scratch files left behind:"; echo "$left"; status=1; }
exit $status
