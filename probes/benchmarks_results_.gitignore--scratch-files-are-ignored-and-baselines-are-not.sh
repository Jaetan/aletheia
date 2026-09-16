#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/results/.gitignore.
# Claim: the three scratch-file shapes the harness creates and a killed run can
# leave behind are ignored, a lane's result file is ignored, and a committed
# baseline is not. Non-zero exit: a scratch or result file would show up in
# git status, or a baseline would be hidden from it.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
for scratch in .tmp.Go.abc123 .err.Go.abc123 .json.Go.abc123 go_throughput.json; do
    git check-ignore -q "benchmarks/results/$scratch" || {
        echo "not ignored: benchmarks/results/$scratch"; status=1
    }
done
if git check-ignore -q benchmarks/results/go_throughput_baseline.json; then
    echo "a baseline is ignored"; status=1
fi
exit $status
