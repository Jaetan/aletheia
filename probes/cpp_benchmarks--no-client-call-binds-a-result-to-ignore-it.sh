#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/benchmark.cpp and cpp/benchmarks/stability_bench.cpp.
# Claim: no client call in either harness binds its result to a variable in
# order to ignore it. Every client method returns a std::expected marked
# nodiscard, so a bare discard is refused by the lint gate; the binding to a
# [[maybe_unused]] local is the one shape that passes the gate and still
# throws the result away, and it is the shape under which a failing operation
# was timed as a success. Each file is read as one line, because the formatter
# breaks a long binding across lines and a per-line pattern would miss it.
# Non-zero exit: a binding of that shape is back in a harness.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
for file in cpp/benchmarks/benchmark.cpp cpp/benchmarks/stability_bench.cpp; do
    hits=$(tr '\n' ' ' < "$file" | grep -oE '\[\[maybe_unused\]\] auto const [a-z_]+ = *client\.[a-z_]+\(' || true)
    [ -z "$hits" ] || {
        echo "$file binds a client result to ignore it:"
        printf '%s\n' "$hits" | sed 's/^/    /'
        status=1
    }
done
exit "$status"
