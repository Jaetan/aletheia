#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: each compiled harness is built where the runner is told and run from
# there: the C++ one in the tree ALETHEIA_BENCH_CPP_BUILD_DIR names, the Go one
# at the path ALETHEIA_BENCH_GO_BIN names, and the Rust one under the
# CARGO_TARGET_DIR cargo builds in, rather than at the places in the tree a
# run without them uses. A runner that built in one place and ran another
# measured an earlier build, or nothing. Shown with a cmake, a go and a cargo
# that each write, where they are asked to build, a harness that names the
# path it runs from and fails, so the runner replays what it said.
# Non-zero exit: a lane ran a harness other than the one built where it was
# told. Exits 2 when the kernel library or the venv is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
[ -f python/.venv/bin/activate ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
mkdir -p "$dir/bin" "$dir/cpp" || exit 2
# The runner reads a configured tree's build type before it builds there.
printf 'CMAKE_BUILD_TYPE:STRING=Release\n' > "$dir/cpp/CMakeCache.txt"
# harness <lane> <path>: write at the path a harness that says where it runs from.
cat > "$dir/bin/harness" <<'SH'
#!/bin/sh
mkdir -p "$(dirname "$2")" || exit 1
printf '#!/bin/sh\necho "%s harness at $0" >&2\nexit 1\n' "$1" > "$2" && chmod +x "$2"
SH
# cmake --build <tree> --target benchmark
cat > "$dir/bin/cmake" <<SH
#!/bin/sh
exec "$dir/bin/harness" C++ "\$2/benchmark"
SH
# go build -o <path> ./benchmarks/
cat > "$dir/bin/go" <<SH
#!/bin/sh
exec "$dir/bin/harness" Go "\$3"
SH
# cargo build --release --example benchmark, from rust/
cat > "$dir/bin/cargo" <<SH
#!/bin/sh
exec "$dir/bin/harness" Rust "\${CARGO_TARGET_DIR:-target}/release/examples/benchmark"
SH
chmod +x "$dir/bin/harness" "$dir/bin/cmake" "$dir/bin/go" "$dir/bin/cargo"
out=$(PATH="$dir/bin:$PATH" ALETHEIA_BENCH_RESULTS_DIR="$dir/results" \
    ALETHEIA_BENCH_CPP_BUILD_DIR="$dir/cpp" ALETHEIA_BENCH_GO_BIN="$dir/go-benchmark" \
    CARGO_TARGET_DIR="$dir/cargo" bash benchmarks/run_all.sh --frames 1 --runs 1 --bench throughput 2>&1)
status=0
for ran in "C++ harness at $dir/cpp/benchmark" \
           "Go harness at $dir/go-benchmark" \
           "Rust harness at $dir/cargo/release/examples/benchmark"; do
    grep -qF "| $ran" <<< "$out" || { echo "no lane said: $ran"; status=1; }
done
[ "$status" -eq 0 ] || { echo "the run said:"; grep -E '^>>>|\| ' <<< "$out" | sed 's/^/  /'; exit 1; }
echo "PASS: each compiled harness ran from where it was told to build"
