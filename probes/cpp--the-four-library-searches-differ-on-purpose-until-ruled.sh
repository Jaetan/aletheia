# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the four places the binding looks for libaletheia-ffi.so.
# Claim: they do not agree, and this records exactly how, so the difference
# is a measured state rather than a suspicion. The renderer consults the path
# the backend registered, the command-line tool is the only one that looks in
# a system install directory, the throughput benchmark resolves relative to
# its own executable, and the stability benchmark returns one path without
# checking it. Non-zero exit: any of the four changed its candidates, which
# means the difference moved and the comparison above is stale.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

check() {
    grep -q "$2" "$1" || { echo "$1 no longer has: $2"; status=1; }
}
refute() {
    grep -q "$2" "$1" && { echo "$1 has gained: $2"; status=1; }
}

renderer=cpp/src/rational_renderer.cpp
check "$renderer" 'default_path_state'
check "$renderer" '"../../build/libaletheia-ffi.so"'
refute "$renderer" '/usr/local/lib'

cli=cpp/src/cli/cli.cpp
check "$cli" '"/usr/local/lib/libaletheia-ffi.so"'
check "$cli" '"build/libaletheia-ffi.so", "../build/libaletheia-ffi.so"'
refute "$cli" 'register_default_lib_path'

bench=cpp/benchmarks/benchmark.cpp
check "$bench" 'read_symlink("/proc/self/exe")'
refute "$bench" '/usr/local/lib'

stability=cpp/benchmarks/stability_bench.cpp
check "$stability" 'return std::filesystem::path{"build/libaletheia-ffi.so"};'
refute "$stability" '/usr/local/lib'

# The one property a unification must not break: the renderer and the backend
# must resolve to the same library, which is why the renderer consults the
# registered path at all.
check cpp/include/aletheia/detail/rational_renderer.hpp 'register_default_lib_path'
exit $status
