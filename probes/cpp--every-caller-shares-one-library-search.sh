# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the four places the binding looks for libaletheia-ffi.so.
# Claim: there is one search and all four callers use it, so the renderer that
# formats values and the backend that answers queries cannot load different
# builds. The renderer, the command-line tool, the throughput benchmark and the
# stability benchmark each call find_ffi_library and none carries a candidate
# list of its own.
# Non-zero exit: a caller searches on its own again.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
status=0

callers="cpp/src/cli/cli.cpp cpp/benchmarks/benchmark.cpp cpp/benchmarks/stability_bench.cpp"
for f in $callers; do
    grep -q 'find_ffi_library' "$f" || {
        echo "$f does not use the shared search"
        status=1
    }
    # A caller with its own candidate is a caller that can diverge again.
    if grep -qE '"[^"]*libaletheia-ffi\.so"' "$f"; then
        echo "$f names a library candidate of its own"
        status=1
    fi
done

# The search itself, and the registered path that is the reason it is shared.
renderer=cpp/src/rational_renderer.cpp
grep -q 'auto find_ffi_library() -> std::filesystem::path' "$renderer" || {
    echo "the shared search is not defined where the registered path lives"
    status=1
}
grep -q 'default_path_state' "$renderer" || {
    echo "the search no longer consults the path a backend registered"
    status=1
}
grep -q 'find_ffi_library' cpp/include/aletheia/backend.hpp || {
    echo "the shared search is not published"
    status=1
}

[ "$status" -eq 0 ] || exit 1
echo "PASS: one search, and every caller uses it"
