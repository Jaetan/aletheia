# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/README.md.
# Claim: the C++ fence in the README is a complete program that compiles
# against the built binding with the same command shape as the doc-example
# harness and runs to exit 0 against the built kernel. Non-zero exit: the
# fence no longer compiles, links or runs. Needs cpp/build configured and
# built and build/libaletheia-ffi.so present; exits 2 when they are not.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] && [ -f build/libaletheia-ffi.so ] || exit 2
scratch=cpp/build/probe-scratch/readme-fence
mkdir -p "$scratch" || exit 2
awk '/^```cpp$/{flag=1; next} /^```$/{flag=0} flag' cpp/README.md > "$scratch/fence.cpp"
grep -q 'int main' "$scratch/fence.cpp" || { echo "fence is not a complete program"; exit 1; }
clang++-22 -std=c++23 -Icpp/include "$scratch/fence.cpp" "$lib" $rpath \
    -ldl -lpthread -o "$scratch/fence" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so "$scratch/fence"
