#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/backend.hpp.
# Claim: make_ffi_backend_from_env throws AletheiaException of kind Validation
# both when ALETHEIA_LIB is unset and when it is set to the empty string, and
# never reaches dlopen. Non-zero exit: either case does not throw that kind.
# Exits 2 when the library archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2
scratch=cpp/build/probe-scratch/from-env
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>
int main() {
    try {
        auto b = aletheia::make_ffi_backend_from_env();
        return 1; // must not construct
    } catch (const aletheia::AletheiaException& e) {
        return e.error().kind() == aletheia::ErrorKind::Validation ? 0 : 3;
    }
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -3 "$scratch/compile.log"; exit 1; }
env -u ALETHEIA_LIB "$scratch/t"; unset_rc=$?
ALETHEIA_LIB= "$scratch/t"; empty_rc=$?
[ "$unset_rc" -eq 0 ] && [ "$empty_rc" -eq 0 ] || { echo "unset=$unset_rc empty=$empty_rc"; exit 1; }
