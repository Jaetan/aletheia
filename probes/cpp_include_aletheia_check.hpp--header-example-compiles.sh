#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/check.hpp.
# Claim: the usage example in the header's own comment (the lines beginning
# with check::) compiles as written against the public API. Non-zero exit: an
# example line no longer names a real builder or a real factory.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/check-example
mkdir -p "$scratch" || exit 2
example=$(sed -n '/^\/\/   check::/,/;$/p' cpp/include/aletheia/check.hpp | sed 's|^// *||')
[ -n "$example" ] || { echo "no check:: example found in the header comment"; exit 1; }
{
    printf '#include <aletheia/check.hpp>\n#include <chrono>\nusing namespace aletheia;\nusing namespace std::chrono_literals;\nint main() {\n'
    printf '%s\n' "$example" | sed 's/^\(check::\)/auto r_\1/' | awk '{ n++; sub(/^auto r_/, "auto r" n " = "); print }'
    printf '    return 0;\n}\n'
} > "$scratch/t.cpp"
clang++-23 -std=c++23 -fsyntax-only -Icpp/include "$scratch/t.cpp" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
