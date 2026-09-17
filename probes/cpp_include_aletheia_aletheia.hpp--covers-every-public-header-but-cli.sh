#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/aletheia.hpp.
# Claim: a translation unit including only the umbrella header sees every
# public header under cpp/include/aletheia except cli.hpp (the CLI entry
# point, built as its own library), and no nlohmann, yaml-cpp or OpenXLSX
# header. Measured through the preprocessor's dependency listing. Non-zero
# exit: a public header is missing from the umbrella's closure, or a
# third-party header is in it.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/umbrella
mkdir -p "$scratch" || exit 2
printf '#include <aletheia/aletheia.hpp>\n' > "$scratch/u.cpp"
clang++-23 -std=c++23 -Icpp/include -MM "$scratch/u.cpp" > "$scratch/u.d" 2> "$scratch/u.err" || { tail -3 "$scratch/u.err"; exit 1; }
seen=$(tr ' \\' '\n\n' < "$scratch/u.d" | grep 'cpp/include/aletheia/' | sed 's|.*/include/aletheia/||' | sort -u)
status=0
for h in $(cd cpp/include/aletheia && ls *.hpp); do
    [ "$h" = cli.hpp ] && continue
    printf '%s\n' "$seen" | grep -qx "$h" || { echo "not reached from the umbrella: $h"; status=1; }
done
if tr ' \\' '\n\n' < "$scratch/u.d" | grep -qE 'nlohmann|yaml-cpp|OpenXLSX'; then echo "third-party header in the umbrella closure"; status=1; fi
exit $status
