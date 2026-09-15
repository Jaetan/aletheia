#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/aletheia.hpp.
# Claim: the umbrella's description of <aletheia/client.hpp> holds: a
# translation unit including only the facade reaches none of excel.hpp,
# yaml.hpp and enrich.hpp, and no nlohmann, yaml-cpp or OpenXLSX header.
# Non-zero exit: the facade's closure contains one of those.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/umbrella
mkdir -p "$scratch" || exit 2
printf '#include <aletheia/client.hpp>\n' > "$scratch/c.cpp"
clang++-22 -std=c++23 -Icpp/include -MM "$scratch/c.cpp" > "$scratch/c.d" 2> "$scratch/c.err" || { tail -3 "$scratch/c.err"; exit 1; }
! tr ' \\' '\n\n' < "$scratch/c.d" | grep -qE 'aletheia/(excel|yaml|enrich)\.hpp|nlohmann|yaml-cpp|OpenXLSX'
