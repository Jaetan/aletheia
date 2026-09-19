#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/temp_path.hpp and tools/cpp_scratch.py.
# Claim: the scratch directory name prefix is one string, spelled the same by
# the fixture that creates the directories and by the lane that removes the
# ones its killed runs left. Non-zero exit: the two drifted, and the lane
# sweeps a name nothing makes while the directories pile up under another.
set -u
cd "$(dirname "$0")/.." || exit 2
fixture=$(sed -n 's/^inline constexpr std::string_view scratch_prefix = "\(.*\)";$/\1/p' cpp/tests/temp_path.hpp)
lane=$(sed -n 's/^SCRATCH_PREFIX = "\(.*\)"$/\1/p' tools/cpp_scratch.py)
[ -n "$fixture" ] || { echo "no scratch_prefix definition in cpp/tests/temp_path.hpp"; exit 1; }
[ -n "$lane" ] || { echo "no SCRATCH_PREFIX definition in tools/cpp_scratch.py"; exit 1; }
[ "$fixture" = "$lane" ] || { echo "the prefixes differ: fixture '$fixture', lane '$lane'"; exit 1; }
exit 0
