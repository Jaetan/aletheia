# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/cli.hpp.
# Claim: run_cli returns 0 when a subcommand succeeds, 1 when validation
# fails, and 2 on error (no subcommand, an unknown subcommand, an unreadable
# DBC path), as the header states. Exercised through the aletheia-cli binary,
# built first. Non-zero exit: any of the five cases returns a different code.
# Exits 2 when cpp/build or the kernel is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] && [ -f build/libaletheia-ffi.so ] || exit 2
cmake --build cpp/build --target aletheia-cli > /dev/null 2>&1 || exit 2
export ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so
cli=cpp/build/aletheia-cli
scratch=cpp/build/probe-scratch/cli-exit
mkdir -p "$scratch" || exit 2
printf 'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 A: 8 ECU\n SG_ S : 0|16@1+ (1,0) [0|1] "" ECU\n\nBO_ 256 B: 8 ECU\n SG_ T : 0|8@1+ (1,0) [0|1] "" ECU\n' > "$scratch/duplicate_id.dbc"
expect() { "$cli" "${@:2}" > /dev/null 2>&1; rc=$?; [ "$rc" -eq "$1" ] || { echo "expected $1 got $rc for: ${*:2}"; exit 1; }; }
expect 0 validate --dbc examples/example.dbc
expect 1 validate --dbc "$scratch/duplicate_id.dbc"
expect 2
expect 2 bogus
expect 2 validate --dbc "$scratch/does-not-exist.dbc"
