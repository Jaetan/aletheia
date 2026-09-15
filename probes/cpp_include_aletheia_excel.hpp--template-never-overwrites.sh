# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/excel.hpp.
# Claim: create_excel_template writes a workbook at a fresh path and refuses
# an existing path without touching it. Non-zero exit: the first call fails,
# the second succeeds, or the file changed. Exits 2 when the archive is not
# built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2
scratch=cpp/build/probe-scratch/excel-template
rm -rf "$scratch"; mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/excel.hpp>
int main(int, char** argv) {
    auto first = aletheia::create_excel_template(argv[1]);
    if (!first) return 3;
    auto second = aletheia::create_excel_template(argv[1]);
    return second ? 4 : 0;
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t" "$scratch/template.xlsx" || exit 1
before=$(sha256sum "$scratch/template.xlsx" | cut -c1-64)
"$scratch/t" "$scratch/template.xlsx" > /dev/null 2>&1; rc=$?
[ "$rc" -eq 3 ] || { echo "second program run should fail its first call with rc 3, got $rc"; exit 1; }
[ "$(sha256sum "$scratch/template.xlsx" | cut -c1-64)" = "$before" ]
