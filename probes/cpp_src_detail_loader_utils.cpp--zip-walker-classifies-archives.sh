# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/detail/loader_utils.cpp.
# Claim: check_xlsx_uncompressed_bound reads a ZIP central directory and
# refuses an archive whose uncompressed entries exceed the DBC text bound
# with an InputBoundExceeded error carrying the summed size, accepts an
# archive under the bound, and refuses a file that is not a ZIP with a
# Validation error. The archives are built here with Python's zipfile (a
# 70 MiB entry of zeros compresses to a few hundred bytes). Non-zero exit: a
# classification differs. Exits 2 when the archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.a
yaml=$(find cpp/build/_deps -maxdepth 2 -name 'libyaml-cpp.a' | head -1)
xlsx=$(find cpp/build -maxdepth 3 -name 'libOpenXLSX.a' | head -1)
[ -f "$lib" ] && [ -n "$yaml" ] && [ -n "$xlsx" ] || exit 2
scratch=cpp/build/probe-scratch/loader-zip
mkdir -p "$scratch" || exit 2
python/.venv/bin/python - "$scratch" <<'PY'
import sys, zipfile, pathlib
d = pathlib.Path(sys.argv[1])
with zipfile.ZipFile(d / "bomb.zip", "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("xl/big.xml", b"\0" * (70 * 1024 * 1024))
with zipfile.ZipFile(d / "sane.zip", "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("xl/workbook.xml", b"<workbook/>")
    z.writestr("xl/sheet1.xml", b"<sheet/>" * 1000)
(d / "notzip.bin").write_bytes(b"this is not a zip archive" * 10)
PY
cat > "$scratch/t.cpp" <<'CPP'
#include "detail/loader_utils.hpp"
#include <cstdio>
using namespace aletheia;
int main(int, char** argv) {
    int failures = 0;
    auto bomb = detail::check_xlsx_uncompressed_bound(argv[1]);
    if (bomb || bomb.error().kind() != ErrorKind::InputBoundExceeded || !bomb.error().bound_info() ||
        bomb.error().bound_info()->observed != 70ULL * 1024 * 1024) ++failures;
    auto sane = detail::check_xlsx_uncompressed_bound(argv[2]);
    if (!sane) ++failures;
    auto notzip = detail::check_xlsx_uncompressed_bound(argv[3]);
    if (notzip || notzip.error().kind() != ErrorKind::Validation) ++failures;
    std::printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
CPP
clang++-22 -std=c++23 -Icpp/include -Icpp/src "$scratch/t.cpp" "$lib" "$yaml" "$xlsx" -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t" "$scratch/bomb.zip" "$scratch/sane.zip" "$scratch/notzip.bin"
