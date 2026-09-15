# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/sanitizer-ignorelist.txt.
# Claim: the ignorelist's one pattern matches the path under which the
# sanitizer lane compiles the OpenXLSX source the list names, and the
# configured UBSan tree passes the list to the compiler. Non-zero exit: the
# pattern no longer matches the fetched tree's layout, the named file is
# gone, or the UBSan tree does not carry the flag. Exits 2 when
# cpp/build-ubsan is not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build-ubsan/CMakeCache.txt ] || exit 2
pattern=$(grep -E '^src:' cpp/sanitizer-ignorelist.txt | head -1 | sed 's/^src://')
[ -n "$pattern" ] || { echo "no src: entry"; exit 1; }
src=$(find cpp/build-ubsan/_deps -maxdepth 1 -type d -name 'openxlsx-src' | head -1)
[ -n "$src" ] || { echo "no fetched OpenXLSX under cpp/build-ubsan"; exit 1; }
status=0
for f in "$src/OpenXLSX/sources/XLStyles.cpp"; do
    [ -f "$f" ] || { echo "named file missing: $f"; status=1; }
    case "$f" in $pattern) ;; *) echo "pattern '$pattern' does not match $f"; status=1;; esac
done
grep -q 'fsanitize-ignorelist=.*sanitizer-ignorelist.txt' cpp/build-ubsan/CMakeFiles/aletheia-cpp.dir/flags.make || { echo "UBSan tree does not pass the ignorelist"; status=1; }
exit $status
