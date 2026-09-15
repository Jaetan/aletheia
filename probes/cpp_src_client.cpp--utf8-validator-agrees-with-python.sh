# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/client.cpp.
# Claim: the file's UTF-8 validator (used on every extraction reason slice)
# accepts exactly what RFC 3629 accepts: it agrees with Python's strict UTF-8
# decoder on a corpus of valid sequences, overlong encodings, surrogate code
# points, code points above U+10FFFF, truncated sequences and stray
# continuation bytes. The validator is file-local, so the probe compiles the
# translation unit into its own program. Non-zero exit: any disagreement.
# Exits 2 when the archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.a
yaml=$(find cpp/build/_deps -maxdepth 2 -name 'libyaml-cpp.a' | head -1)
xlsx=$(find cpp/build -maxdepth 3 -name 'libOpenXLSX.a' | head -1)
json=$(find cpp/build/_deps -maxdepth 2 -type d -name 'json-src' | head -1)
[ -f "$lib" ] && [ -n "$yaml" ] && [ -n "$xlsx" ] && [ -n "$json" ] || exit 2
scratch=cpp/build/probe-scratch/client-utf8
mkdir -p "$scratch" || exit 2
cat > "$scratch/corpus.txt" <<'TXT'
 
41
7f
c2 80
df bf
e0 a0 80
ef bf bf
f0 90 80 80
f4 8f bf bf
41 c3 a9 e2 82 ac f0 9f 98 80
c0 80
c1 bf
e0 80 80
e0 9f bf
f0 80 80 80
f0 8f bf bf
ed a0 80
ed bf bf
ed 9f bf
ee 80 80
f4 90 80 80
f5 80 80 80
f8 88 80 80 80
80
bf
c2
e0 a0
f0 90 80
c2 41
e2 82
ff
fe
TXT
cat > "$scratch/t.cpp" <<'CPP'
#include "client.cpp"
#include <cstdio>
#include <string>
#include <vector>
int main() {
    char line[512];
    while (std::fgets(line, sizeof line, stdin) != nullptr) {
        std::vector<std::byte> bytes;
        unsigned v = 0; int n = 0; const char* p = line;
        while (std::sscanf(p, "%x%n", &v, &n) == 1) { bytes.push_back(static_cast<std::byte>(v)); p += n; }
        std::printf("%d\n", aletheia::is_valid_utf8(bytes) ? 1 : 0);
    }
}
CPP
clang++-22 -std=c++23 -Icpp/include -Icpp/src -I"$json/include" "$scratch/t.cpp" "$lib" "$yaml" "$xlsx" -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t" < "$scratch/corpus.txt" > "$scratch/got.txt"
python/.venv/bin/python - "$scratch/corpus.txt" "$scratch/got.txt" <<'PY'
import sys
lines = open(sys.argv[1]).read().split("\n")[:-1]
got = [l.strip() for l in open(sys.argv[2]) if l.strip() != ""]
bad = 0
for hexes, g in zip(lines, got, strict=True):
    b = bytes(int(h, 16) for h in hexes.split())
    try:
        b.decode("utf-8"); want = "1"
    except UnicodeDecodeError:
        want = "0"
    if want != g: print(f"{hexes!r}: python {want} cpp {g}"); bad += 1
print(f"cases {len(lines)} bad {bad}")
sys.exit(1 if bad else 0)
PY
