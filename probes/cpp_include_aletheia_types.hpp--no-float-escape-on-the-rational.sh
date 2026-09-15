# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/types.hpp.
# Claim: the exact rational offers no conversion to a floating-point type, so no
# caller can take a lossy value out of it by accident. The float principle the
# header proves at its constructor boundary is not undone by an accessor.
# Non-zero exit: such a conversion exists, or a translation unit that calls one
# compiles.
# Exits 2 when the compiler is unavailable.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-22 > /dev/null || exit 2
header=cpp/include/aletheia/types.hpp

if grep -nE '(-> *(double|float))|operator +(double|float) *\(' "$header"; then
    echo "FAIL: the rational offers a conversion to a floating-point type"
    exit 1
fi

scratch=cpp/build/probe-scratch/no-float-escape
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/types.hpp>

// Must not compile: nothing takes a double out of an exact rational.
int main() {
    const aletheia::Rational r{1, 3};
    return static_cast<int>(r.to_double());
}
CPP
if clang++-22 -std=c++23 -fsyntax-only -Icpp/include "$scratch/t.cpp" > "$scratch/compile.log" 2>&1
then
    echo "FAIL: a call to a float conversion still compiles"
    exit 1
fi
echo "PASS: the rational has no float escape"
