# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/yaml.hpp.
# Claim: the usage example in the header's own comment (the two
# load_checks_from_yaml calls) compiles as written against the public API.
# Non-zero exit: an example line no longer names a real loader or a real
# signature.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/yaml-example
mkdir -p "$scratch" || exit 2
example=$(sed -n '/^\/\/   auto checks = load_checks_from_yaml(/,/^\/\/   )");$/p' cpp/include/aletheia/yaml.hpp | sed 's|^// \{0,3\}||')
[ -n "$example" ] || { echo "no example found in the header comment"; exit 1; }
{
    printf '#include <aletheia/yaml.hpp>\nusing namespace aletheia;\nint main() {\n'
    printf '%s\n' "$example" | sed 's/^auto checks = /auto checks_a = /; t; s/^auto checks = /auto checks_b = /' | awk 'BEGIN{n=0} /^auto checks_a = /{n++; if (n==2) sub(/^auto checks_a = /, "auto checks_b = ")} {print}'
    printf '    return 0;\n}\n'
} > "$scratch/t.cpp"
clang++-22 -std=c++23 -fsyntax-only -Icpp/include "$scratch/t.cpp" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
