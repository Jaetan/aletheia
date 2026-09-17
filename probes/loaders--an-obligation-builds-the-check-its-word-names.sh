#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes python/aletheia/_check_conditions.py with its two loaders, and
# cpp/src/detail/loader_utils.hpp with its two.
# Claim: an obligation a when-then check closes with builds the check its own
# word names, and a word the vocabulary does not carry is refused by that word.
# Both bindings used to decide the slots a second time, per loader, with a
# trailing branch that was the range obligation: a word the shared vocabulary
# gained and that branch did not was built as a range check, silently, from two
# places in each binding. Measured before the fix, a document naming a fourth
# obligation came back as a between predicate in Python and as one built check
# in C++.
# Python is checked by reading the formula each word builds, which its wire
# form exposes. The C++ arm checks that each word loads and that an unknown one
# is refused by name, the binding having no formula introspection to compare.
# Non-zero exit: a word builds something other than what it names, or an
# unknown word is not refused.
# Exits 2 without the venv or a built kernel; the C++ arm is skipped without a
# compiler or a built binding.
set -u
cd "$(dirname "$0")/.." || exit 2
root=$PWD
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
export ALETHEIA_LIB=$root/build/libaletheia-ffi.so LD_LIBRARY_PATH=$root/build

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
status=0

(cd python && "$root/$py" - <<'PY'
import sys

from aletheia._check_conditions import ALL_THEN_CONDITIONS, THEN_SLOTS
from aletheia.client._types import ValidationError
from aletheia.yaml_loader import load_checks

# The roster comes from the vocabulary, so a word added to it with no case here
# fails rather than going unchecked.
WANT = {"equals": ("equals", "value: 5"),
        "exceeds": ("greaterThan", "value: 5"),
        "stays_between": ("between", "min: 1\n      max: 9")}
bad = []
if set(THEN_SLOTS) != set(ALL_THEN_CONDITIONS):
    bad.append("the accepted set and the slot table disagree")
for word in ALL_THEN_CONDITIONS:
    if word not in WANT:
        bad.append(f"the vocabulary carries {word!r} and this probe has no case for it")
for word in WANT:
    if word not in ALL_THEN_CONDITIONS:
        bad.append(f"this probe uses {word!r}, which the vocabulary does not carry")

for word, (predicate, slots) in WANT.items():
    if word not in ALL_THEN_CONDITIONS:
        continue
    doc = (f"checks:\n  - name: c\n    when: {{signal: Brake, condition: drops_below, value: 10}}\n"
           f"    within_ms: 100\n    then:\n      signal: Speed\n      condition: {word}\n      {slots}\n")
    try:
        built = load_checks(doc)[0].to_dict()["formula"]
    except ValidationError as exc:
        bad.append(f"{word!r} was refused by its own loader: {exc}")
        continue
    # The obligation is the right branch of the implication the check compiles
    # to; the left is the trigger, whose own predicate must not be read here or
    # a word wired to the trigger's builder would pass.
    try:
        got = built["right"]["formula"]["predicate"]["predicate"]
    except (KeyError, TypeError):
        bad.append(f"{word!r} built a shape with no obligation predicate: {str(built)[:160]}")
        continue
    if got != predicate:
        bad.append(f"{word!r} built a {got!r} predicate, not {predicate!r}")

doc = ("checks:\n  - name: c\n    when: {signal: Brake, condition: drops_below, value: 10}\n"
       "    within_ms: 100\n    then: {signal: Speed, condition: flickers, value: 5}\n")
try:
    load_checks(doc)
    bad.append("a word outside the vocabulary was accepted")
except ValidationError as exc:
    if "flickers" not in str(exc):
        bad.append(f"the refusal does not name the word: {exc}")

if bad:
    print("the Python loaders do not build what an obligation names:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"  python: {len(WANT)} obligations build what they name, and an unknown one is refused")
PY
) || status=1

if command -v clang++-22 > /dev/null && [ -f cpp/build/libaletheia-cpp.so ]; then
    cat > "$work/c.cpp" <<'CPP'
#include <aletheia/backend.hpp>
#include <aletheia/yaml.hpp>
#include <iostream>
#include <string>
#include <string_view>

namespace {
auto doc_for(std::string_view word, std::string_view slots) -> std::string {
    return std::string{"checks:\n  - name: c\n    when:\n      signal: Brake\n"
                       "      condition: drops_below\n      value: 10\n    within_ms: 100\n"
                       "    then:\n      signal: Speed\n      condition: "} +
           std::string{word} + "\n      " + std::string{slots} + "\n";
}
} // namespace

int main() {
    auto backend = aletheia::make_ffi_backend_from_env();
    int bad = 0;
    for (auto [word, slots] : {std::pair<std::string_view, std::string_view>{"equals", "value: 5"},
                               {"exceeds", "value: 5"},
                               {"stays_between", "min: 1\n      max: 9"}}) {
        auto res = aletheia::load_checks_from_yaml_string(doc_for(word, slots));
        if (!res || res->size() != 1) {
            std::cout << "  cpp: " << word << " did not load: "
                      << (res ? "no check" : res.error().message()) << "\n";
            ++bad;
        }
    }
    auto unknown = aletheia::load_checks_from_yaml_string(doc_for("flickers", "value: 5"));
    if (unknown) {
        std::cout << "  cpp: a word outside the vocabulary was accepted\n";
        ++bad;
    } else if (std::string{unknown.error().message()}.find("flickers") == std::string::npos) {
        std::cout << "  cpp: the refusal does not name the word: " << unknown.error().message()
                  << "\n";
        ++bad;
    }
    if (bad == 0)
        std::cout << "  cpp: 3 obligations load, and an unknown one is refused by name\n";
    return bad == 0 ? 0 : 1;
}
CPP
    if clang++-22 -std=c++23 -Icpp/include "$work/c.cpp" cpp/build/libaletheia-cpp.so \
        -Wl,-rpath,"$root/cpp/build" -ldl -lpthread -o "$work/c" > "$work/cc.log" 2>&1; then
        "$work/c" || status=1
    else
        echo "  cpp: the probe program does not compile:"
        head -5 "$work/cc.log" | sed 's/^/    /'
        status=1
    fi
else
    echo "  cpp: no compiler or no built binding, that half is untestable"
fi

[ "$status" -eq 0 ] || exit 1
echo "PASS: every obligation builds the check its word names in both bindings"
