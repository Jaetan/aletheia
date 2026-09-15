# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/enrich.cpp.
# Claim: the formula pretty-printer renders byte-identically to the Python
# binding's, for every formula alternative, every predicate and the three
# time-bound units, including the parenthesisation of nested binary
# operators and the "never" shorthand. One formula covering all of them is
# built in C++, rendered there, and serialised to the wire JSON; Python
# parses that JSON and renders it with its own formatter; the two strings
# must be equal. Both sides render thresholds through the kernel, so both
# bring the runtime up. Non-zero exit: the renderings differ. Exits 2 when
# the archive, the kernel or the Python environment is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.a
yaml=$(find cpp/build/_deps -maxdepth 2 -name 'libyaml-cpp.a' | head -1)
xlsx=$(find cpp/build -maxdepth 3 -name 'libOpenXLSX.a' | head -1)
json=$(find cpp/build/_deps -maxdepth 2 -type d -name 'json-src' | head -1)
kernel=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] && [ -n "$yaml" ] && [ -n "$xlsx" ] && [ -n "$json" ] && [ -f "$kernel" ] || exit 2
[ -x python/.venv/bin/python ] || exit 2
scratch=cpp/build/probe-scratch/enrich-parity
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>
#include <aletheia/client.hpp>
#include <aletheia/enrich.hpp>
#include "detail/json.hpp"
#include <cstdio>
#include <memory>
#include <span>
using namespace aletheia;
static auto pv(int n, int d) -> PhysicalValue { return PhysicalValue::of(n, d); }
// One formula per alternative and per predicate, nested so binary operators
// appear as children of binary operators (the parenthesisation rule) and the
// three time-bound units each occur once.
static auto everything() -> LtlFormula {
    using namespace ltl;
    const SignalName s{"Speed"};
    auto eq = atomic(equals(s, pv(1, 1)));
    auto lt = atomic(less_than(s, pv(3, 2)));
    auto gt = atomic(greater_than(s, pv(7, 1)));
    auto le = atomic(less_than_or_equal(s, pv(220, 1)));
    auto ge = atomic(greater_than_or_equal(SignalName{"RPM"}, pv(0, 1)));
    auto bt = atomic(between(SignalName{"Temp"}, pv(-40, 1), pv(215, 1)));
    auto ch = atomic(changed_by(SignalName{"Pos"}, Delta{Rational{5, 2}}));
    auto chn = atomic(changed_by(SignalName{"Neg"}, Delta{Rational{-5, 2}}));
    auto st = atomic(stable_within(SignalName{"Volt"}, Tolerance{Rational{1, 100}}));
    auto never_form = always(negate(clone(eq)));                       // the never shorthand
    auto unary = both(next(clone(lt)), either(weak_next(clone(gt)), negate(clone(le))));
    auto temporal = until(always(clone(ge)), release(eventually(clone(bt)), clone(ch)));
    auto metric_u = MetricUntil{Timestamp{2'000'000}, std::make_unique<LtlFormula>(clone(chn)),
                                std::make_unique<LtlFormula>(clone(st))};          // seconds
    auto metric_r = MetricRelease{Timestamp{1500}, std::make_unique<LtlFormula>(LtlFormula{std::move(metric_u)}),
                                  std::make_unique<LtlFormula>(within(Timestamp{7}, clone(eq)))}; // ms, then us
    auto metric_a = always_within(Timestamp{250'000}, clone(lt));
    return both(both(std::move(never_form), std::move(unary)),
                either(std::move(temporal), both(LtlFormula{std::move(metric_r)}, std::move(metric_a))));
}
int main(int, char** argv) {
    auto backend = make_ffi_backend(argv[1]); // brings the GHC runtime up
    const auto f = everything();
    const auto rendered = format_formula(f);
    std::FILE* out = std::fopen(argv[2], "w");
    std::fputs(rendered.c_str(), out);
    std::fputc('\n', out);
    std::fclose(out);
    std::FILE* wire = std::fopen(argv[3], "w");
    std::fputs(detail::serialize_set_properties(std::span<const LtlFormula>{&f, 1}).c_str(), wire);
    std::fclose(wire);
    return 0;
}
CPP
clang++-22 -std=c++23 -Icpp/include -Icpp/src -I"$json/include" "$scratch/t.cpp" "$lib" "$yaml" "$xlsx" -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t" "$kernel" "$scratch/cpp.txt" "$scratch/wire.json" || { echo "C++ side failed"; exit 1; }
ALETHEIA_LIB="$kernel" python/.venv/bin/python - "$scratch/wire.json" "$scratch/cpp.txt" <<'PY'
import json, pathlib, sys
from fractions import Fraction
from aletheia.client._backend import FFIBackend
from aletheia.client._enrichment import format_formula

# The wire carries a rational as a bare integer or as {numerator,denominator};
# the Python formatter takes Fraction, so decode the numeric predicate fields.
_RATIONAL_FIELDS = ("value", "min", "max", "delta", "tolerance")

def decode(node):
    if isinstance(node, dict) and node.get("operator") == "atomic":
        pred = dict(node["predicate"])
        for field in _RATIONAL_FIELDS:
            if field in pred:
                raw = pred[field]
                pred[field] = Fraction(raw["numerator"], raw["denominator"]) if isinstance(raw, dict) else Fraction(raw)
        return {**node, "predicate": pred}
    if isinstance(node, dict):
        return {k: decode(v) for k, v in node.items()}
    return node

backend = FFIBackend()  # brings the GHC runtime up, as the C++ side does
wire = json.loads(pathlib.Path(sys.argv[1]).read_text())
formula = decode(wire["properties"][0])
py = format_formula(formula)
cpp = pathlib.Path(sys.argv[2]).read_text().rstrip("\n")
if py != cpp:
    print("cpp:", cpp)
    print("py :", py)
    sys.exit(1)
print(f"identical, {len(cpp)} characters")
PY
