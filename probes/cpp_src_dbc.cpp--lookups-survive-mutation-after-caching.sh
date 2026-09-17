#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/dbc.cpp.
# Claim: message_by_id, message_by_name and signal_by_name build their index
# lazily and never trust it blindly: after the public vectors are shrunk,
# reordered or replaced, a lookup returns the element that still matches or
# nullptr, never a stale or out-of-bounds element. Non-zero exit: a lookup
# returns a wrong element or fails to find one that exists. Exits 2 when the
# archive is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] || exit 2
scratch=cpp/build/probe-scratch/dbc-stale
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/dbc.hpp>
#include <algorithm>
#include <cstdio>
using namespace aletheia;
static auto sig(const char* n) -> DbcSignal {
    return DbcSignal{.name = SignalName{n}, .start_bit = BitPosition{0}, .bit_length = BitLength{8},
                     .byte_order = ByteOrder::LittleEndian, .is_signed = false,
                     .factor = RationalFactor{Rational{1, 1}}, .offset = RationalOffset{Rational{0, 1}},
                     .minimum = RationalBound{Rational{0, 1}}, .maximum = RationalBound{Rational{1, 1}},
                     .unit = Unit{""}, .presence = AlwaysPresent{}};
}
static auto msg(unsigned id, const char* n) -> DbcMessage {
    return DbcMessage{.id = CanId{StandardId::create(static_cast<std::uint16_t>(id)).value()},
                      .name = MessageName{n}, .dlc = Dlc::create(8).value(), .sender = NodeName{"E"},
                      .signals = {sig("A"), sig("B"), sig("C")}};
}
int main() {
    int failures = 0;
    DbcDefinition d{.version = "", .messages = {msg(1, "M1"), msg(2, "M2"), msg(3, "M3")}};
    const CanId id3 = CanId{StandardId::create(3).value()};
    if (d.message_by_id(id3) == nullptr || d.message_by_name(MessageName{"M3"}) == nullptr) ++failures;
    // shrink: the cached index for M3 is now out of bounds
    d.messages.pop_back();
    if (d.message_by_id(id3) != nullptr || d.message_by_name(MessageName{"M3"}) != nullptr) ++failures;
    // reorder: cached indices now point at the wrong messages
    std::swap(d.messages[0], d.messages[1]);
    const auto* m1 = d.message_by_name(MessageName{"M1"});
    const auto* m2 = d.message_by_id(CanId{StandardId::create(2).value()});
    if ((m1 != nullptr && m1->name.get() != "M1") || (m2 != nullptr && m2->name.get() != "M2")) ++failures;
    // replace in place: the element at the cached index changes identity
    d.messages[0] = msg(9, "M9");
    if (d.message_by_name(MessageName{"M2"}) != nullptr && d.message_by_name(MessageName{"M2"})->name.get() != "M2") ++failures;
    // signals: same discipline on one message
    DbcMessage m = msg(5, "M5");
    if (m.signal_by_name(SignalName{"C"}) == nullptr) ++failures;
    m.signals.pop_back();
    if (m.signal_by_name(SignalName{"C"}) != nullptr) ++failures;
    std::swap(m.signals[0], m.signals[1]);
    const auto* a = m.signal_by_name(SignalName{"A"});
    if (a != nullptr && a->name.get() != "A") ++failures;
    std::printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
CPP
clang++-23 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t"
