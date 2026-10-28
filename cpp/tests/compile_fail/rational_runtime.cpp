// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Must not compile, which the rational_runtime_refused test holds: the
// two-argument Rational constructor is consteval, so a pair known only at run
// time is refused by the compiler and goes through Rational::make or
// Rational::integer instead.
#include <aletheia/types.hpp>

auto main(int argc, char** /*argv*/) -> int {
    aletheia::Rational const refused{argc, 1};
    return static_cast<int>(refused.numerator());
}
