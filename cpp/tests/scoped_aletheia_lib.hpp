// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// ALETHEIA_LIB set or unset for one test and restored after it. Catch2 runs
// test cases one after another, so changing the process environment is safe as
// long as it is restored.
#pragma once

#include <cstdlib>
#include <optional>
#include <string>

namespace aletheia::test {

class ScopedAletheiaLib {
public:
    // `value` set, or the variable unset for null.
    explicit ScopedAletheiaLib(char const* value) {
        if (char const* cur = std::getenv("ALETHEIA_LIB"))
            saved_ = cur;
        if (value != nullptr)
            ::setenv("ALETHEIA_LIB", value, /*overwrite=*/1);
        else
            ::unsetenv("ALETHEIA_LIB");
    }
    ScopedAletheiaLib(ScopedAletheiaLib const&) = delete;
    ScopedAletheiaLib(ScopedAletheiaLib&&) = delete;
    auto operator=(ScopedAletheiaLib const&) -> ScopedAletheiaLib& = delete;
    auto operator=(ScopedAletheiaLib&&) -> ScopedAletheiaLib& = delete;
    ~ScopedAletheiaLib() {
        if (saved_)
            ::setenv("ALETHEIA_LIB", saved_->c_str(), /*overwrite=*/1);
        else
            ::unsetenv("ALETHEIA_LIB");
    }

private:
    std::optional<std::string> saved_;
};

} // namespace aletheia::test
