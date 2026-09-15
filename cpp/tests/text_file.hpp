// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// One reader for the whole-file reads the test executables do.

#include <filesystem>
#include <fstream>
#include <iterator>
#include <stdexcept>
#include <string>

namespace aletheia::test {

// Read a text file whole. Throws naming the path when it cannot be opened, so
// a fixture that has moved fails at the read instead of arriving downstream as
// an empty string.
inline auto read_text_file(const std::filesystem::path& path) -> std::string {
    std::ifstream in{path};
    if (!in)
        throw std::runtime_error("cannot read " + path.string());
    return std::string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
}

} // namespace aletheia::test
