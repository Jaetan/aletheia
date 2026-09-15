// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// One owning temporary path for the test tree.  Three suites needed a scratch
// file, a scratch file with content, and a scratch directory, and each carried
// its own type with its own lifetime to get right; one removed its file
// through the throwing overloads, from inside a destructor.  This one removes
// whatever is at the path, file or directory, and cannot throw doing it.
//
// Non-copyable and non-movable, so the path's life is exactly the scope that
// declared it.  `path` is public and const, which is what the call sites read.

#include <filesystem>
#include <fstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>

namespace aletheia::test {

// Tag for the directory shape, so the three constructors differ by more than
// their argument count at the call site.
struct AsDirectory {};

class TempPath {
public:
    // A name under the system temporary directory, with anything already
    // there removed.
    explicit TempPath(std::string_view name) : path(std::filesystem::temp_directory_path() / name) {
        clear();
    }

    // The same, with `content` written to it.
    TempPath(std::string_view name, std::string_view content) : TempPath(name) {
        std::ofstream out{path};
        out << content;
        out.close();
        if (!out)
            throw std::runtime_error("cannot write " + path.string());
    }

    // A directory at an explicit path, created now.
    TempPath(std::filesystem::path where, AsDirectory) : path(std::move(where)) {
        std::filesystem::create_directories(path);
    }

    TempPath(const TempPath&) = delete;
    TempPath(TempPath&&) = delete;
    auto operator=(const TempPath&) -> TempPath& = delete;
    auto operator=(TempPath&&) -> TempPath& = delete;
    ~TempPath() { clear(); }

    [[nodiscard]] auto string() const -> std::string { return path.string(); }

    const std::filesystem::path path;

private:
    void clear() const {
        std::error_code ec;
        std::filesystem::remove_all(path, ec);
    }
};

} // namespace aletheia::test
