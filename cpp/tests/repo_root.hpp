// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The one way a test finds the repository root.
//
// ctest passes it per target through an ENVIRONMENT property in
// cpp/CMakeLists.txt, so the binary does not have to guess where it was built
// from.  The alternative a few suites used, walking up from __FILE__, bakes
// the build machine's source path into the binary and stops working the
// moment the tree is copied or the binary is run from elsewhere.
//
// A binary run outside ctest needs the variable set.  Nothing falls back to a
// guess, because a wrong root reads the wrong fixtures and fails somewhere
// far from the cause.

#include <cstdlib>
#include <filesystem>
#include <stdexcept>

namespace aletheia::test {

// The repository root, from the environment.  Throws when the variable is
// unset or empty, naming who is supposed to set it.
[[nodiscard]] inline auto repo_root() -> std::filesystem::path {
    const char* env = std::getenv("ALETHEIA_REPO_ROOT");
    if (env == nullptr || *env == '\0')
        throw std::runtime_error(
            "ALETHEIA_REPO_ROOT is unset or empty; ctest passes it per target through "
            "set_tests_properties(ENVIRONMENT ...) in cpp/CMakeLists.txt, and a run outside "
            "ctest has to set it");
    return std::filesystem::path{env};
}

} // namespace aletheia::test
