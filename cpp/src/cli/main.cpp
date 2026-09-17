// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Thin entry point for the aletheia-cli binary: collect argv (minus the
// program name) and hand off to aletheia::run_cli (cpp/src/cli/cli.cpp),
// which owns all parsing, dispatch, and exit-code logic.

#include <aletheia/cli.hpp>

#include <cstddef>
#include <exception>
#include <iostream>
#include <span>
#include <string>
#include <vector>

auto main(int argc, char** argv) -> int {
    try {
        const std::span<char* const> raw{argv, static_cast<std::size_t>(argc)};
        std::vector<std::string> args;
        for (auto const* arg : raw.subspan(1))
            args.emplace_back(arg);
        return aletheia::run_cli(args);
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << '\n';
        return aletheia::cli_exit_error;
    }
}
