// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Thin entry point for the aletheia-cli binary: set up the process's standard
// output so every failed report write reaches run_cli as an error, collect argv
// (minus the program name) and hand off to aletheia::run_cli
// (cpp/src/cli/cli.cpp), which owns all parsing, dispatch, and exit-code logic.

#include <aletheia/cli.hpp>
#include <aletheia/detail/checked.hpp>

#include <cerrno>
#include <csignal>
#include <cstddef>
#include <cstdio>
#include <exception>
#include <iostream>
#include <span>
#include <string>
#include <tuple>
#include <vector>

#include <sys/stat.h>
#include <unistd.h>

// A write to a pipe whose reader is gone, or past the file-size limit, raises a
// signal whose default action kills the process before the write returns; with
// both ignored the write fails with EPIPE or EFBIG, which run_cli reports.
// A descriptor 1 closed at start would be handed to the next file the program
// opens, and the report written into that file; stdout reopened read-only on
// /dev/null keeps descriptor 1 while every write to it still fails with EBADF.
static void prepare_stdout() noexcept {
    std::ignore = std::signal(SIGPIPE, SIG_IGN);
    std::ignore = std::signal(SIGXFSZ, SIG_IGN);
    struct stat status{};
    if (::fstat(STDOUT_FILENO, &status) == -1 && errno == EBADF)
        std::ignore = std::freopen("/dev/null", "r", stdout);
}

auto main(int argc, char** argv) -> int {
    prepare_stdout();
    try {
        std::span<char* const> const raw{argv, static_cast<std::size_t>(argc)};
        std::vector<std::string> args;
        for (auto const* arg : aletheia::detail::subspan_at(raw, 1))
            args.emplace_back(arg);
        return aletheia::run_cli(args);
    } catch (std::exception const& e) {
        std::cerr << "Error: " << e.what() << '\n';
        return aletheia::cli_exit_error;
    }
}
