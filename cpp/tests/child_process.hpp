// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// What a suite hands a child it starts: the environment this process was
// started with, the suite's own settings in place of what it held for them,
// and each list of strings as the array exec takes; and the run of a program
// as that child, its stdout and stderr on files the suite names.

#include "owned_file.hpp"

#include <catch2/catch_test_macros.hpp>

#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <ios>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia::test {

// The environment this process was started with, one `NAME=value` entry each,
// with each `NAME=value` of `extra` in place of any NAME it holds.
[[nodiscard]] inline auto environment_with(const std::vector<std::string>& extra)
    -> std::vector<std::string> {
    for (auto const& set : extra)
        REQUIRE(set.contains('='));
    auto const replaced = [&extra](std::string_view entry) {
        return std::ranges::any_of(extra, [entry](std::string_view set) {
            return entry.starts_with(set.substr(0, set.find('=') + 1));
        });
    };
    std::ifstream in{"/proc/self/environ", std::ios::binary};
    std::vector<std::string> environment;
    for (std::string entry; std::getline(in, entry, '\0');)
        environment.push_back(std::move(entry));
    std::erase_if(environment, replaced);
    environment.insert(environment.end(), extra.begin(), extra.end());
    return environment;
}

// `words` as the null-terminated array exec takes, pointing into `words`,
// which outlives it.
[[nodiscard]] inline auto exec_array(std::vector<std::string>& words) -> std::vector<char*> {
    std::vector<char*> array;
    array.reserve(words.size() + 1);
    for (auto& word : words)
        array.push_back(word.data());
    array.push_back(nullptr);
    return array;
}

// The status a child that could not start its program exits with, which no
// program a suite runs exits with.
inline constexpr int not_started = 127;

// Runs the program `words` names first, with the rest of `words` as its
// arguments, in the directory `where`, over `environment`, with its stdout on
// the file at `out_path` and its stderr on the file at `err_path`, and answers
// its exit code, or -1 when a signal ended it.
[[nodiscard]] inline auto run_program(std::vector<std::string> words,
                                      std::vector<std::string> environment,
                                      const std::filesystem::path& where,
                                      const std::filesystem::path& out_path,
                                      const std::filesystem::path& err_path) -> int {
    auto const argv = exec_array(words);
    auto const envp = exec_array(environment);
    const File out{std::fopen(out_path.c_str(), "we")};
    const File err{std::fopen(err_path.c_str(), "we")};
    REQUIRE(out != nullptr);
    REQUIRE(err != nullptr);
    auto const out_fd = ::fileno(out.get());
    auto const err_fd = ::fileno(err.get());
    auto const pid = ::fork();
    if (pid == 0) {
        // Only calls safe after a fork.
        if (::chdir(where.c_str()) == 0 && ::dup2(out_fd, STDOUT_FILENO) == STDOUT_FILENO &&
            ::dup2(err_fd, STDERR_FILENO) == STDERR_FILENO)
            static_cast<void>(::execve(argv.front(), argv.data(), envp.data()));
        ::_exit(not_started);
    }
    REQUIRE(pid > 0);
    int status = 0;
    REQUIRE(::waitpid(pid, &status, 0) == pid);
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

} // namespace aletheia::test
