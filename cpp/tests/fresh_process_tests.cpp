// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The three suites that need a process of their own for the renderer and the
// runtime, each run as a child of this one: the renderer with the runtime down
// or with no library to find, and the runtime's heap cap. ctest runs this file
// as a binary of its own, and the mutation build folds it into the mutation
// binary, which the runner starts once per mutant with the mutant named in its
// environment: a child inherits the environment, and it or the workload it
// starts links the same mutated library, so it runs under the mutant too. A child
// that does not pass ends this process the way it ended itself, by its exit
// status or by its signal, so the sweep reads the child's ending as if it had
// run the child.

#include <catch2/catch_test_macros.hpp>

#include <linux/prctl.h>
#include <sys/prctl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <ios>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "repo_root.hpp"

#if !defined(ALETHEIA_RUNTIME_DOWN_TESTS) || !defined(ALETHEIA_RENDERER_MISSING_LIBRARY_TESTS) ||  \
    !defined(ALETHEIA_RTS_HEAP_CAP_TESTS)
#error "the fresh-process suites' paths are compile definitions of the build"
#endif

// The environment this process was started with, where the runner names the
// mutant, one `NAME=value` entry each.
static auto started_environment() -> std::vector<std::string> {
    std::ifstream in{"/proc/self/environ", std::ios::binary};
    std::vector<std::string> entries;
    for (std::string entry; std::getline(in, entry, '\0');)
        entries.push_back(std::move(entry));
    return entries;
}

// Starts `binary` under the order the lane pins, with the environment this
// process was started with, each `NAME=value` of `extra` in place of any NAME
// it holds, and returns its wait status. The child dies with the thread that
// started it: the mutation runner ends a run by killing this process alone and
// then waits for its pipes to close, which a child left running would hold.
static auto run_child(std::string binary, const std::vector<std::string>& extra) -> int {
    for (auto const& set : extra)
        REQUIRE(set.contains('='));
    auto const replaced = [&extra](std::string_view entry) {
        return std::ranges::any_of(extra, [entry](std::string_view set) {
            return entry.starts_with(set.substr(0, set.find('=') + 1));
        });
    };
    auto environment = started_environment();
    std::erase_if(environment, replaced);
    environment.insert(environment.end(), extra.begin(), extra.end());
    std::vector<char*> envp;
    envp.reserve(environment.size() + 1);
    for (auto& entry : environment)
        envp.push_back(entry.data());
    envp.push_back(nullptr);
    std::string order{"--order"};
    std::string decl{"decl"};
    std::vector<char*> argv{binary.data(), order.data(), decl.data(), nullptr};
    static_cast<void>(std::fflush(nullptr));
    auto const parent = ::getpid();
    auto const pid = ::fork();
    if (pid == 0) {
        // Only calls safe after a fork in a process that may run other threads.
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-vararg): PR_SET_PDEATHSIG has no other API
        static_cast<void>(::prctl(PR_SET_PDEATHSIG, SIGKILL));
        if (::getppid() != parent)
            ::_exit(EXIT_FAILURE);
        static_cast<void>(::execve(binary.c_str(), argv.data(), envp.data()));
        ::_exit(EXIT_FAILURE);
    }
    REQUIRE(pid > 0);
    int status = 0;
    REQUIRE(::waitpid(pid, &status, 0) == pid);
    return status;
}

// Passes when the child passed; otherwise ends this process as the child
// ended, which no assertion here could report as faithfully. Catch2 ends a run
// in which every case skipped with 4, so a child that found nothing to run
// does not pass.
static void require_passes(std::string binary, const std::vector<std::string>& extra = {}) {
    auto const status = run_child(std::move(binary), extra);
    if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
        SUCCEED();
        return;
    }
    static_cast<void>(std::fflush(nullptr));
    if (WIFSIGNALED(status)) {
        static_cast<void>(std::signal(WTERMSIG(status), SIG_DFL));
        static_cast<void>(std::raise(WTERMSIG(status)));
    }
    std::_Exit(WIFEXITED(status) ? WEXITSTATUS(status) : EXIT_FAILURE);
}

TEST_CASE("the renderer refuses while the runtime is down", "[fresh_process]") {
    require_passes(ALETHEIA_RUNTIME_DOWN_TESTS);
}

TEST_CASE("the renderer refuses when it finds no library", "[fresh_process]") {
    require_passes(ALETHEIA_RENDERER_MISSING_LIBRARY_TESTS);
}

TEST_CASE("the runtime's heap cap contains", "[fresh_process]") {
    // The workload loads the kernel from the variable, which the sweep's
    // environment does not carry.
    require_passes(ALETHEIA_RTS_HEAP_CAP_TESTS,
                   {"ALETHEIA_LIB=" +
                    (aletheia::test::repo_root() / "build" / "libaletheia-ffi.so").string()});
}
