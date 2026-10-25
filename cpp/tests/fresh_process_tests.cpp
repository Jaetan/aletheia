// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The suites that need a process of their own for the renderer and the
// runtime, each run as a child of this one: the renderer with the runtime down,
// releasing the kernel's strings, or handed a decimal failure with no envelope;
// the runtime started before any client, on the kernel and on the recording
// kernel's four CPUs; the allocation count, read beside the renderer in each,
// answering none with the runtime down, the recording kernel's count whole and
// the null kernel's zero;
// the runtime's heap cap; and a command holding one long number, which a
// kernel that echoes it whole answers by ending its process. ctest runs this file
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

#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

#include "child_process.hpp"
#include "repo_root.hpp"

#if !defined(ALETHEIA_RUNTIME_DOWN_TESTS) || !defined(ALETHEIA_RUNTIME_START_TESTS) ||             \
    !defined(ALETHEIA_RUNTIME_START_STAND_IN_TESTS) || !defined(ALETHEIA_RENDERER_FREES_TESTS) ||  \
    !defined(ALETHEIA_RTS_HEAP_CAP_TESTS) || !defined(ALETHEIA_LITERAL_BOUND_TESTS) ||             \
    !defined(ALETHEIA_RENDERER_NULL_KERNEL_TESTS)
#error "the fresh-process suites' paths are compile definitions of the build"
#endif

// Starts `binary` under the order the lane pins, with the environment this
// process was started with, where the runner names the mutant, each
// `NAME=value` of `extra` in place of any NAME it holds, and returns its wait
// status. The child dies with the thread that started it: the mutation runner
// ends a run by killing this process alone and then waits for its pipes to
// close, which a child left running would hold.
static auto run_child(const std::string& binary, const std::vector<std::string>& extra) -> int {
    auto environment = aletheia::test::environment_with(extra);
    auto const envp = aletheia::test::exec_array(environment);
    std::vector<std::string> arguments{binary, "--order", "decl"};
    auto const argv = aletheia::test::exec_array(arguments);
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
static void require_passes(const std::string& binary, const std::vector<std::string>& extra = {}) {
    auto const status = run_child(binary, extra);
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

TEST_CASE("the runtime starts before any client, and what read a number first keeps nothing",
          "[fresh_process]") {
    require_passes(ALETHEIA_RUNTIME_START_TESTS);
}

TEST_CASE("a core count is held to the CPUs the runtime counts", "[fresh_process]") {
    require_passes(ALETHEIA_RUNTIME_START_STAND_IN_TESTS);
}

TEST_CASE("the renderer frees the strings the kernel hands it", "[fresh_process]") {
    require_passes(ALETHEIA_RENDERER_FREES_TESTS);
}

TEST_CASE("a decimal failure without an envelope is a protocol error", "[fresh_process]") {
    require_passes(ALETHEIA_RENDERER_NULL_KERNEL_TESTS);
}

TEST_CASE("the runtime's heap cap contains", "[fresh_process]") {
    // The workload loads the kernel from the variable, which the sweep's
    // environment does not carry.
    require_passes(ALETHEIA_RTS_HEAP_CAP_TESTS,
                   {"ALETHEIA_LIB=" +
                    (aletheia::test::repo_root() / "build" / "libaletheia-ffi.so").string()});
}

// The child's cost is its input's, a 100 KB number through the kernel, so the
// mutation binary runs this case after every untagged test ([costly],
// tools/mutation_cpp_order.py): it stays the file's last case, and this file
// the last unit ahead of the costly ones.
TEST_CASE("a command holding one long number is refused at the ceiling",
          "[fresh_process][costly]") {
    // The suite loads the kernel from the variable, which the sweep's
    // environment does not carry; the runtime's flags are emptied, so a shell
    // that set them does not decide what the child runs under.
    require_passes(
        ALETHEIA_LITERAL_BOUND_TESTS,
        {"ALETHEIA_LIB=" + (aletheia::test::repo_root() / "build" / "libaletheia-ffi.so").string(),
         "ALETHEIA_RTS_OPTS="});
}
