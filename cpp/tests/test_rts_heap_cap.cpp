// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Runtime GHC RTS heap-cap containment — C++ behavioural test.
//
// CONTAINMENT-BY-ABORT: the heap cap is NOT a recoverable error.  When it fires
// the process TERMINATES (a GHC HeapExhausted abort of the foreign-export
// wrapper) so the HOST survives.  This test forks the rts_heap_cap_workload
// helper (its own process, because the GHC RTS is one-shot per process) twice:
//
//   positive — default cap (-M3G): boots via hs_init_with_rtsopts and parses;
//   negative — a tight ALETHEIA_RTS_OPTS=-M12M cap over a large DBC aborts.
//
// This test process itself creates no FfiBackend, so it never starts the RTS —
// making fork() safe (forking a process with the GHC RTS live is unsafe).

#include <catch2/catch_test_macros.hpp>

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <array>
#include <cstddef>
#include <cstdlib>
#include <string>
#include <utility>

#ifndef ALETHEIA_RTS_WORKLOAD_BIN
#error "ALETHEIA_RTS_WORKLOAD_BIN must be defined (the workload binary path)"
#endif

// Fork+exec the workload with `n` messages and an optional ALETHEIA_RTS_OPTS
// override, returning its exit code (or -1 if it died from a signal) and
// whatever it wrote to stdout.  The child inherits ALETHEIA_LIB from this
// test's environment, which ctest sets.  Its stdout comes back through a pipe
// so the positive case can read the success sentinel rather than infer it from
// the exit code; stderr flows to this process's, where a failure shows it.
static auto run_workload(const std::string& n, const char* rts_opts)
    -> std::pair<int, std::string> {
    std::array<int, 2> out{};
    REQUIRE(pipe(out.data()) == 0);

    const pid_t pid = fork();
    if (pid == 0) {
        close(out[0]);
        dup2(out[1], STDOUT_FILENO);
        close(out[1]);
        if (rts_opts != nullptr)
            setenv("ALETHEIA_RTS_OPTS", rts_opts, 1);
        else
            unsetenv("ALETHEIA_RTS_OPTS");
        // execv over execl: the varargs form has no way to pass the argument
        // vector without a C-style ellipsis, and both take the same strings.
        std::string bin{ALETHEIA_RTS_WORKLOAD_BIN};
        std::string count{n};
        std::array<char*, 3> args{bin.data(), count.data(), nullptr};
        execv(bin.c_str(), args.data());
        _exit(127); // exec failed
    }
    REQUIRE(pid > 0);
    close(out[1]);

    // Drain before waiting: a child that filled the pipe would block forever
    // on its next write while this process waited for it to exit.
    std::string captured;
    std::array<char, 4096> buf{};
    for (ssize_t got = 0; (got = read(out[0], buf.data(), buf.size())) > 0;)
        captured.append(buf.data(), static_cast<std::size_t>(got));
    close(out[0]);

    int status = 0;
    REQUIRE(waitpid(pid, &status, 0) == pid);
    return {WIFEXITED(status) ? WEXITSTATUS(status) : -1, captured};
}

TEST_CASE("default cap boots and parses a workload", "[rts][heap_cap]") {
    // The correct path: hs_init_with_rtsopts and the default heap cap. The
    // workload prints its sentinel only after a clean parse, so reading it
    // back pins both the exit code and the path that produced it.
    auto const [code, out] = run_workload("3", nullptr);
    CHECK(code == 0);
    CHECK(out.contains("ALETHEIA_RTS_OK"));
}

TEST_CASE("a tight heap cap aborts the process", "[rts][heap_cap]") {
    // The teeth: -M12M over a large DBC exhausts the heap mid-parse and GHC
    // aborts the process.  A non-zero exit that is neither the parse-error path
    // (3) nor a backend exception (2) is the heap abort (containment), not a
    // masked failure.
    auto const [code, out] = run_workload("1000", "-M12M");
    CHECK(code != 0);
    CHECK(code != 3);
    CHECK(code != 2);
    // And it died before the clean-parse path, so the sentinel never printed.
    CHECK(!out.contains("ALETHEIA_RTS_OK"));
}
