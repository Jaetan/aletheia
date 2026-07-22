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

#include <sys/wait.h>
#include <unistd.h>

#include <cstdlib>
#include <string>

#ifndef ALETHEIA_RTS_WORKLOAD_BIN
#error "ALETHEIA_RTS_WORKLOAD_BIN must be defined (the workload binary path)"
#endif

namespace {

// Fork+exec the workload with `n` messages and an optional ALETHEIA_RTS_OPTS
// override, returning its exit code (or -1 if it died from a signal).  The child
// inherits ALETHEIA_LIB from this test's environment (set by ctest).  stdout /
// stderr flow to this process's, which is fine — the assertions key on the exit
// code (the helper returns 0 only after printing its success sentinel).
auto run_workload(const std::string& n, const char* rts_opts) -> int {
    const pid_t pid = fork();
    if (pid == 0) {
        if (rts_opts != nullptr)
            setenv("ALETHEIA_RTS_OPTS", rts_opts, 1);
        else
            unsetenv("ALETHEIA_RTS_OPTS");
        execl(ALETHEIA_RTS_WORKLOAD_BIN, ALETHEIA_RTS_WORKLOAD_BIN, n.c_str(),
              static_cast<char*>(nullptr));
        _exit(127); // exec failed
    }
    REQUIRE(pid > 0);
    int status = 0;
    REQUIRE(waitpid(pid, &status, 0) == pid);
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

} // namespace

TEST_CASE("default cap boots and parses a workload", "[rts][heap_cap]") {
    // The correct path: hs_init_with_rtsopts + the -M3G default cap.  A clean
    // exit implies the sentinel printed (the helper returns 0 only then).
    CHECK(run_workload("3", nullptr) == 0);
}

TEST_CASE("a tight heap cap aborts the process", "[rts][heap_cap]") {
    // The teeth: -M12M over a large DBC exhausts the heap mid-parse and GHC
    // aborts the process.  A non-zero exit that is neither the parse-error path
    // (3) nor a backend exception (2) is the heap abort (containment), not a
    // masked failure.
    const int code = run_workload("1000", "-M12M");
    CHECK(code != 0);
    CHECK(code != 3);
    CHECK(code != 2);
}
