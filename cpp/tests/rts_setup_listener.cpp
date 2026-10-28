// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer does not start the GHC runtime (see
// rational_renderer.cpp), so any render-dependent test that does not create a
// real FfiBackend itself needs the runtime started out of band. The test
// binaries that link this listener are unit_tests, where a check's
// condition description and enrichment's value render need it; yaml_tests and
// excel_tests, whose numeric fields are parsed through the kernel decimal
// source of truth; and log_events_tests, where set_properties renders the
// condition descriptions. The standalone integration_tests binary does not
// link it, because every one of its tests creates the backend it needs. Where
// the mutation build folds those same sources into unit_tests, the two sit in
// one binary and agree: the listener initialises the runtime with one core,
// which is what a default backend asks for, and the tests that assert on a
// different count establish the count they assert against before asking.
//
// This Catch2 listener starts the runtime once for the whole process
// (`testRunStarting`) with `aletheia::start_runtime`; the runtime persists
// process-wide (`hs_exit` is never called). It is the C++ analogue of Go's
// package `TestMain`. Best-effort:
// if the .so is not locatable the render tests fail vocally with the renderer's
// "runtime not initialized" error. (The dedicated renderer-uninitialised test runs
// in a process of its own without this listener, so it is not masked.)

#include <catch2/catch_test_run_info.hpp>
#include <catch2/interfaces/catch_interfaces_reporter.hpp>
#include <catch2/reporters/catch_reporter_event_listener.hpp>
#include <catch2/reporters/catch_reporter_registrars.hpp>

#include <aletheia/backend.hpp>

#include <cstdlib>
#include <exception>
#include <filesystem>
#include <string_view>
#include <system_error>

// Locate libaletheia-ffi.so in aletheia::find_ffi_library's order, with its
// own code so the start of every mutant's run reads none the sweep mutates:
// ALETHEIA_LIB when set, which CI pins, the file it names or none, then the
// build-tree paths ctest runs from, a path that cannot be looked at taken not
// to exist. No library, a stale variable included, is the empty path, which
// leaves the runtime down and the render-dependent tests failing vocally.
static auto find_test_lib() -> std::filesystem::path {
    namespace fs = std::filesystem;
    std::error_code ec;
    if (auto const* env = std::getenv("ALETHEIA_LIB")) {
        if (std::string_view const env_sv{env}; !env_sv.empty()) {
            fs::path const p{env_sv};
            return fs::exists(p, ec) ? p : fs::path{};
        }
    }
    for (auto const* candidate : {"../../build/libaletheia-ffi.so", "../build/libaletheia-ffi.so",
                                  "build/libaletheia-ffi.so"}) {
        if (auto p = fs::canonical(candidate, ec); !ec)
            return p;
    }
    return {};
}

namespace {
class RtsSetupListener : public Catch::EventListenerBase {
public:
    using Catch::EventListenerBase::EventListenerBase;

    void testRunStarting(Catch::TestRunInfo const& /*info*/) override {
        auto const lib = find_test_lib();
        if (lib.empty())
            return; // best-effort; render tests fail vocally if the runtime is down
        // Best-effort: a refused start leaves the runtime down, which the render
        // tests then report, and so does a start that throws, a defect of the
        // binding the tests then name rather than a run that ends before any
        // test reports. The runtime starts on one core here, so no mismatch can
        // be answered.
        try {
            if (!aletheia::start_runtime(lib, 1))
                return;
        } catch (std::exception const&) {
            return;
        }
    }
};
} // namespace

CATCH_REGISTER_LISTENER(RtsSetupListener)
