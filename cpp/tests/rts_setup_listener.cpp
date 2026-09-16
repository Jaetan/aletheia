// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer does not initialise the GHC RTS (see
// rational_renderer.cpp), so any render-dependent test that does not create a
// real FfiBackend itself needs the runtime brought up out of band. The test
// binaries that link this listener are unit_tests, where a check's
// condition description and enrichment's value render need it; yaml_tests and
// excel_tests, whose numeric fields are parsed through the kernel decimal
// source of truth; and log_events_tests, where set_properties renders the
// condition descriptions. Real-backend binaries such as integration_tests must
// not link it: they create their own FfiBackend, possibly asking for more than
// one core, and the listener's single-core init would race them into a
// spurious cores mismatch.
//
// This Catch2 listener brings the RTS up once for the whole process
// (`testRunStarting`) via a throwaway FfiBackend whose constructor runs `hs_init`;
// the RTS persists process-wide (`hs_exit` is never called), and the backend is
// held for the run. It is the C++ analogue of Go's package `TestMain`. Best-effort:
// if the .so is not locatable the render tests fail vocally with the renderer's
// "runtime not initialized" error. (The dedicated renderer-uninitialised test runs
// in its own ctest process without this listener, so it is not masked.)

#include <catch2/catch_test_run_info.hpp>
#include <catch2/interfaces/catch_interfaces_reporter.hpp>
#include <catch2/reporters/catch_reporter_event_listener.hpp>
#include <catch2/reporters/catch_reporter_registrars.hpp>

#include <aletheia/backend.hpp>

#include <cstdlib>
#include <exception>
#include <filesystem>
#include <memory>
#include <string_view>

// Locate libaletheia-ffi.so the way the renderer's find_library_path does, in
// the same order and with the same checks: ALETHEIA_LIB, which CI pins, then
// the build-tree paths ctest runs from, each existence-checked so a stale
// variable cannot shadow a library that is there. The empty path comes back
// only when every candidate is exhausted, which leaves the runtime down and
// the render-dependent tests failing vocally.
static auto find_test_lib() -> std::filesystem::path {
    namespace fs = std::filesystem;
    if (auto* env = std::getenv("ALETHEIA_LIB")) {
        const std::string_view env_sv{env};
        if (!env_sv.empty()) {
            if (const fs::path p{env_sv}; fs::exists(p))
                return p;
        }
    }
    for (const auto* candidate : {"../../build/libaletheia-ffi.so", "../build/libaletheia-ffi.so",
                                  "build/libaletheia-ffi.so"}) {
        if (fs::exists(candidate))
            return fs::canonical(candidate);
    }
    return {};
}

namespace {
class RtsSetupListener : public Catch::EventListenerBase {
public:
    using Catch::EventListenerBase::EventListenerBase;

    void testRunStarting(const Catch::TestRunInfo& /*info*/) override {
        const auto lib = find_test_lib();
        if (lib.empty())
            return; // best-effort; render tests fail vocally if the runtime is down
        try {
            // The constructor runs hs_init, bringing the RTS up for the process.
            backend_ = aletheia::make_ffi_backend(lib);
        } catch (const std::exception&) {
            backend_ = nullptr; // best-effort: leave the runtime down
        }
    }

private:
    std::unique_ptr<aletheia::IBackend> backend_;
};
} // namespace

CATCH_REGISTER_LISTENER(RtsSetupListener)
