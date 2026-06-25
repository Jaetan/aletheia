// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Point 2 ("whine if the runtime is uninitialised"): the rational renderer no
// longer self-initialises the GHC RTS (see rational_renderer.cpp), so any
// render-dependent test that does NOT create a real FfiBackend itself needs the
// runtime brought up out of band. Two test binaries link this listener:
//   - unit_tests        — a Check's `condition_desc()` + enrichment's value render
//   - log_events_tests  — `set_properties` renders the condition descriptions
// (Real-backend binaries like integration_tests must NOT link it: they create
// their own FfiBackend, possibly at `rts_cores > 1`, and the listener's default
// `-N1` init would race them into a spurious `rts.cores_mismatch`.)
//
// This Catch2 listener brings the RTS up once for the whole process
// (`testRunStarting`) via a throwaway FfiBackend whose constructor runs `hs_init`;
// the RTS persists process-wide (`hs_exit` is never called), and the backend is
// held for the run. It is the C++ analogue of Go's package `TestMain`. Best-effort:
// if the .so is not locatable the render tests fail vocally with the renderer's
// "runtime not initialized" error. (The dedicated renderer-uninitialised test runs
// in its own ctest process without this listener, so it is not masked.)

#include <catch2/reporters/catch_reporter_event_listener.hpp>
#include <catch2/reporters/catch_reporter_registrars.hpp>

#include <aletheia/backend.hpp>

#include <cstdlib>
#include <filesystem>
#include <memory>
#include <string_view>

namespace {

// Locate libaletheia-ffi.so the same way the renderer's find_library_path does:
// ALETHEIA_LIB (pinned by CI), else the build-tree relative paths ctest runs from.
// Each candidate is existence-checked and falls through to the next if it does not
// resolve (so a stale env value cannot shadow a present .so); the empty path is
// returned only when EVERY candidate is exhausted, which leaves the runtime down
// and the render-dependent tests fail vocally. Uses the same getenv → string_view
// (!empty) → fs::exists shape as find_library_path verbatim.
auto find_test_lib() -> std::filesystem::path {
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
