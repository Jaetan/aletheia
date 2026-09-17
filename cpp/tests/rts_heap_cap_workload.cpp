// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Standalone workload driven by test_rts_heap_cap.cpp (forked as a subprocess):
// boot the real FFI client and parse a VALID DBC of argv[1] messages, then print
// the sentinel.  A large count builds a live parse tree past a tight -M cap, so
// the cap fires mid-parse and the process aborts before the sentinel; a small
// count fits any cap and parses cleanly.  Its own main() because the GHC RTS is
// process-global and one-shot, so the abort must happen in a fresh process.
//
// Exit codes: 0 = clean parse + sentinel; 3 = parse error (a valid DBC never
// hits this); 2 = the workload could not run, either because the message count
// argument is not a positive number or because the backend threw.  The GHC heap
// abort terminates the process out of band, which is what the test asserts for
// the tight-cap case: a non-zero code that is none of these.

#include <aletheia/backend.hpp>
#include <aletheia/client.hpp>

#include <charconv>
#include <cstddef>
#include <cstdio>
#include <exception>
#include <memory>
#include <print>
#include <span>
#include <sstream>
#include <stop_token>
#include <string>
#include <string_view>
#include <system_error>

static auto build_dbc(int n) -> std::string {
    std::ostringstream dbc;
    dbc << "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n";
    for (int i = 0; i < n; ++i) {
        dbc << "BO_ " << (256 + i) << " Msg" << i << ": 8 ECU\n";
        dbc << " SG_ Sig" << i << " : 0|16@1+ (0.25,0) [0|8000] \"u\" ECU\n\n";
    }
    return dbc.str();
}

static auto run(std::span<char* const> args) -> int {
    try {
        int n = 3;
        if (args.size() > 1) {
            // Refuse a count this cannot read rather than falling back to the
            // default: a silent fallback runs the small workload under the tight
            // cap, which is the one case the driver reads as containment.
            const std::string_view arg{args[1]};
            auto const* const last = std::to_address(arg.end());
            auto const [ptr, ec] = std::from_chars(std::to_address(arg.begin()), last, n);
            if (ec != std::errc{} || ptr != last || n <= 0) {
                std::println(
                    stderr,
                    "rts_heap_cap_workload: message count must be a positive number, got '{}'",
                    arg);
                return 2;
            }
        }
        aletheia::AletheiaClient client(aletheia::make_ffi_backend_from_env());
        auto const parsed = client.parse_dbc_text(std::stop_token{}, build_dbc(n));
        if (!parsed)
            return 3;
    } catch (const std::exception& e) {
        std::println(stderr, "rts_heap_cap_workload: {}", e.what());
        return 2;
    }
    std::puts("ALETHEIA_RTS_OK");
    return 0;
}

// The driver reads this binary's exit code, so nothing leaves main: an
// escaping exception would arrive as a signal instead, which the driver reads
// as a containment failure rather than as the refusal it is.
auto main(int argc, char** argv) -> int {
    try {
        return run(std::span{argv, static_cast<std::size_t>(argc)});
    } catch (...) {
        return 2;
    }
}
