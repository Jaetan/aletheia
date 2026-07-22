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
// hits this); 2 = backend/exception.  The GHC heap abort terminates the process
// out of band (exit 1), which is what the test asserts for the tight-cap case.

#include <aletheia/backend.hpp>
#include <aletheia/client.hpp>

#include <charconv>
#include <cstdio>
#include <exception>
#include <sstream>
#include <stop_token>
#include <string>
#include <string_view>

namespace {

auto build_dbc(int n) -> std::string {
    std::ostringstream dbc;
    dbc << "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n";
    for (int i = 0; i < n; ++i) {
        dbc << "BO_ " << (256 + i) << " Msg" << i << ": 8 ECU\n";
        dbc << " SG_ Sig" << i << " : 0|16@1+ (0.25,0) [0|8000] \"u\" ECU\n\n";
    }
    return dbc.str();
}

} // namespace

auto main(int argc, char** argv) -> int {
    int n = 3;
    if (argc > 1) {
        const std::string_view arg{argv[1]};
        std::from_chars(arg.data(), arg.data() + arg.size(), n);
    }
    try {
        aletheia::AletheiaClient client(aletheia::make_ffi_backend_from_env());
        auto parsed = client.parse_dbc_text(std::stop_token{}, build_dbc(n));
        if (!parsed)
            return 3;
    } catch (const std::exception& e) {
        std::fprintf(stderr, "rts_heap_cap_workload: %s\n", e.what());
        return 2;
    }
    std::puts("ALETHEIA_RTS_OK");
    return 0;
}
