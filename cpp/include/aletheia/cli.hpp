// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <span>
#include <string>

namespace aletheia {

// The CLI's exit codes.  The binary, the dispatch below it and the tests all
// read them here, so the three cannot drift apart.
inline constexpr int cli_exit_ok = 0;
inline constexpr int cli_exit_validation_failed = 1;
inline constexpr int cli_exit_error = 2;

// Run the Aletheia C++ CLI over args, the program arguments *excluding* the
// program name, i.e. [subcommand, flags…, positionals…]. Returns one of the
// exit codes above.
//
// noexcept: every failure (including an unexpected exception) is converted to
// `cli_exit_error`, so callers, the aletheia-cli binary and the CLI tests,
// never observe a throw. Subcommands mirror the Python `python -m aletheia` surface:
// validate, extract, signals, format-dbc, mux-query. There is no `check`
// subcommand: the binding has no CAN-log reader. Behavior lives in
// cpp/src/cli/cli.cpp.
[[nodiscard]] auto run_cli(std::span<const std::string> args) noexcept -> int;

} // namespace aletheia
