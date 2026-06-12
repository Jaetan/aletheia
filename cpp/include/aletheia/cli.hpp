// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <span>
#include <string>

namespace aletheia {

// Run the Aletheia C++ CLI over args — the program arguments *excluding* the
// program name, i.e. [subcommand, flags…, positionals…]. Returns the process
// exit code: 0 ok, 1 violations / validation failed, 2 error.
//
// noexcept: every failure (including an unexpected exception) is converted to
// exit code 2, so callers — the aletheia-cli binary and the CLI tests — never
// observe a throw. Subcommands mirror the Python `python -m aletheia` surface:
// validate, extract, signals, format-dbc, mux-query. `check` is deferred (it
// needs a verified CAN-log reader). Behavior lives in cpp/src/cli/cli.cpp.
[[nodiscard]] auto run_cli(std::span<const std::string> args) noexcept -> int;

} // namespace aletheia
