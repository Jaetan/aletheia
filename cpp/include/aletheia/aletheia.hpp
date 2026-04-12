// SPDX-License-Identifier: BSD-2-Clause
//
// Aletheia C++23 Binding — Umbrella Header
//
// Formally verified CAN frame analysis via Linear Temporal Logic.
// Include this single header to access the full C++ API.
//
#pragma once

// Every sub-header below is the authoritative source for some vocabulary
// type (Client, Check, DbcDefinition, LtlFormula, …). The `IWYU pragma:
// export` annotations tell misc-include-cleaner that <aletheia/aletheia.hpp>
// transitively re-exports every public symbol defined beneath it, so tests
// and downstream callers can keep using the single umbrella include.
#include <aletheia/backend.hpp>    // IWYU pragma: export
#include <aletheia/check.hpp>      // IWYU pragma: export
#include <aletheia/client.hpp>     // IWYU pragma: export
#include <aletheia/dbc.hpp>        // IWYU pragma: export
#include <aletheia/enrich.hpp>     // IWYU pragma: export
#include <aletheia/error.hpp>      // IWYU pragma: export
#include <aletheia/excel.hpp>      // IWYU pragma: export
#include <aletheia/log.hpp>        // IWYU pragma: export
#include <aletheia/ltl.hpp>        // IWYU pragma: export
#include <aletheia/response.hpp>   // IWYU pragma: export
#include <aletheia/types.hpp>      // IWYU pragma: export
#include <aletheia/validation.hpp> // IWYU pragma: export
#include <aletheia/yaml.hpp>       // IWYU pragma: export
