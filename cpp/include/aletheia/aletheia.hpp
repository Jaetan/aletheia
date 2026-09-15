// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Aletheia C++23 Binding — Umbrella Header
//
// Formally verified CAN frame analysis via Linear Temporal Logic.
// Include this single header to reach every public header but cli.hpp (the
// CLI entry point, built as its own library), the optional Excel and YAML
// loaders included.
//
// Two entry points:
//
//   <aletheia/aletheia.hpp>  — the umbrella: the core API plus the loaders
//                              (excel.hpp, yaml.hpp) and the enrichment
//                              helper (enrich.hpp).
//
//   <aletheia/client.hpp>    — the facade: the core API only (Client, Check,
//                              DbcDefinition, LtlFormula, logging, errors,
//                              responses). Include excel.hpp, yaml.hpp or
//                              enrich.hpp beside it where they are used.
//
// Neither entry point includes a third-party header: OpenXLSX, yaml-cpp and
// nlohmann/json stay behind the library's own sources, so the difference is
// the set of declarations, not compile time (a probe under probes/ measures
// both closures).
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
#include <aletheia/limits.hpp>     // IWYU pragma: export
#include <aletheia/log.hpp>        // IWYU pragma: export
#include <aletheia/ltl.hpp>        // IWYU pragma: export
#include <aletheia/response.hpp>   // IWYU pragma: export
#include <aletheia/types.hpp>      // IWYU pragma: export
#include <aletheia/validation.hpp> // IWYU pragma: export
#include <aletheia/yaml.hpp>       // IWYU pragma: export
