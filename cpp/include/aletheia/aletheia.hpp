// SPDX-License-Identifier: BSD-2-Clause
//
// Aletheia C++23 Binding — Umbrella Header
//
// Formally verified CAN frame analysis via Linear Temporal Logic.
// Include this single header to access the full C++ API, including the
// optional Excel and YAML loaders.
//
// Two entry points, by audience:
//
//   <aletheia/aletheia.hpp>  — umbrella-for-quickstart. Pulls in the core
//                              API plus the optional loaders (excel.hpp,
//                              yaml.hpp) and the enrichment helper
//                              (enrich.hpp). Pick this for tutorials,
//                              examples, and one-file scripts where
//                              compile time is not a concern.
//
//   <aletheia/client.hpp>    — facade-for-production. Pulls in only the
//                              core API (Client, Check, DbcDefinition,
//                              LtlFormula, logging, errors, responses).
//                              Pick this when you want to avoid the
//                              OpenXLSX / yaml-cpp transitive cost in
//                              production code, and include excel.hpp /
//                              yaml.hpp / enrich.hpp separately only
//                              where they are actually needed.
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
