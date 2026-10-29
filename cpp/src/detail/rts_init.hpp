// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The GHC runtime's once-per-process state. `runtime_start.cpp` writes it when
// it starts the runtime, for `aletheia::start_runtime` and every FfiBackend
// alike, and the rational renderer, the decimal parser and
// `aletheia::allocated_bytes` read it: they call the library the runtime
// started on, through the entries the start recorded, and never start the
// runtime themselves, which would fix its core count before the program chose
// one. While it is down they refuse.
//
// The `cores` field backs the `rts.cores_mismatch` warning when a later start
// asks another count (the first start wins).
//
// Lifecycle invariant: the GHC RTS is process-global, so `hs_init` is called at
// most once per process; there is no teardown (`hs_exit` is never called, as the
// GHC RTS does not support reinitialization), so the state is never reset.

#pragma once

#include <aletheia/error.hpp>

#include <cstdint>
#include <mutex>
#include <string_view>

#include "ffi_abi.hpp"

namespace aletheia::detail {

// The entries of the library the runtime started on that a caller outside a
// session calls. The library stays open for the process, so the addresses do.
struct RuntimeEntries {
    std::uint64_t (*allocated_bytes)() = nullptr;
    char* (*format_rational)(FfiRational const*) = nullptr;
    void (*free_str)(char*) = nullptr;
    std::int8_t (*parse_decimal)(FfiText const*, FfiDecimal*) = nullptr;
};

struct RTSInitState {
    std::mutex mu;
    bool initialized = false;
    // The core count the runtime started with.  A later start asking another
    // cannot change it and surfaces the difference as `rts.cores_mismatch`.
    int cores = 0;
    RuntimeEntries entries;
};

// Function-static accessor: guarantees a single instance shared across
// every TU that links against aletheia-cpp.  Lock `RTSInitState::mu`
// before reading or writing any field.
[[nodiscard]] auto rts_init_state() -> RTSInitState&;

// Whether the GHC runtime has started. Acquires `RTSInitState::mu` internally.
[[nodiscard]] auto rts_initialized() -> bool;

// The recorded entries, or an error of kind Ffi while the runtime is down,
// `reading` naming what the caller was doing. Acquires `RTSInitState::mu`.
[[nodiscard]] auto started_entries(std::string_view reading) -> Result<RuntimeEntries>;

} // namespace aletheia::detail
