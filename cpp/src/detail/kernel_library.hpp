// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Opening libaletheia-ffi.so and starting the GHC runtime on it, the steps
// `aletheia::start_runtime` and every FfiBackend share (runtime_start.cpp).

#pragma once

#include <aletheia/error.hpp>

#include <cstdint>
#include <expected>
#include <filesystem>
#include <memory>
#include <optional>
#include <string_view>
#include <utility>

#include "ffi_abi.hpp"
#include "rts_init.hpp"

namespace aletheia::detail {

struct LibraryCloser {
    void operator()(void* handle) const noexcept;
};

// A library opened with dlopen, closed again unless it is released: a refusal
// after the open leaves no mapping behind.
using KernelLibrary = std::unique_ptr<void, LibraryCloser>;

// Opens the library at `lib_path`, refusing an empty path (Validation: dlopen of
// one opens the calling program), one that does not open, and one laid out for
// another ABI version, read before any other entry (Ffi).
[[nodiscard]] auto open_kernel(const std::filesystem::path& lib_path) -> Result<KernelLibrary>;

// Reads the entries of an opened library and keeps the refusal naming the first
// one missing, so a caller reads every entry it needs and is answered once.
class SymbolResolver {
public:
    explicit SymbolResolver(void* handle) : handle_(handle) {}

    // The entry `name`, or null when the library lacks it.
    [[nodiscard]] auto entry(const char* name) -> void*;
    template<typename Fn>
    [[nodiscard]] auto get(const char* name) -> Fn {
        return symbol_as<Fn>(entry(name));
    }
    // `value` when every entry read through this resolver was found, otherwise
    // the refusal naming the first one missing (kind Ffi), so no entry read as
    // null reaches a caller.
    template<typename T>
    [[nodiscard]] auto resolved(T value) const -> Result<T> {
        if (missing_)
            return std::unexpected(missing_.value());
        return value;
    }

private:
    void* handle_ = nullptr;
    std::optional<AletheiaError> missing_;
};

// What a start reads of an opened library: its start entry, its count of the
// CPUs the process may use, and the entries recorded if the runtime starts on it.
struct RuntimeSymbols {
    void (*hs_init)(int*, char***) = nullptr;
    std::uint32_t (*processors)() = nullptr;
    RuntimeEntries entries;
};

// Reads the runtime symbols through `resolver`, the start entry first; one
// missing is the resolver's refusal.
[[nodiscard]] auto runtime_symbols(SymbolResolver& resolver) -> RuntimeSymbols;

// What a start did: whether it started the runtime, whose library the caller
// then keeps open for good, and the `{active, requested}` counts when the
// runtime ran on another count than the one asked.
struct StartOutcome {
    bool started = false;
    std::optional<std::pair<int, int>> mismatch;
};

// Starts the runtime on the library `symbols` came from with `cores`
// capabilities, unless it runs; no count asks for the count running, the
// default when nothing runs. The count is held to 1 through the CPUs the
// process may use, as the runtime counts them, whether or not it runs
// (Validation).
[[nodiscard]] auto start_runtime_on(const RuntimeSymbols& symbols, std::optional<int> cores)
    -> Result<StartOutcome>;

// The library ALETHEIA_LIB names, or a Validation refusal naming
// `counted_twin`, the call that takes the path, when it is unset or empty.
[[nodiscard]] auto env_library_path(std::string_view counted_twin) -> Result<std::filesystem::path>;

} // namespace aletheia::detail
